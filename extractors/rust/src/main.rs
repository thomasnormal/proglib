#![feature(rustc_private)]

//! Extract the Runtime(Optimized) MIR that the pinned Miri toolchain executes.
//!
//! The compiler is the parser for this lane.  This program only consumes the
//! `rustc_public` tree and never parses rustc's textual MIR dumps.

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_public;
extern crate serde;

mod json;

use json::Value;
use rustc_public::mir::alloc::{AllocId, GlobalAlloc};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BasicBlock, Body, ConstOperand, MirVisitor, Operand, TerminatorKind};
use rustc_public::mir::visit::Location;
use rustc_public::ty::{ConstantKind, GenericArgKind, GenericArgs, MirConst, Prov, RigidTy, Span,
    Ty, TyConst, TyConstKind, TyKind};
use rustc_public::{entry_fn, CrateDef, CrateItem};
use serde::Serialize;
use std::collections::{HashMap, HashSet, VecDeque};
use std::env;
use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};

const TOOLCHAIN: &str = "nightly-2026-11-16-x86_64-unknown-linux-gnu";
const RUSTC_VERSION: &str = "1.102.0-nightly (5f4effd57 2026-11-13)";

/// These are Miri's compiler flags for the pinned nightly.  The extractor and
/// oracle therefore consume the same Runtime(Optimized) MIR bodies.
const MIRI_FLAGS: &[&str] = &[
    "-Zalways-encode-mir",
    "-Zextra-const-ub-checks",
    "-Zmir-preserve-ub",
    "-Zmir-opt-level=0",
    "-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums",
    "-Zmir-enable-passes=-ReferencePropagation,-GVN",
    "-Zdeduplicate-diagnostics=no",
];

fn string(value: impl Into<String>) -> Value {
    Value::string(value)
}

fn number(value: impl ToString) -> Value {
    Value::number(value)
}

fn bool_value(value: bool) -> Value {
    Value::Bool(value)
}

fn null() -> Value {
    Value::Null
}

fn object(fields: impl IntoIterator<Item = (impl Into<String>, Value)>) -> Value {
    Value::object(fields)
}

fn array(values: impl IntoIterator<Item = Value>) -> Value {
    Value::array(values)
}

fn query_layout(ty: Ty) -> Result<Result<rustc_public::abi::Layout, rustc_public::Error>, ()> {
    // Some rustc_public layout queries still assert on escaping binders in
    // trait-object types.  A refusal must remain data in the envelope, not an
    // uncontrolled driver panic; temporarily silence the panic hook around
    // this one compiler query and restore it immediately afterwards.
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(|| ty.layout())).map_err(|_| ());
    std::panic::set_hook(hook);
    result
}

/// `rustc_public::Ty::layout` still asserts for some types whose generic
/// arguments contain an escaping trait-object binder.  Detect those shapes
/// structurally before entering the compiler query.  This is a refusal of a
/// layout value, not a fallback to a textual type representation.
fn has_dynamic_type(ty: Ty, seen: &mut HashSet<Ty>) -> bool {
    if !seen.insert(ty) {
        return false;
    }
    let contains_args = |args: &GenericArgs, seen: &mut HashSet<Ty>| {
        args.0.iter().any(|argument| match argument {
            GenericArgKind::Type(inner) => has_dynamic_type(*inner, seen),
            GenericArgKind::Lifetime(_) | GenericArgKind::Const(_) => false,
        })
    };
    match ty.kind() {
        TyKind::RigidTy(rigid) => match rigid {
            RigidTy::Dynamic(_, _) => true,
            RigidTy::Adt(_, args)
            | RigidTy::FnDef(_, args)
            | RigidTy::Closure(_, args)
            | RigidTy::Coroutine(_, args)
            | RigidTy::CoroutineClosure(_, args) => contains_args(&args, seen),
            RigidTy::CoroutineWitness(_, args) => contains_args(&args, seen),
            RigidTy::Array(inner, _) | RigidTy::Pat(inner, _) | RigidTy::Slice(inner)
            | RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _) => {
                has_dynamic_type(inner, seen)
            }
            RigidTy::FnPtr(signature) => signature
                .value
                .inputs_and_output
                .iter()
                .any(|inner| has_dynamic_type(*inner, seen)),
            RigidTy::Tuple(types) => types.iter().any(|inner| has_dynamic_type(*inner, seen)),
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Float(_)
            | RigidTy::Foreign(_)
            | RigidTy::Str
            | RigidTy::Never => false,
        },
        TyKind::Alias(_, alias) => contains_args(&alias.args, seen),
        TyKind::Param(_) | TyKind::Bound(_, _) => false,
    }
}

fn raw<T: Serialize + ?Sized>(value: &T) -> Value {
    json::to_value(value)
        .unwrap_or_else(|error| object([("serialization_error", string(error.0))]))
}

fn raw_key<T: Serialize + ?Sized>(value: &T) -> String {
    let mut encoded = String::new();
    raw(value).write_to(&mut encoded);
    encoded
}

fn portable_path(path: String) -> String {
    if let Some(rest) = path.split_once("/rustlib/src/rust/").map(|(_, rest)| rest) {
        return format!("<rust-std>/{rest}");
    }
    if let Some((_, rest)) = path.split_once("/wt/ls-rust/") {
        return rest.to_owned();
    }
    path
}

fn span_value(span: Span) -> Value {
    let lines = span.get_lines();
    let file = span.get_filename();
    let portable_file = portable_path(file.clone());
    let display = span.diagnostic().replace(&file, &portable_file);
    object([
        ("handle", string(raw_key(&span))),
        ("file", string(portable_file)),
        ("display", string(display)),
        (
            "start",
            object([
                ("line", number(lines.start_line)),
                ("column", number(lines.start_col)),
            ]),
        ),
        (
            "end",
            object([
                ("line", number(lines.end_line)),
                ("column", number(lines.end_col)),
            ]),
        ),
    ])
}

fn crate_value<D: CrateDef>(definition: &D) -> Value {
    let krate = definition.krate();
    object([
        ("name", string(krate.name)),
        ("id", string(raw_key(&krate.id))),
        ("definition", string(definition.name())),
    ])
}

#[derive(Default)]
struct Metadata {
    types: HashMap<Ty, String>,
    type_values: Vec<Value>,
    spans: HashMap<String, Value>,
    definitions: HashMap<String, Value>,
    allocations: HashMap<rustc_public::ty::Allocation, String>,
    allocation_values: Vec<Value>,
    globals: HashMap<String, Value>,
}

impl Metadata {
    fn add_span(&mut self, span: Span) {
        let key = raw_key(&span);
        self.spans.entry(key).or_insert_with(|| span_value(span));
    }

    fn add_definition<D: CrateDef>(&mut self, definition: &D, kind: &str) {
        let id = raw_key(&definition.def_id());
        let key = format!("{kind}:{id}");
        self.definitions.entry(key).or_insert_with(|| {
            object([
                ("id", string(id)),
                ("kind", string(kind)),
                ("name", string(definition.name())),
                ("trimmed_name", string(definition.trimmed_name())),
                ("crate", crate_value(definition)),
                ("span", span_value(definition.span())),
            ])
        });
    }

    fn add_alloc(&mut self, allocation: &rustc_public::ty::Allocation) -> String {
        if let Some(id) = self.allocations.get(allocation) {
            return id.clone();
        }
        let id = format!("a{}", self.allocation_values.len());
        self.allocations.insert(allocation.clone(), id.clone());
        let provenance = allocation
            .provenance
            .ptrs
            .iter()
            .map(|(offset, prov)| {
                self.add_global(prov.0);
                object([
                    ("offset", number(*offset)),
                    ("allocation", string(raw_key(&prov.0))),
                ])
            })
            .collect::<Vec<_>>();
        self.allocation_values.push(object([
            ("id", string(id.clone())),
            ("bytes", array(allocation.bytes.iter().map(|byte| match byte {
                Some(value) => number(*value),
                None => null(),
            }))),
            (
                "provenance",
                array(provenance),
            ),
            ("align", number(allocation.align)),
            ("mutability", string(format!("{:?}", allocation.mutability))),
        ]));
        id
    }

    fn add_global(&mut self, allocation_id: AllocId) {
        let key = raw_key(&allocation_id);
        if self.globals.contains_key(&key) {
            return;
        }
        let global = GlobalAlloc::from(allocation_id);
        let value = match &global {
            GlobalAlloc::Function(instance) => object([
                ("id", string(key.clone())),
                ("kind", string("function")),
                ("instance", string(instance.mangled_name())),
                ("name", string(instance.name())),
            ]),
            GlobalAlloc::VTable(ty, trait_ref) => object([
                ("id", string(key.clone())),
                ("kind", string("vtable")),
                ("type", string(raw_key(ty))),
                ("trait", string(format!("{trait_ref:?}"))),
            ]),
            GlobalAlloc::Static(definition) => object([
                ("id", string(key.clone())),
                ("kind", string("static")),
                ("name", string(definition.name())),
                ("definition", raw(definition)),
            ]),
            GlobalAlloc::Memory(allocation) => object([
                ("id", string(key.clone())),
                ("kind", string("memory")),
                ("allocation", string(self.add_alloc(allocation))),
            ]),
            GlobalAlloc::TypeId { ty } => object([
                ("id", string(key.clone())),
                ("kind", string("type_id")),
                ("type", string(raw_key(ty))),
            ]),
        };
        self.globals.insert(key, value);
    }

    fn add_const(&mut self, constant: &MirConst) {
        self.add_ty(constant.ty());
        match constant.kind() {
            ConstantKind::Allocated(allocation) => {
                self.add_alloc(allocation);
            }
            ConstantKind::Ty(ty) => self.add_ty_const(ty),
            ConstantKind::Unevaluated(value) => self.add_args(&value.args),
            ConstantKind::Param(_) | ConstantKind::ZeroSized => {}
        }
    }

    fn add_ty_const(&mut self, constant: &TyConst) {
        match constant.kind() {
            TyConstKind::Param(_) | TyConstKind::Bound(_, _) => {}
            TyConstKind::Unevaluated(_, args) => self.add_args(args),
            TyConstKind::Value(ty, allocation) => {
                self.add_ty(*ty);
                self.add_alloc(allocation);
            }
            TyConstKind::ZSTValue(ty) => self.add_ty(*ty),
        }
    }

    fn add_args(&mut self, args: &GenericArgs) {
        for argument in &args.0 {
            match argument {
                GenericArgKind::Lifetime(_) => {}
                GenericArgKind::Type(ty) => self.add_ty(*ty),
                GenericArgKind::Const(value) => self.add_ty_const(value),
            }
        }
    }

    fn add_ty(&mut self, ty: Ty) {
        if self.types.contains_key(&ty) {
            return;
        }
        let id = format!("t{}", self.type_values.len());
        self.types.insert(ty, id.clone());
        // Reserve the slot before descending: recursive types are legal.
        self.type_values.push(null());
        let kind = ty.kind();
        self.add_ty_kind(&kind);
        let pointee = match &kind {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => Some(string(raw_key(inner))),
            _ => None,
        };
        let type_args: Vec<Value> = match &kind {
            TyKind::RigidTy(RigidTy::Adt(_, args)) => args.0.iter().filter_map(|argument| {
                match argument {
                    GenericArgKind::Type(inner) => Some(number(raw_key(inner))),
                    _ => None,
                }
            }).collect(),
            _ => Vec::new(),
        };
        let layout = if has_dynamic_type(ty, &mut HashSet::new()) {
            object([( "error", string("layout refused: type contains a dynamic trait object") )])
        } else {
            match query_layout(ty) {
                Err(_) => object([( "error", string("rustc_public layout query panicked") )]),
                Ok(Err(error)) => object([( "error", string(error.to_string()) )]),
                Ok(Ok(layout)) => object([
                    ("shape", raw(&layout.shape())),
                    ("handle", string(raw_key(&layout))),
                ]),
            }
        };
        let type_index = id[1..].parse::<usize>().unwrap();
        self.type_values[type_index] = object([
            ("id", string(id)),
            ("handle", string(raw_key(&ty))),
            ("kind", string(format!("{kind:?}"))),
            ("pointee", pointee.unwrap_or_else(null)),
            ("type_args", array(type_args)),
            ("layout", layout),
        ]);
    }

    fn add_ty_kind(&mut self, kind: &TyKind) {
        match kind {
            TyKind::RigidTy(rigid) => match rigid {
                RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_)
                | RigidTy::Foreign(_)
                | RigidTy::Str
                | RigidTy::Never => {}
                RigidTy::Adt(definition, args) => {
                    self.add_definition(definition, "adt");
                    self.add_args(args);
                }
                RigidTy::Array(ty, constant) => {
                    self.add_ty(*ty);
                    self.add_ty_const(constant);
                }
                RigidTy::Pat(ty, _) | RigidTy::Slice(ty) => self.add_ty(*ty),
                RigidTy::RawPtr(ty, _) => self.add_ty(*ty),
                RigidTy::Ref(_, ty, _) => self.add_ty(*ty),
                RigidTy::FnDef(definition, args) => {
                    self.add_definition(definition, "function");
                    self.add_args(args);
                }
                RigidTy::FnPtr(signature) => {
                    for ty in &signature.value.inputs_and_output {
                        self.add_ty(*ty);
                    }
                }
                RigidTy::Closure(_, args)
                | RigidTy::Coroutine(_, args)
                | RigidTy::CoroutineClosure(_, args)
                | RigidTy::CoroutineWitness(_, args) => self.add_args(args),
                RigidTy::Dynamic(predicates, _) => {
                    for predicate in predicates {
                        if let rustc_public::ty::ExistentialPredicate::Trait(trait_ref) = &predicate.value {
                            self.add_args(&trait_ref.generic_args);
                        }
                    }
                }
                RigidTy::Tuple(types) => {
                    for ty in types {
                        self.add_ty(*ty);
                    }
                }
            },
            TyKind::Alias(_, alias) => self.add_args(&alias.args),
            TyKind::Param(_) | TyKind::Bound(_, _) => {}
        }
    }

    fn scan_body(&mut self, body: &Body) {
        let mut scanner = Scanner { metadata: self };
        scanner.visit_body(body);
    }
}

struct Scanner<'a> {
    metadata: &'a mut Metadata,
}

impl MirVisitor for Scanner<'_> {
    fn visit_span(&mut self, span: &Span) {
        self.metadata.add_span(*span);
    }

    fn visit_ty(&mut self, ty: &Ty, _location: Location) {
        self.metadata.add_ty(*ty);
    }

    fn visit_mir_const(&mut self, constant: &MirConst, location: Location) {
        self.metadata.add_const(constant);
        self.super_mir_const(constant, location);
    }
}

fn direct_callee(operand: &Operand) -> Result<Option<Instance>, String> {
    let Operand::Constant(ConstOperand { const_, .. }) = operand else {
        return Ok(None);
    };
    if let Some((definition, args)) = const_.ty().kind().fn_def() {
        return Instance::resolve(definition, args)
            .map(Some)
            .map_err(|error| error.to_string());
    }
    if let rustc_public::ty::ConstantKind::Allocated(allocation) = const_.kind() {
        for (_, Prov(allocation_id)) in &allocation.provenance.ptrs {
            if let GlobalAlloc::Function(instance) = GlobalAlloc::from(*allocation_id) {
                return Ok(Some(instance));
            }
        }
    }
    Ok(None)
}

#[derive(Default)]
struct Extractor {
    metadata: Metadata,
    instance_ids: HashMap<Instance, String>,
    instances: Vec<(String, Instance)>,
    bodies: Vec<(String, Value)>,
    calls: Vec<Value>,
}

impl Extractor {
    fn instance_id(&mut self, instance: Instance) -> String {
        if let Some(id) = self.instance_ids.get(&instance) {
            return id.clone();
        }
        let base = instance.mangled_name();
        let mut id = base.clone();
        let mut suffix = 0usize;
        while self.instances.iter().any(|(known, _)| known == &id) {
            suffix += 1;
            id = format!("{base}#{suffix}");
        }
        self.instance_ids.insert(instance, id.clone());
        self.instances.push((id.clone(), instance));
        id
    }

    fn walk(&mut self, entry: Instance) -> String {
        let entry_id = self.instance_id(entry);
        let mut queue = VecDeque::from([entry]);
        let mut visited = HashSet::new();
        while let Some(instance) = queue.pop_front() {
            if !visited.insert(instance) {
                continue;
            }
            let id = self.instance_id(instance);
            self.metadata.add_args(&instance.args());
            let Some(body) = instance.body() else {
                continue;
            };
            self.metadata.scan_body(&body);
            let body_json = raw(&body);
            self.bodies.push((id.clone(), body_json));
            let mut discovered = Vec::new();
            for (block, BasicBlock { terminator, .. }) in body.blocks.iter().enumerate() {
                if let TerminatorKind::Call { func, .. } = &terminator.kind {
                    match direct_callee(func) {
                        Ok(Some(callee)) => {
                            let callee_id = self.instance_id(callee);
                            self.metadata.add_definition_from_instance(callee);
                            self.calls.push(object([
                                ("caller", string(id.clone())),
                                ("block", number(block)),
                                ("span", span_value(terminator.source_info.span)),
                                ("callee", string(callee_id)),
                                ("resolved", bool_value(true)),
                            ]));
                            if callee.body().is_some() {
                                discovered.push(callee);
                            }
                        }
                        Ok(None) => self.calls.push(object([
                            ("caller", string(id.clone())),
                            ("block", number(block)),
                            ("span", span_value(terminator.source_info.span)),
                            ("callee", null()),
                            ("resolved", bool_value(false)),
                            ("reason", string("indirect or foreign call")),
                        ])),
                        Err(error) => self.calls.push(object([
                            ("caller", string(id.clone())),
                            ("block", number(block)),
                            ("span", span_value(terminator.source_info.span)),
                            ("callee", null()),
                            ("resolved", bool_value(false)),
                            ("reason", string(error)),
                        ])),
                    }
                }
            }
            queue.extend(discovered);
        }
        entry_id
    }

    fn envelope(&self, entry: &str) -> Value {
        let instances = self.instances.iter().map(|(id, instance)| {
            object([
                ("id", string(id.clone())),
                ("kind", string(format!("{:?}", instance.kind))),
                ("name", string(instance.name())),
                ("mangled_name", string(instance.mangled_name())),
                ("def", raw(&instance.def)),
                ("args", raw(&instance.args())),
                ("has_body", bool_value(instance.body().is_some())),
                ("foreign", bool_value(instance.is_foreign_item())),
                ("intrinsic", instance
                    .intrinsic_name()
                    .map(string)
                    .unwrap_or_else(null)),
            ])
        });
        let bodies = self.bodies.iter().map(|(id, body)| {
            object([("instance", string(id.clone())), ("body", body.clone())])
        });
        let definitions = sorted_values(&self.metadata.definitions);
        let globals = sorted_values(&self.metadata.globals);
        let spans = sorted_values(&self.metadata.spans);
        object([
            ("schema", string("lean-surfaces.rust.mir.v0")),
            (
                "toolchain",
                object([
                    ("channel", string(TOOLCHAIN)),
                    ("rustc", string(RUSTC_VERSION)),
                    ("miri", string("0.1.0 (5f4effd579 2026-11-13)")),
                ]),
            ),
            ("miri_flags", array(MIRI_FLAGS.iter().copied().map(string))),
            ("entry", string(entry.to_owned())),
            ("target", raw(&rustc_public::target::MachineInfo::target())),
            ("instances", array(instances)),
            ("bodies", array(bodies)),
            ("calls", array(self.calls.iter().cloned())),
            (
                "tables",
                object([
                    ("types", array(self.metadata.type_values.iter().cloned())),
                    ("spans", array(spans)),
                    ("definitions", array(definitions)),
                    (
                        "allocations",
                        array(self.metadata.allocation_values.iter().cloned()),
                    ),
                    ("globals", array(globals)),
                ]),
            ),
        ])
    }
}

fn sorted_values(values: &HashMap<String, Value>) -> Vec<Value> {
    let mut entries = values.iter().collect::<Vec<_>>();
    entries.sort_by(|(left, _), (right, _)| left.cmp(right));
    entries.into_iter().map(|(_, value)| value.clone()).collect()
}

impl Metadata {
    fn add_definition_from_instance(&mut self, instance: Instance) {
        let id = raw_key(&instance.def);
        self.definitions.entry(format!("instance:{id}")).or_insert_with(|| {
            object([
                ("id", string(id)),
                ("kind", string("instance")),
                ("name", string(instance.name())),
                ("mangled_name", string(instance.mangled_name())),
            ])
        });
    }
}

fn rustc_args() -> (Vec<String>, Option<String>) {
    let mut arguments = Vec::new();
    let mut output = env::var("RUST_MIR_OUTPUT").ok();
    let mut iter = env::args().peekable();
    if let Some(program) = iter.next() {
        arguments.push(program);
    }
    while let Some(argument) = iter.next() {
        if let Some(value) = argument.strip_prefix("--rust-mir-output=") {
            output = Some(value.to_owned());
        } else if argument == "--rust-mir-output" {
            output = iter.next();
        } else {
            arguments.push(argument);
        }
    }
    for flag in MIRI_FLAGS {
        if !arguments.iter().any(|argument| argument == flag) {
            arguments.push((*flag).to_owned());
        }
    }
    (arguments, output)
}

fn main() {
    let (arguments, output_path) = rustc_args();
    let result = rustc_public::run!(&arguments, || -> std::ops::ControlFlow<(), ()> {
        let item: CrateItem = entry_fn().unwrap_or_else(|| {
            panic!("rust-mir-extract: no entry function in local crate")
        });
        let entry = Instance::try_from(item).unwrap_or_else(|error| {
            panic!("rust-mir-extract: entry function is not monomorphic: {error}")
        });
        let mut extractor = Extractor::default();
        let entry_id = extractor.walk(entry);
        let mut encoded = String::new();
        extractor.envelope(&entry_id).write_to(&mut encoded);
        if let Some(path) = output_path.as_deref() {
            fs::write(path, encoded).unwrap_or_else(|error| {
                panic!("rust-mir-extract: cannot write {path}: {error}")
            });
        } else {
            println!("{encoded}");
        }
        std::ops::ControlFlow::Break(())
    });
    match result {
        Ok(()) | Err(rustc_public::CompilerError::Interrupted(())) => {}
        Err(error) => {
            eprintln!("rust-mir-extract: {error:?}");
            std::process::exit(1);
        }
    }
}
