import LeanModels.Core.Basic
import Lean.ToExpr
import LeanModels.Clang.QualType

/-!
# The C tier's deep-embedded AST (`LeanModels.C`)

The Lean image of the `c-0.1` envelope (`docs/c-envelope-schema.md`). One
constructor per node kind in the pinned vocabulary, plus an `unsupported`
leaf for everything outside it.

**This file is a TYPE, not a semantics.** Nothing here evaluates
anything; the interpreter, the memory model and the UB refusals are
milestone M2 and later (`docs/c-tier-charter.md` §3). A term of type
`TranslationUnit` is what `load_c_program` produces at elaboration time,
and what the `#guard`s of `Examples/c/sunfish/` are stated about.

Three shapes are worth reading before the constructors, because each is a
decision the census or the schema forced rather than a convenience:

* **`String` remains the frontend spelling during this migration.** Every
  declaration and expression node also carries the optional recursive
  `LeanModels.Clang.QualType` observed by the approved Clang plugin. The
  extractor joins that observation by the Clang node identity from the same
  invocation. The spelling is metadata and is never parsed by Lean.
* **`Span.macro` is an `Option`.** Six function-like macros produce
  corpus constructs, and a refusal that cannot name the macro is one a
  human cannot act on. It is `none` for source written directly, so
  macro-free files carry no extra weight.
* **Every literal keeps its SOURCE SPELLING as a `String`.** An
  `IntegerLiteral`'s value is `"2147483648"`, not a `Nat` — because the
  tier's whole product is refusing what C leaves undefined, and a
  literal that overflowed its type during ingestion would have been
  silently decided before the semantics ever saw it.
-/

namespace LeanModels.C

open LeanModels (Span)

/-- Full compiler identity required by the C envelope ingester. A family stamp
is insufficient because point releases and build revisions can change the AST
that the model is shown. -/
def pinnedFrontendVersion : String :=
  "clang version 21.1.8 (https://github.com/conda-forge/clangdev-feedstock " ++
    "334cf9a5e6c0331e9f261eaf01fc3568724fcce9)"

/- Clang's declaration handle is an identity, not a source spelling. Keep it
   distinct from names even though the frontend currently serializes the
   token as text. -/
structure DeclarationId where
  value : String
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- A source span, with the macro that produced the construct when one did.
`line`/`col` are the EXPANSION location — where a reader sees it. -/
structure CSpan where
  line : Nat
  /-- Parser-provided byte offset of the node's beginning, when available. -/
  offset : Option Nat := none
  /-- The column, **when the frontend gives one**.

  `none` is not "column 0" and must never be defaulted to it: clang omits
  `col` for locations it knows only to a line — an unnamed parameter in a
  prototype is the common case — and a fabricated column is silently wrong
  data that reads exactly like a measured one. Column 0 and
  column-unknown stay distinguishable because they are different
  constructors.

  **Nothing in this tier reads it today**, so the `Option` costs no call
  site; it is here so that the first reader has to decide the absence case
  in the open (`docs/backlog/c.md` 2026-08-24-c-19). -/
  col : Option Nat
  endLine : Nat
  /-- Parser-provided byte offset just after the node, when available. -/
  endOffset : Option Nat := none
  /-- The end column, on the same terms as `col`. -/
  endCol : Option Nat
  /-- The SPELLING location, present only when it differs from the
  expansion location — i.e. the node came out of a macro body. -/
  macroLine : Option Nat := none
  macroCol : Option Nat := none
deriving Repr, Inhabited, BEq, DecidableEq

/-- The structured type tree, emitted only under a `TypedefDecl`. -/
inductive TypeNode where
  | builtin (name : String)
  | pointer (inner : TypeNode)
  | array (inner : TypeNode) (extent : Option Nat)
  | paren (inner : TypeNode)
  | elaborated (inner : TypeNode)
  | qualified (isConst : Bool) (isVolatile : Bool) (inner : TypeNode)
  | record (id : Option DeclarationId) (ty : String)
  | enumeration (id : Option DeclarationId) (ty : String)
  | typedefRef (id : Option DeclarationId) (ty : String)
  | funcProto (ret : TypeNode) (params : List TypeNode) (variadic : Bool)
  | unsupported (cKind : String) (text : String)
deriving Repr, Inhabited, BEq

/-! ### Parser-native bridge to the shared clang type layer

`TypeNode` is already the recursive shape clang emits below a typedef.  This
bridge preserves that shape and carries declaration identity into the shared
`QualType`; it never interprets a flat `qualType` spelling.  Recognized C
builtin names become parser-kind leaves.  Unknown names remain explicit
`cBuiltin` leaves until the C profile supplies their facts.
-/

partial def TypeNode.toQualType : TypeNode → Except String LeanModels.Clang.QualType
  | .builtin name =>
      match LeanModels.Clang.CBuiltin.ofName name with
      | some kind => .ok (.cBuiltinKind kind)
      | none => .ok (.cBuiltin name)
  | .pointer inner => do
      let pointee ← inner.toQualType
      pure (.pointer pointee)
  | .array inner extent => do
      let element ← inner.toQualType
      pure (.array element extent)
  | .paren inner => inner.toQualType
  | .elaborated inner => inner.toQualType
  | .qualified isConst isVolatile inner => do
      let base ← inner.toQualType
      pure (.qualified isConst isVolatile base)
  | .funcProto ret params variadic => do
      let result ← ret.toQualType
      let arguments ← params.mapM TypeNode.toQualType
      pure (.function result arguments variadic)
  | .record (some id) _ => .ok (.record {value := id.value})
  | .record none spelling =>
      .error s!"structured record type has no declaration identity: {spelling}"
  | .enumeration (some id) _ => .ok (.enumeration {value := id.value})
  | .enumeration none spelling =>
      .error s!"structured enum type has no declaration identity: {spelling}"
  | .typedefRef (some id) _ => .ok (.typedefRef {value := id.value})
  | .typedefRef none spelling =>
      .error s!"structured typedef type has no declaration identity: {spelling}"
  | .unsupported kind text =>
      .error s!"unsupported structured C type '{kind}': {text}"

/-- A record layout observed from Clang's `ASTRecordLayout` probe.  These are
frontend facts carried by the envelope; the C semantics may use them only
after checking the profile and the record identity. -/
structure RecordLayoutField where
  name : String
  offsetBits : Nat
  bitfield : Bool
  /-- Clang's parser-native marker for a flexible (incomplete) array member. -/
  incompleteArray : Bool := false
  widthBits : Option Nat := none
deriving Repr, Inhabited, BEq, Lean.ToExpr

structure RecordLayout where
  offset : Nat
  tokenLength : Nat
  name : String
  tagKind : String
  sizeBytes : Nat
  alignmentBytes : Nat
  fields : List RecordLayoutField
deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- A parser-native size/alignment observation for a declared object type.
This supplements record layouts for declarator-shaped objects such as nested
function-pointer objects whose size is a frontend fact but has no record node. -/
structure TypeLayout where
  declaration : Option DeclarationId := none
  ty : String
  sizeBytes : Nat
  alignmentBytes : Nat
  /-- For a declared pointer object, Clang's exact byte size of its pointee.
  This avoids parsing the flat pointer spelling when pointer arithmetic or
  subscripting needs its stride. -/
  pointeeSizeBytes : Option Nat := none
  /-- For a declared array object, Clang's exact parser element type. -/
  elementType : Option String := none
  /-- For a declared array object, Clang's exact byte size of one element. -/
  elementSizeBytes : Option Nat := none
  /-- For a variable-length array whose parser bound is a declaration
  identity, the declaration supplying that bound. -/
  boundDeclaration : Option DeclarationId := none
deriving Repr, Inhabited, BEq, Lean.ToExpr

/-! A recursive `QualType` observation joined to a parser declaration ID. -/
structure StructuredType where
  declaration : DeclarationId
  type : LeanModels.Clang.QualType
deriving Repr, Inhabited, BEq, Lean.ToExpr

structure StructuredExprType where
  /-- Parser node identity from the same Clang invocation as the AST dump. -/
  exprId : Option DeclarationId := none
  offset : Nat
  /-- End of the parser expression range, when Clang reports it. -/
  endOffset : Option Nat := none
  /-- Clang's expression node kind, used with the source range to disambiguate
      nested nodes beginning at the same byte. -/
  kind : String := ""
  type : LeanModels.Clang.QualType
deriving Repr, Inhabited, BEq, Lean.ToExpr

/-! ## The three layers

C's grammar makes the layering, not us: a function DEFINITION is the only
declaration that contains statements, and C has no nested functions — so
`Expr`, `Decl` and `Stmt` form no cycle, and `FunctionDefn` sits on top as
a structure. That is the same shape the Python lane's `FunctionDefn` has,
arrived at from the language rather than borrowed. -/

/-- C expressions — the 19 expression kinds of the pinned vocabulary. -/
inductive Expr where
  /-- Literals keep their SOURCE SPELLING; see the module docstring. -/
  | intLit (value : String) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | charLit (value : String) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | strLit (value : String) (decodedBytes : Option (List Nat)) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | predefined (name value : String) (decodedBytes : Option (List Nat)) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | floatLit (value : String) (bitsHex : Option String) (bitWidth : Option Nat)
      (ty : String) (span : CSpan) (structuredType : Option LeanModels.Clang.QualType)
  /-- C23's `true`/`false` literals, retained from clang's semantic node. -/
  | boolLit (value : Bool) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | nullPtrLit (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- GNU `__builtin_choose_expr`: condition and both parser branches. -/
  | choose (cond thenBranch elseBranch : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- A name, with the kind of declaration it resolved to. -/
  | declRef (id : Option DeclarationId) (name : String) (declKind : String)
      (ty : String) (span : CSpan) (structuredType : Option LeanModels.Clang.QualType)
  | member (base : Expr) (field : String) (arrow : Bool) (ty : String) (span : CSpan)
      (recordId : Option DeclarationId) (structuredType : Option LeanModels.Clang.QualType)
  | index (base : Expr) (idx : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- A call. An INDIRECT call is one whose callee is not a `declRef` to a
  function — all 19 in the corpus go through the `movecb` parameter. -/
  | call (callee : Expr) (args : List Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | binop (op : String) (lhs rhs : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | compoundAssign (op : String) (lhs rhs : Expr)
      (computeLHSType computeResultType ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
      (structuredComputeLHSType structuredComputeResultType : Option LeanModels.Clang.QualType)
  | unop (op : String) (sub : Expr) (isPostfix : Bool) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | cond (c t e : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | paren (sub : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- Clang's full-expression cleanup wrapper. C has no cleanup actions for
      the admitted rows, so the node evaluates its child and preserves the
      parser node in the envelope. -/
  | exprWithCleanups (sub : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- Clang's temporary-materialization node. C's value model uses the
      materialized child directly and retains the parser node. -/
  | materializeTemporary (sub : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- An implicit conversion, carrying clang's `castKind`. The 8 kinds are
  the whole conversion lattice and they arrive PRE-SOLVED — the tier never
  re-derives a promotion, it reads one off. -/
  | implicitCast (cast : String) (sub : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | cast (cast : String) (sub : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | initList (inits : List Expr) (unionField : Option String) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- Clang's `InitListExpr` retains both `inner` and `array_filler` fields. -/
  | arrayInitList (inits filler : List Expr) (unionField : Option String)
      (ty : String) (span : CSpan) (structuredType : Option LeanModels.Clang.QualType)
  /-- C23 designated-update initialization: initialize the base object, then
      apply the parser's update list to the same object. -/
  | designatedUpdate (base update : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | implicitValueInit (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | compoundLit (init : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- `sizeof`/`alignof`, over a type or over an expression. -/
  | typeTrait (trait : String) (argType : Option String) (sub : Option Expr)
      (ty : String) (span : CSpan)
      (structuredArgType : Option LeanModels.Clang.QualType)
      (operandSizeBytes operandAlignmentBytes : Option Nat)
      (structuredType : Option LeanModels.Clang.QualType)
  | constExpr (value : String) (sub : Option Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- C23 §6.5.3.3 / §7.16: parser-resolved `va_arg` operand and result
  type. The cursor is abstract state, not an ABI representation. -/
  | vaArg (ap : Expr) (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | offsetOf (ty : String) (span : CSpan)
      (offsetBytes : Option Nat)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- C11 §6.5.1.1 generic selection. The parser marks the selected
      association. The controlling expression remains unevaluated. -/
  | genericSelection (control selected : Expr) (associations : List (Bool × Expr))
      (ty : String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- Outside the pinned vocabulary: clang's own class name and ≤200 chars
  of source. Never silently dropped, never guessed at. -/
  | unsupported (cKind : String) (text : String) (span : CSpan)
deriving Repr, Inhabited

def Expr.span : Expr → CSpan
  | .intLit _ _ span .. | .charLit _ _ span .. | .strLit _ _ _ span ..
  | .predefined _ _ _ _ span ..
  | .floatLit _ _ _ _ span .. | .boolLit _ _ span .. | .nullPtrLit _ span .. | .choose _ _ _ _ span ..
  | .declRef _ _ _ _ span .. | .member _ _ _ _ span _ .. | .index _ _ _ span ..
  | .call _ _ _ span .. | .binop _ _ _ _ span .. | .compoundAssign _ _ _ _ _ _ span ..
  | .unop _ _ _ _ span .. | .cond _ _ _ _ span .. | .paren _ _ span ..
  | .exprWithCleanups _ _ span ..
  | .materializeTemporary _ _ span ..
  | .implicitCast _ _ _ span .. | .cast _ _ _ span .. | .initList _ _ _ span ..
  | .arrayInitList _ _ _ _ span .. | .designatedUpdate _ _ _ span ..
  | .implicitValueInit _ span .. | .compoundLit _ _ span ..
  | .typeTrait _ _ _ _ span .. | .constExpr _ _ _ span .. | .vaArg _ _ span ..
  | .offsetOf _ span ..
  | .genericSelection _ _ _ _ span ..
  | .unsupported _ _ span => span

/-- C declarations that can appear at BLOCK scope as well as file scope —
everything but a function definition. -/
inductive Decl where
  /-- A block-scope function prototype declaration.  §6.7.6.3 permits a
  prototype in a block.  It has no object lifetime or runtime effect, while
  its parser-native identity and parameter nodes remain available to lookup.
  -/
  | functionProto (id : Option DeclarationId) (name : String) (ty : String)
      (params : List Decl) (variadic : Bool) (span : CSpan)
  | var (id : Option DeclarationId) (name : String) (ty : String)
      (storage : Option String) (init : Option Expr)
      (recordId : Option DeclarationId) (vaList : Bool) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- A parameter. `name` is **optional**, because C's is: §6.7.6.3 lets a
  prototype declare a parameter with no identifier (`int f(int);`), and
  clang reports one with no `name`.

  `none` is not `""` and is never a synthetic. A fabricated `_unnamed_3`
  would be a fabricated column one field over — it reads exactly like a
  real name, and something downstream would eventually look it up. The
  absence is decided in exactly ONE place, `C23.bindParams`
  (`docs/backlog/c.md` 2026-08-24-c-20). -/
  | param (id : Option DeclarationId) (name : Option String) (ty : String)
      (vaList : Bool) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- A member declarator. `bits` is the BIT-FIELD WIDTH (§6.7.2.1p4) and
  `none` means "not a bit-field" — the two are different declarations, not
  a present/absent spelling of one. It is carried because `unsigned int b :
  1` and `unsigned int b` are DIFFERENT PROGRAMS with different observable
  behaviour, and an AST that cannot tell them apart makes the model answer
  correctly about whichever one it happened to build. -/
  | field (name : Option String) (ty : String) (bits : Option Nat)
      (fieldId : Option DeclarationId) (recordId : Option DeclarationId) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | record (id : Option DeclarationId) (name : Option String) (fields : List Decl)
      (layout : Option RecordLayout) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | typedef (id : Option DeclarationId) (name : String) (ty : String)
      (underlying : Option TypeNode) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  | enum (name : Option String) (constants : List Decl) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- An enumeration constant. clang's `ConstantExpr` wrapper is flattened
  by the extractor (schema §3.1). `value` is the FOLDED integer as a decimal
  string, and it is **optional**: clang does not always give one, and the
  absence family's rule holds here as it did for `col` and a parameter's
  `name` — no fabricated `"0"`, which would read exactly like a folded
  value somebody would then use as one.

  Measured: nothing in this tier reads it. `C23.Ctx.enums` is only ever
  supplied from `Program.enums`, which nothing builds from an envelope, so
  this is schema-widening (`docs/backlog/c.md` 2026-08-24-c-21). -/
  | enumConst (id : Option DeclarationId) (name : String) (value : Option String) (span : CSpan)
      (structuredType : Option LeanModels.Clang.QualType)
  /-- §6.7.2 — an empty declaration (`;`) has no runtime effect. -/
  | empty (span : CSpan)
  | unsupported (cKind : String) (text : String) (span : CSpan)
deriving Repr, Inhabited


/-- C statements — the modelled statement kinds. `SwitchStmt` is deliberately
absent (measured 0 in the corpus); it arrives with rung R1 and until then
ingests as `unsupported`, which is what makes R1 a rung and not a hole. -/
inductive Stmt where
  | compound (body : List Stmt) (span : CSpan)
  | decl (decls : List Decl) (span : CSpan)
  | ifS (cond : Expr) (thenS : Stmt) (elseS : Option Stmt) (span : CSpan)
  | forS (init : Option Stmt) (cond : Option Expr) (inc : Option Expr)
      (body : Stmt) (span : CSpan)
  | whileS (cond : Expr) (body : Stmt) (span : CSpan)
  | doS (body : Stmt) (cond : Expr) (span : CSpan)
  | ret (value : Option Expr) (span : CSpan)
  | breakS (span : CSpan)
  | continueS (span : CSpan)
  /-- §6.8.3 — the empty statement; it has no effect. -/
  | nullStmt (span : CSpan)
  | switchS (cond : Expr) (body : Stmt) (span : CSpan)
  | caseS (value : Expr) (body : Stmt) (span : CSpan)
  | caseRange (lo hi : Expr) (body : Stmt) (span : CSpan)
  | defaultS (body : Stmt) (span : CSpan)
  | goto (label : String) (span : CSpan)
  | label (name : String) (body : Stmt) (span : CSpan)
  /-- An expression in statement position. -/
  | expr (e : Expr) (span : CSpan)
  | unsupported (cKind : String) (text : String) (span : CSpan)
deriving Repr, Inhabited

/-- A function DEFINITION (or prototype, when `body = none`). `storage` is
clang's `storageClass` — `"static"`, or `none` for external linkage. -/
structure FunctionDefn where
  id : Option DeclarationId := none
  name : String
  ty : String
  /-- Parser-native function QualType joined by the declaration identity. -/
  structuredType : Option LeanModels.Clang.QualType := none
  storage : Option String
  params : List Decl
  /-- Clang's parser-native `variadic` bit on the function declaration. -/
  variadic : Bool := false
  body : Option Stmt
  span : CSpan
deriving Repr, Inhabited

/-- A file-scope item. -/
inductive TopLevel where
  | fn (f : FunctionDefn)
  | decl (d : Decl)
deriving Repr, Inhabited

/-- One translation unit: the top-level items attributed to the censused
source, in document order. -/
structure TranslationUnit where
  items : List TopLevel
deriving Repr, Inhabited

/-- A declared-but-not-defined name the unit references, with its
prototype. The corpus has exactly 27 (the libc slice). -/
structure External where
  name : String
  ty : Option String
deriving Repr, Inhabited, BEq

/-- The `c-0.1` envelope. The full pinned frontend version is retained and
checked by ingestion; `profileId` is retained because the profile is an input
to the AST and a mismatch has to be refusable. -/
structure Envelope where
  schemaVersion : String
  language : String
  frontendVersion : String
  profileId : String
  profileFlags : List String
  sourceFile : String
  sourceSha256 : String
  unit : TranslationUnit
  externals : List External
  /-- Clang's target represents a default-address-space null pointer in
      eight zero bytes. -/
  zeroNullPointer : Bool := false
  typeLayouts : List TypeLayout := []
  structuredTypes : List StructuredType := []
  structuredExprTypes : List StructuredExprType := []
  /-- Parser-native record tag facts keyed by declaration identity. -/
  recordKinds : List (DeclarationId × Bool) := []
deriving Repr, Inhabited

/-- Parser-native structured type for a declaration occurrence. -/
def Envelope.structuredTypeFor (envl : Envelope) (id : DeclarationId) :
    Option LeanModels.Clang.QualType :=
  -- A declaration identity must select exactly one parser observation. A
  -- duplicate is malformed frontend evidence and refuses instead of silently
  -- choosing whichever row happened to be listed first.
  match envl.structuredTypes.filter (fun row => row.declaration == id) with
  | [row] => some row.type
  | _ => none

/-! ## Structural queries

These exist so the ingester can be checked against
`harness/c_construct_census.py` — two instruments, two paths, one answer.
They are counts over the TERM, not claims about C. -/

/-- The type the frontend assigned to this expression.

Version-neutral: it reads a field the `c-0.1` envelope already carries
(`docs/c-envelope-schema.md` §3), and every semantic layer needs it. An
`unsupported` leaf has no type, and `""` resolves to nothing, so a
consumer refuses rather than inventing one. -/
def Expr.ty : Expr → String
  | .intLit _ t _ .. | .charLit _ t _ .. | .floatLit _ _ _ t _ .. => t
  | .strLit _ _ t _ .. | .predefined _ _ _ t _ .. => t
  | .boolLit _ t _ .. | .nullPtrLit t _ .. => t
  | .choose _ _ _ t _ .. => t
  | .declRef _ _ _ t _ .. => t
  | .member _ _ _ t _ _ .. | .index _ _ t _ .. | .call _ _ t _ .. => t
  | .binop _ _ _ t _ .. | .compoundAssign _ _ _ _ _ t _ .. => t
  | .unop _ _ _ t _ .. | .cond _ _ _ t _ .. | .paren _ t _ ..
  | .exprWithCleanups _ t _ .. | .materializeTemporary _ t _ .. => t
  | .implicitCast _ _ t _ .. | .cast _ _ t _ .. => t
  | .initList _ _ t _ .. | .compoundLit _ t _ .. | .implicitValueInit t _ .. => t
  | .arrayInitList _ _ _ t _ .. | .designatedUpdate _ _ t _ .. => t
  | .typeTrait _ _ _ t _ .. | .constExpr _ _ t _ .. | .vaArg _ t _ ..
  | .offsetOf t _ _ _ => t
  | .genericSelection _ _ _ t _ _ => t
  | .unsupported .. => ""

/-- The parser-native QualType carried directly by an expression node. -/
def Expr.structuredType? : Expr → Option LeanModels.Clang.QualType
  | .intLit _ _ _ q | .charLit _ _ _ q | .strLit _ _ _ _ q
  | .predefined _ _ _ _ _ q
  | .floatLit _ _ _ _ _ q | .boolLit _ _ _ q | .nullPtrLit _ _ q | .choose _ _ _ _ _ q
  | .declRef _ _ _ _ _ q | .member _ _ _ _ _ _ q | .index _ _ _ _ q
  | .call _ _ _ _ q | .binop _ _ _ _ _ q | .compoundAssign _ _ _ _ _ _ _ q _ _
  | .unop _ _ _ _ _ q | .cond _ _ _ _ _ q | .paren _ _ _ q
  | .implicitCast _ _ _ _ q | .cast _ _ _ _ q | .initList _ _ _ _ q
  | .arrayInitList _ _ _ _ _ q | .designatedUpdate _ _ _ _ q
  | .implicitValueInit _ _ q | .compoundLit _ _ _ q
  | .exprWithCleanups _ _ _ q | .materializeTemporary _ _ _ q
  | .typeTrait _ _ _ _ _ _ _ _ q | .constExpr _ _ _ _ q | .vaArg _ _ _ q => q
  | .offsetOf _ _ _ q => q
  | .genericSelection _ _ _ _ _ q => q
  | .unsupported .. => none

/-- clang's own class name for this node, for diagnostics. A refusal a
human cannot act on is a refusal that has not done its job. -/
def Expr.kindName : Expr → String
  | .intLit .. => "IntegerLiteral"
  | .charLit .. => "CharacterLiteral"
  | .strLit .. => "StringLiteral"
  | .predefined .. => "PredefinedExpr"
  | .floatLit .. => "FloatingLiteral"
  | .boolLit .. => "CXXBoolLiteralExpr"
  | .nullPtrLit .. => "CXXNullPtrLiteralExpr"
  | .choose .. => "ChooseExpr"
  | .declRef .. => "DeclRefExpr"
  | .member .. => "MemberExpr"
  | .index .. => "ArraySubscriptExpr"
  | .call .. => "CallExpr"
  | .binop .. => "BinaryOperator"
  | .compoundAssign .. => "CompoundAssignOperator"
  | .unop .. => "UnaryOperator"
  | .cond .. => "ConditionalOperator"
  | .paren .. => "ParenExpr"
  | .exprWithCleanups .. => "ExprWithCleanups"
  | .materializeTemporary .. => "MaterializeTemporaryExpr"
  | .implicitCast .. => "ImplicitCastExpr"
  | .cast .. => "CStyleCastExpr"
  | .initList .. => "InitListExpr"
  | .arrayInitList .. => "InitListExpr"
  | .designatedUpdate .. => "DesignatedInitUpdateExpr"
  | .implicitValueInit .. => "ImplicitValueInitExpr"
  | .compoundLit .. => "CompoundLiteralExpr"
  | .typeTrait .. => "UnaryExprOrTypeTraitExpr"
  | .constExpr .. => "ConstantExpr"
  | .vaArg .. => "VAArgExpr"
  | .offsetOf .. => "OffsetOfExpr"
  | .genericSelection .. => "GenericSelectionExpr"
  | .unsupported k _ _ => k

/-- Sub-expressions, including the expression itself. Effect checks can omit
the unevaluated operands of type traits in the admitted C tier. -/
def Expr.subexprs (e : Expr) (includeTraitOperands : Bool := true) : List Expr :=
  match e with
  | .member b _ _ _ _ _ .. => e :: b.subexprs includeTraitOperands
  | .index b i _ _ .. => e :: (b.subexprs includeTraitOperands ++ i.subexprs includeTraitOperands)
  | .call c args _ _ .. =>
      e :: (c.subexprs includeTraitOperands ++ args.flatMap (·.subexprs includeTraitOperands))
  | .binop _ l r _ _ .. | .compoundAssign _ l r _ _ _ _ .. =>
      e :: (l.subexprs includeTraitOperands ++ r.subexprs includeTraitOperands)
  | .unop _ s _ _ _ .. => e :: s.subexprs includeTraitOperands
  | .cond c t f _ _ .. | .choose c t f _ _ .. =>
      e :: (c.subexprs includeTraitOperands ++ t.subexprs includeTraitOperands ++
        f.subexprs includeTraitOperands)
  | .paren s _ _ .. | .exprWithCleanups s _ _ .. | .materializeTemporary s _ _ ..
  | .implicitCast _ s _ _ .. | .cast _ s _ _ .. =>
      e :: s.subexprs includeTraitOperands
  | .initList xs _ _ _ .. => e :: xs.flatMap (·.subexprs includeTraitOperands)
  | .arrayInitList xs filler _ _ _ .. =>
      e :: (xs.flatMap (·.subexprs includeTraitOperands) ++
        filler.flatMap (·.subexprs includeTraitOperands))
  | .designatedUpdate base update _ _ .. =>
      e :: (base.subexprs includeTraitOperands ++ update.subexprs includeTraitOperands)
  | .genericSelection control selected _ _ .. =>
      e :: (control.subexprs includeTraitOperands ++ selected.subexprs includeTraitOperands)
  | .compoundLit i _ _ .. => e :: i.subexprs includeTraitOperands
  | .typeTrait _ _ (some s) _ _ .. =>
      if includeTraitOperands then e :: s.subexprs includeTraitOperands else [e]
  | .constExpr _ (some s) _ _ .. => e :: s.subexprs includeTraitOperands
  | .vaArg ap _ _ .. => e :: ap.subexprs includeTraitOperands
  | _ => [e]

/-! ### A size measure, for STATED termination

`docs/backlog/c.md` (2026-08-23-c-5): a green build is not a termination
argument. The evaluator's recursion is justified by this measure
EXPLICITLY rather than left to structural inference, and the measure is
defined through `subexprs` so it introduces **no new recursion** — the
nested `List Expr` pattern that defeats inference is elaborated there,
once, and never again. -/

/-- The number of expression nodes in `e`, itself included. -/
def Expr.size (e : Expr) : Nat := e.subexprs.length

/-- The same measure over an argument list. -/
def Expr.sizes (es : List Expr) : Nat := (es.flatMap (·.subexprs)).length

@[simp] theorem Expr.sizes_nil : Expr.sizes [] = 0 := by
  rfl

-- Every constructor the evaluator RECURSES INTO needs its own equation, or
-- `omega` has no fact relating a subterm's size to its parent's. The first
-- attempt covered only member/index/paren/call and left nine goals unprovable
-- at `decreasing_by` — a STATED measure is only as good as the lemmas that
-- let the checker use it.
-- (`size_pos` was once tried here and removed as unprovable by `cases e`:
-- `typeTrait` and `constExpr` carry an `Option Expr`, so `subexprs` has two
-- clauses each and `cases` does not split them. That diagnosis was right about
-- the TACTIC and wrong about the FACT — see `Expr.size_pos` below, which the
-- argument-list measure does need.)

@[simp] theorem Expr.size_member (b : Expr) (f : String) (a : Bool) (t : String) (s : CSpan)
    (recordId : Option DeclarationId) (q : Option LeanModels.Clang.QualType) :
    (Expr.member b f a t s recordId q).size = b.size + 1 := by
  simp [Expr.size, Expr.subexprs]

@[simp] theorem Expr.size_index (b i : Expr) (t : String) (s : CSpan) (q : Option LeanModels.Clang.QualType) :
    (Expr.index b i t s q).size = b.size + i.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_paren (sub : Expr) (t : String) (s : CSpan) (q : Option LeanModels.Clang.QualType) :
    (Expr.paren sub t s q).size = sub.size + 1 := by
  simp [Expr.size, Expr.subexprs]

@[simp] theorem Expr.size_exprWithCleanups (sub : Expr) (t : String) (s : CSpan)
    (q : Option LeanModels.Clang.QualType) :
    (Expr.exprWithCleanups sub t s q).size = sub.size + 1 := by
  simp [Expr.size, Expr.subexprs]

@[simp] theorem Expr.size_materializeTemporary (sub : Expr) (t : String) (s : CSpan)
    (q : Option LeanModels.Clang.QualType) :
    (Expr.materializeTemporary sub t s q).size = sub.size + 1 := by
  simp [Expr.size, Expr.subexprs]

@[simp] theorem Expr.size_call (c : Expr) (args : List Expr) (t : String) (s : CSpan) (q : Option LeanModels.Clang.QualType) :
    (Expr.call c args t s q).size = c.size + Expr.sizes args + 1 := by
  simp [Expr.size, Expr.sizes, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_unop (sub : Expr) (op : String) (post : Bool) (t : String) (sp : CSpan) (q : Option LeanModels.Clang.QualType) :
    (Expr.unop op sub post t sp q).size = sub.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_binop (l r : Expr) (op : String) (t : String) (sp : CSpan) (q : Option LeanModels.Clang.QualType) :
    (Expr.binop op l r t sp q).size = l.size + r.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_compoundAssign (l r : Expr) (op lhsTy resultTy t : String) (sp : CSpan)
    (q lhsQ resultQ : Option LeanModels.Clang.QualType) :
    (Expr.compoundAssign op l r lhsTy resultTy t sp q lhsQ resultQ).size = l.size + r.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_cond (c a b : Expr) (t : String) (sp : CSpan) (q : Option LeanModels.Clang.QualType) :
    (Expr.cond c a b t sp q).size = c.size + a.size + b.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_choose (c a b : Expr) (t : String) (sp : CSpan) (q : Option LeanModels.Clang.QualType) :
    (Expr.choose c a b t sp q).size = c.size + a.size + b.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_genericSelection (control selected : Expr)
    (associations : List (Bool × Expr)) (t : String) (sp : CSpan)
    (q : Option LeanModels.Clang.QualType) :
    (Expr.genericSelection control selected associations t sp q).size =
      control.size + selected.size + 1 := by
  simp [Expr.size, Expr.subexprs]

@[simp] theorem Expr.size_implicitCast (sub : Expr) (ck : String) (t : String) (sp : CSpan)
    (q : Option LeanModels.Clang.QualType) :
    (Expr.implicitCast ck sub t sp q).size = sub.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_cast (sub : Expr) (ck : String) (t : String) (sp : CSpan)
    (q : Option LeanModels.Clang.QualType) :
    (Expr.cast ck sub t sp q).size = sub.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_compoundLit (i : Expr) (t : String) (sp : CSpan) (q : Option LeanModels.Clang.QualType) :
    (Expr.compoundLit i t sp q).size = i.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.size_constExpr (value : String) (sub : Expr)
    (ty : String) (sp : CSpan) (q : Option LeanModels.Clang.QualType) :
    (Expr.constExpr value (some sub) ty sp q).size = sub.size + 1 := by
  simp [Expr.size, Expr.subexprs] <;> omega

@[simp] theorem Expr.sizes_cons (e : Expr) (es : List Expr) :
    Expr.sizes (e :: es) = e.size + Expr.sizes es := by
  simp [Expr.sizes, Expr.size] <;> omega

/-- Every node counts itself: **each `subexprs` clause emits `e`**, either as
`e :: …` or as the catch-all `[e]`, so the list is never empty.

This is what `evalArgs` needs and `evalExpr` never did. Walking an argument
LIST, the step from `e :: es` to `es` drops `e.size` from the measure, and that
is a decrease only if `e.size` is not zero — where every goal in the expression
walk closed on the `+ 1` a constructor contributes.

The proof is three lines because it does NOT go through `cases e`: `eq_def`
turns the definition back into its `match`, and `split` splits the *clauses* —
including the `some`/`none` pair under `typeTrait` and `constExpr` that a
`cases` on `e` leaves as one unreduced variable. The earlier removal read a
tactic's failure as the fact's absence. -/
@[simp] theorem Expr.size_pos (e : Expr) : 0 < e.size := by
  unfold Expr.size
  rw [Expr.subexprs.eq_def]
  split <;> simp

/-- The expressions a block-scope declaration contains. -/
def Decl.exprs : Decl → List Expr
  | .var _ _ _ _ (some i) _ _ _ .. => i.subexprs
  | _ => []

/-- Statements nested inside a statement, including itself. -/
def Stmt.substmts : Stmt → List Stmt
  | s@(.compound body _) => s :: body.flatMap Stmt.substmts
  | s@(.ifS _ t none _) => s :: t.substmts
  | s@(.ifS _ t (some e) _) => s :: (t.substmts ++ e.substmts)
  | s@(.forS (some i) _ _ b _) => s :: (i.substmts ++ b.substmts)
  | s@(.forS none _ _ b _) => s :: b.substmts
  | s@(.whileS _ b _) => s :: b.substmts
  | s@(.doS b _ _) => s :: b.substmts
  | s@(.label _ b _) => s :: b.substmts
  | s@(.switchS _ b _) => s :: b.substmts
  | s@(.caseS _ b _) => s :: b.substmts
  | s@(.caseRange _ _ b _) => s :: b.substmts
  | s@(.defaultS b _) => s :: b.substmts
  | s => [s]

/-- The expressions a statement holds DIRECTLY (its own operands), not
those of its nested statements — `substmts` already reaches those. -/
def Stmt.ownExprs : Stmt → List Expr
  | .decl ds _ => ds.flatMap Decl.exprs
  | .ifS c _ _ _ => c.subexprs
  | .forS _ c inc _ _ =>
      (c.map Expr.subexprs).getD [] ++ (inc.map Expr.subexprs).getD []
  | .whileS c _ _ => c.subexprs
  | .doS _ c _ => c.subexprs
  | .ret (some v) _ => v.subexprs
  | .expr e _ => e.subexprs
  | .nullStmt _ => []
  | .switchS c _ _ => c.subexprs
  | .caseS v _ _ => v.subexprs
  | .caseRange lo hi _ _ => lo.subexprs ++ hi.subexprs
  | .defaultS _ _ => []
  | _ => []

namespace TranslationUnit

/-- Functions WITH a body — definitions, not prototypes. -/
def functionDefns (u : TranslationUnit) : List FunctionDefn :=
  u.items.filterMap fun i => match i with
    | .fn f => if f.body.isSome then some f else none
    | .decl _ => none

/-- File-scope objects: the top-level `var` declarations. -/
def fileScopeObjects (u : TranslationUnit) : List Decl :=
  u.items.filterMap fun i => match i with
    | .decl d@(.var ..) => some d
    | _ => none

/-- Folded enum constants keyed by their frontend declaration handles,
including enums nested in parser-native record declaration fields. -/
def enumBindingsDecl : Decl → List (DeclarationId × Int)
  | .enum _ constants _ _ => constants.filterMap fun constant =>
      match constant with
      | .enumConst (some id) _ (some value) _ .. => value.toInt?.map (fun n => (id, n))
      | _ => none
  | .record _ _ fields _ _ .. => fields.flatMap enumBindingsDecl
  | _ => []

def enumBindings (u : TranslationUnit) : List (DeclarationId × Int) :=
  u.items.flatMap fun item => match item with
    | .fn f => (f.body.map (fun body => body.substmts.flatMap fun stmt =>
        match stmt with
        | .decl decls _ => decls.flatMap enumBindingsDecl
        | _ => [])).getD []
    | .decl d => enumBindingsDecl d

/-- Every statement in the unit (function bodies only — C has no
statements outside one). -/
def stmts (u : TranslationUnit) : List Stmt :=
  u.functionDefns.flatMap fun f => (f.body.map Stmt.substmts).getD []

/-- Every expression in the unit: file-scope initializers, plus every
statement's own operands. -/
def exprs (u : TranslationUnit) : List Expr :=
  (u.items.flatMap fun i => match i with
      | .decl d => d.exprs
      | .fn _ => []) ++ u.stmts.flatMap Stmt.ownExprs

/-- Peel the conversions clang wraps a callee in. -/
def calleeHead : Expr → Expr
  | .implicitCast _ s _ _ .. => calleeHead s
  | .paren s _ _ .. => calleeHead s
  | e => e

/-- Call sites whose callee is NOT a direct function reference — the
callback protocol. All 19 in the corpus go through `movecb`. -/
def indirectCalls (u : TranslationUnit) : List Expr :=
  u.exprs.filter fun e => match e with
    | .call callee _ _ _ .. =>
        match calleeHead callee with
        | .declRef _ _ "FunctionDecl" _ _ .. => false
        | _ => true
    | _ => false

/-- Statements the tier does not model — `switch` today, and nothing else. -/
def unsupportedStmts (u : TranslationUnit) : List Stmt :=
  u.stmts.filter fun s => match s with
    | .unsupported .. => true
    | _ => false

end TranslationUnit

end LeanModels.C
