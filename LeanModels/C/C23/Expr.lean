import LeanModels.C.C23.Memory
import LeanModels.SoftFloat.Transfer

/-!
# §6.5 Expressions — the evaluator — M2 inch 3

C23 (N3220) §6.5, subclause by subclause. Citations follow
`docs/c23-spec-mirror.md`; refusals name their Annex J.2 index.

## FUEL'S FATE, decided BEFORE this file was written

The family checklist's step 7 (`docs/family-architecture.md` §8.4) makes
this a decision about the interpreter's TYPE, not a proof-layer choice
deferrable to later. **This layer is FUEL-FREE**: `evalExpr` is
STRUCTURALLY recursive on `Expr`, and calls enter through a HANDLER
parameter, which is where fuel arrives at inch 5.

Measured, on the shipped corpus:

| | |
| --- | ---: |
| full expressions | 1169 |
| …containing a call | 298 |
| **…CALL-FREE — the fuel-free fragment** | **871 (74.5%)** |

Three reasons this is the right cut:

1. **The fuel-free fragment is the majority of the corpus**, and the
   checklist gives that fragment the shared `mvcgen` and ~120 lines of
   `@[spec]` while the fuel-recursive points get the tier's own threshold
   assembly. Making the expression layer fuel-free maximizes the half
   that is cheap.
2. **This tier wants kernel-reducible runs.** Inch 2 shipped 50 `#guard`s
   and inch 6's scorer must RUN programs; structural recursion delivers
   that with no fuel argument to pick.
3. It is what `docs/c-semantics-design.md` §4.2 already required —
   *"every helper the interpreter computes with is STRUCTURAL
   recursion."*

So the fuel parameter does not appear here and is not owed here. The
`∃ n, ∀ fuel ≥ n` threshold form is assembled AROUND this layer, never
inside it.

**Where fuel DOES arrive, measured — and it is two places, not one.**
Inch 4's census corrected this file's first draft, which said "inch 5,
with calls":

* **Inch 4, with LOOPS.** The corpus has **84 loops** (50 `for`, 29 `do`,
  5 `while`), and an iteration count is not structurally bounded, so the
  statement evaluator needs fuel whether or not a call is involved.
  Measured: **64 of the 84 contain a call and 20 do not** — and those 20
  need fuel just the same.
* **Inch 5, with CALLS**, through `CallHandler`.

Expressions are fuel-free because neither construct is one.

## The monad, and its layer order

```
EvalM α := ExceptT Refusal (StateT Mem Id) α
```

**State OUTSIDE `Except` — the state-RETAINING order.** The `mvcgen`
pilot proved by `rfl` that `StateT σ (ExceptT ρ …)` discards the state on
a raise, which would make every refusal forget what the program had
already written. `Run.exn` carries a state field for exactly this reason,
and the C scoreboard's REFUSE rows are worth much less if they cannot say
what had happened by the time the refusal fired.

**Every refusal routes through a NAMED primitive** (`refuseUB`,
`refuseValue`, `refuseUnsupported`, `refuseLibc`) rather than a bare
polymorphic `throw`, which the pilot found unusable. That is also the
shape `@[spec]` lemmas want, so the law and the tooling agree.

## The order the census imposed

Inch 2's census measured which operations actually carry the traffic, and
this file is written in that order rather than the standard's:

| | sites | |
| --- | ---: | --- |
| lvalue conversion (§6.3.2.1p2) | **1837** | the load-bearing implicit |
| array-to-pointer decay (§6.3.2.1p3) | **405** | the common path |
| `p->f` (§6.5.3.4) | **226** | …and its partner |
| `&` (§6.5.4.2p3) | 106 | the rare case |
| `*` (§6.5.4.2p4) | 24 | the rarest |

**`evalLValue` has exactly five cases, and the census is why**: the 1837
lvalue conversions take their operand from `DeclRefExpr` 1406,
`MemberExpr` 248, `ArraySubscriptExpr` 169, `UnaryOperator` (`*`) 13, and
`CompoundLiteralExpr` 1 — and the 287 assignments plus 63
increments target the same four kinds. One function serves both.
-/

namespace LeanModels.C.C23

open LeanModels.C (Expr CSpan DeclarationId)

/-! ## The evaluation monad -/

/-- The expression evaluator's monad. See the module docstring: `ExceptT`
OUTSIDE `StateT` is the state-retaining order, and it is not the obvious
one. -/
abbrev EvalM (α : Type) := SemMWith Mem Refusal CDetail Mem α

/-- Run an evaluation against a starting memory, keeping BOTH halves: the
outcome and the memory as it stood when the outcome was produced. A
refusal that threw away its memory could not say what had happened.

The `Halt` wrapper is the uncatchable layer (`Memory.lean` §3.4) — a
`timeout` or an out-of-tier construct answers there and carries no
`Mem` alongside, because neither is an observation. -/
def EvalM.run (m : Mem) (x : EvalM α) :
    Except (Loud CDetail Mem) (Except Refusal α × Mem) :=
  StateT.run x m

/-- The run's VERDICT, in `docs/c23-goal.md` §3's vocabulary. This is what
a scoreboard reads, and it is where the diagnostic snapshot stops: there
is nowhere to put a `Mem` in an `Outcome`. -/
def EvalM.verdict (m : Mem) (x : EvalM α) : Outcome α :=
  match EvalM.run m x with
  | .ok (.ok a, _) => .ok a
  | .ok (.error .aborted, _) => .aborted
  | .ok (.error (.indeterminateRead ..), _) => .unsupported indeterminateReadMessage
  | .ok (.error r, _) => .refused r
  | .error .timeout => .timeout
  | .error (.unsupported _ msg _) => .unsupported msg

/-! ### The named refusal primitives

`docs/backlog.md` §L61: *never a bare polymorphic `throw`* — route
refusals through named primitives, each of which can carry its own
`@[spec]`. The three never-pooled causes are one constructor each, so the
partition is structural rather than a convention. -/

/-- Refuse with undefined behavior from the MEMORY rules (§2 of the
memory model). Cause: `ub`, which never retires. -/
def refuseUB (f : MemFault) : EvalM α := throw (.memUB f)

/-- Refuse with undefined behavior from the VALUE rules (§6.5.1p5 and
friends). Cause: `ub`. -/
def refuseValue (u : UB) : EvalM α := throw (.valueUB u)

/-- Refuse a construct outside the tier's vocabulary. Cause:
`unsupported`, which retires by climbing a rung.

**It answers in the `Halt` BASE, not in `ExceptT`** — per §3.4, an
out-of-tier refusal is uncatchable by definition rather than by a
per-construct proof. And **this primitive takes the memory as its
argument**, capturing it AS IT STOOD at the refusal site, so no call site
can forget to.

The snapshot is diagnostic only, and since the Core adoption **both
guards are enforced in `Core` rather than here**: `Loud`'s `BEq` ignores
the snapshot and `Loud.observable` has nowhere to put one. This tier's
`Outcome` is the third. -/
def refuseUnsupported (what : String) : EvalM α := fun m =>
  .error (.unsupported (.unsupported ()) what (some m))

/-- Refuse an unmodeled library function. Cause: `libc`, which retires by
widening the slice. -/
def refuseLibc (name : String) : EvalM α := throw (.libc name)

/-- C23 §7.22.4.1 terminal abnormal termination.  This is deliberately a
named terminal primitive rather than a `libc` refusal: the public verdict
preserves that the program aborted. -/
def terminateAbort : EvalM α := throw .aborted

/-! ### Lifting the memory model

Inch 2's operations are pure functions over `Mem`. These are the lifts,
and they are the reason inch 2 threaded `Mem` explicitly: not one of its
definitions had to be rewritten. -/

/-- Read through a pure memory operation. N3220 §6.3.2.1p2 requires
the register premise and an uninitialized automatic object. The lvalue
supplies the first premise. On that direct scalar path, an entirely
unwritten object supplies the second. -/
def readMem (f : Mem → MRes α) (couldBeUninitializedRegister : Unit → Bool := fun _ => false) :
    EvalM α := do
  let m ← get
  match f m with
  | .ok a => pure a
  | .error (.indeterminateRead o off) =>
      if couldBeUninitializedRegister () && off == 0 &&
          (m.get? o).any (fun c => c.dur == .automatic && c.bytes.all (· == CByte.indet)) then
        refuseUB (.indetAutomatic o off)
      else refuseUnsupported indeterminateReadMessage
  | .error e => throw e

/-- Write through a pure memory operation. The new memory is committed
only on success; on a refusal the OLD memory is retained, which is the
layer order doing its job. -/
def writeMem (f : Mem → MRes Mem) : EvalM Unit := do
  match f (← get) with
  | .ok m => set m
  | .error e => throw e

def popVaArg (p : Ptr) : EvalM CallArgument := do
  match Mem.vaArg (← get) p with
  | .ok (v, m) => set m; pure v
  | .error e => throw e


/-- Decode the parser's canonical value for the first string-object slice.
Only printable ASCII characters are admitted here; escape spellings stay
loud until the envelope carries their parser-decoded bytes.  The quotes are
the value delimiters supplied by Clang, not source text reparsed by Lean. -/
def plainStringBytes (s : String) : Option (List CByte) :=
  match s.toList with
  | '"' :: rest =>
      match rest.reverse with
      | '"' :: revBody =>
          let body := revBody.reverse
          if body.all (fun c => c.toNat >= 32 && c.toNat < 127 && c != '\\') then
            some ((body.map (fun c => CByte.conc (UInt8.ofNat c.toNat))) ++
              [CByte.conc 0])
          else none
      | _ => none
  | _ => none

/-! Parser metadata helpers.  `float_bits_hex` is emitted by the pinned
Clang probe, not copied from C source spelling.  Decoding this envelope field
is therefore not a second C literal parser; it merely reconstructs the exact
bit pattern Clang already chose. -/

def hexDigitValue : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
  | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | 'A' => some 10 | 'B' => some 11 | 'C' => some 12 | 'D' => some 13
  | 'E' => some 14 | 'F' => some 15 | _ => none

def hexNatAux : List Char → Nat → Option Nat
  | [], n => some n
  | c :: cs, n => do
      let d ← hexDigitValue c
      hexNatAux cs (n * 16 + d)

def hexNat (s : String) : Option Nat :=
  if s.toList.isEmpty then none else hexNatAux s.toList 0

def floatLiteralValue (bitsHex : Option String) (bitWidth : Option Nat) : EvalM CVal :=
  match bitsHex, bitWidth with
  | some bits, some 32 =>
      match hexNat bits with
      | some n =>
          if n < 2 ^ 32 then
            pure (.float32 (Float32.Model.ofBits (UInt32.ofNat n)))
          else refuseUnsupported "floating literal bit pattern exceeds binary32"
      | none => refuseUnsupported "floating literal has invalid parser-native bits"
  | some bits, some 64 =>
      match hexNat bits with
      | some n =>
          if n < 2 ^ 64 then
            pure (.float64 (Float.Model.ofBits (UInt64.ofNat n)))
          else refuseUnsupported "floating literal bit pattern exceeds binary64"
      | none => refuseUnsupported "floating literal has invalid parser-native bits"
  | _, some 80 => refuseUnsupported "long double floating literal"
  | some _, some _ => refuseUnsupported "unsupported floating literal width"
  | _, _ => refuseUnsupported "floating literal lacks parser-native bits"

/-! Parser-native scalar projections.  These consume the C frontend's
structured builtin or enumeration leaf and never infer a width from a
display spelling.  A typedef reference remains unresolved here because the
envelope carries its declaration identity, while its underlying typedef type
is a separate declaration observation. -/
def intTyOfStructured : LeanModels.Clang.QualType → Option IntTy
  | .qualified _ _ base => intTyOfStructured base
  | .cBuiltinKind kind =>
      match kind with
      | .bool => some IntTy.bool_
      | .char | .signedChar => some IntTy.char_
      | .unsignedChar => some IntTy.uchar
      | .short => some IntTy.short_
      | .unsignedShort => some IntTy.ushort
      | .int => some IntTy.int_
      | .unsignedInt => some IntTy.uint
      | .long | .longLong => some IntTy.long_
      | .unsignedLong | .unsignedLongLong => some IntTy.ulong
      | .int128 => some IntTy.int128_
      | .uint128 => some IntTy.uint128
      | _ => none
  | .cBuiltin _ => none
  | .enumeration _ => some IntTy.int_
  | _ => none

/-- Integer conversion for literal nodes. The node-carried parser type is the
only admitted source of width and signedness for this conversion family. -/
def intTyOfNode (structured : Option LeanModels.Clang.QualType) : EvalM IntTy :=
  match structured.bind intTyOfStructured with
  | some t => pure t
  | none => refuseUnsupported "integer literal lacks parser-native QualType"

def floatBitsOfStructured : LeanModels.Clang.QualType → Option Nat
  | .qualified _ _ base => floatBitsOfStructured base
  | .cBuiltinKind .float => some 32
  | .cBuiltinKind .double => some 64
  | _ => none

/-- Byte size for a scalar parser-native type.  Aggregate sizes remain a
layout observation, while scalar pointer strides can be obtained directly
from Clang's recursive `QualType` tree. -/
def scalarSizeOfStructured (type : LeanModels.Clang.QualType) : Option Nat :=
  (intTyOfStructured type).map IntTy.storageBytes
    |>.orElse (fun _ => (floatBitsOfStructured type).map (· / 8))

def objectSizeOfStructured (type : LeanModels.Clang.QualType)
    (recordSize : LeanModels.Clang.DeclarationHandle → Option Nat := fun _ => none) : Option Nat :=
  match type with
  | .qualified _ _ base | .restrictQualified base => objectSizeOfStructured base recordSize
  | .array element (some extent) => objectSizeOfStructured element recordSize |>.map (· * extent)
  | .record handle => recordSize handle
  | .pointer _ => some 8
  | type => scalarSizeOfStructured type

def structuredDeclarationId : LeanModels.Clang.QualType → Option DeclarationId
  | .record declaration | .enumeration declaration | .typedefRef declaration =>
      some { value := declaration.value }
  | .qualified _ _ base => structuredDeclarationId base
  | _ => none

/-- Integer promotions on the pinned LP64 profile. -/
def promoteIntTy (t : IntTy) : IntTy :=
  if t.bits < IntTy.int_.bits then IntTy.int_ else t

/-! ## The environment

An expression cannot change which names are in scope — only a declaration
can, and declarations are inch 4 — so the environment is a read-only
PARAMETER here rather than part of the state. Measured: 250 block-scope
objects, of which **zero** are `static`, so a name maps to one object for
the lifetime of its frame. -/

/-- Names in scope, innermost first. -/
abbrev Env := List (String × ObjId)

abbrev IdEnv := List (DeclarationId × ObjId)

/-- Resolve a name to its object. Innermost binding wins (§6.2.1). -/
def Env.lookup? (env : Env) (name : String) : Option ObjId :=
  (env.find? (·.1 == name)).map (·.2)

def IdEnv.lookup? (env : IdEnv) (id : DeclarationId) : Option ObjId :=
  (env.find? (·.1 == id)).map (·.2)

/-! ## Calls — the handler, and where fuel will arrive

Inch 3 is fuel-free (module docstring). A call is the one expression that
can recurse into an arbitrary function body, so it is not evaluated here:
it is delegated to a HANDLER supplied by the caller. Inch 5 supplies one
that threads fuel; until then `noCalls` refuses, loudly and by cause. -/

/-- Peel the conversions clang wraps a callee in and read its name.
`"<indirect>"` is a call through a pointer — measured 19, every one
through the `movecb` callback parameter. -/
def calleeNameOf : Expr → String
  | .implicitCast _ s _ _ .. => calleeNameOf s
  | .paren s _ _ .. => calleeNameOf s
  | .declRef _ n _ _ _ .. => n
  | _ => "<indirect>"

/-- What a call site delegates to: the callee expression and its arguments
**already evaluated, in the CALLER's scope**.

**This signature is the repair of inch 5's open problem, and the two
rejected shapes are worth keeping.** §6.5.3.3p4 evaluates arguments in the
caller's scope, so inch 5 first tried `(Expr → EvalM CVal) → …`, handing
`evalExpr ctx` to the handler as a closure. That broke termination: a
recursive function passed into an OPAQUE callee cannot be shown to
terminate, because nothing constrains what the callee does with it. The
retreat was `List Expr` — unevaluated — which terminated by handing the
handler a job it had no way to do, and every nested call to a defined
function refused.

The shape that works is the one `CallHandler`'s own note predicted:
**`evalArgs` inside the mutual block below, feeding the handler VALUES.**
The recursion is then `evalExpr`'s, where the measure already lives, and
the callee is opaque again because it receives data rather than a function.

**The ORDER is now this layer's, not the handler's**, and that is a
deliberate move of the obligation. §6.5.3.3p10 leaves argument evaluation
indeterminately sequenced (`J.1(16)`); `evalArgs` fixes left-to-right as
the CANONICAL order for extracting witnesses, and Thomas's `∀ order`
ruling becomes a theorem about `evalArgs` — a thing that can be stated —
rather than a property of an opaque handler, which could not be. -/
abbrev CallHandler := Expr → Option CVal → List CallArgument → EvalM CVal

/-- The handler for a context with **no program behind it**: a bare `Ctx`
knows names, enums and layout, and nothing about function definitions, so
there is nothing to call INTO.

It refuses as `unsupported` — the cause that retires by climbing a rung —
NOT `libc`, and never silently. The arguments have already been evaluated
by then (`evalArgs`), which is deliberate: their effects are the caller's,
and a refusal must not un-happen them.

The message used to read *"the call semantics is inch 5"*. Inch 5 has
landed and `callFn` supplies a real handler; what remains true is only
that THIS context has no program. -/
def noCalls : CallHandler := fun callee _ _ =>
  refuseUnsupported
    s!"call to '{calleeNameOf callee}' in a context with no program — call it through 'callByName'"

/-! ## Layout — the implementation-defined surface, PARAMETERIZED

`sizeof` and `offsetof` are **implementation-defined** (`J.3.10`), so
they are not baked in: they arrive the way the integer widths do, as
facts a profile supplies and a probe can check on any host. The fixture
instantiates this with offsets measured by `_Static_assert` on BOTH hosts
in `docs/c-profile.json`, which agree.

Deriving layout from the type spellings inside Lean would mean writing
the C type parser `docs/c-envelope-schema.md` §3 exists to avoid. -/

/-- The implementation-defined layout facts an evaluator needs.

Every table is keyed on the type spelling **exactly as the AST carries
it** — `"Pos"`, `"const Pos *"` — never on a parsed type. That is the
same decision `docs/c-envelope-schema.md` §3 made for `String` itself, and
it is what keeps the C type parser out of the tier. -/
structure Layout where
  zeroNullPointer : Bool := false
  declSize : DeclarationId → Option Nat := fun _ => none
  recordSizeDecl : DeclarationId → Option Nat := fun _ => none
  recordAlignmentDecl : DeclarationId → Option Nat := fun _ => none
  structuredType : DeclarationId → Option LeanModels.Clang.QualType := fun _ => none
  structuredExprType : Nat → Option LeanModels.Clang.QualType := fun _ => none
  structuredExprTypeAt : Nat → Option Nat → String → String → Option LeanModels.Clang.QualType :=
    fun offset _ _ _ => structuredExprType offset
  pointeeSizeDecl : DeclarationId → Option Nat := fun _ => none
  elementSizeDecl : DeclarationId → Option Nat := fun _ => none
  fieldOffTypeDecl : DeclarationId → String → Option Nat := fun _ _ => none
  fieldOffStructuredDecl : DeclarationId → LeanModels.Clang.QualType → Option Nat :=
    fun _ _ => none
  fieldSizeDecl : DeclarationId → String → Option Nat := fun _ _ => none
  fieldStructuredDecl : DeclarationId → String → Option LeanModels.Clang.QualType := fun _ _ => none
  fieldDecl : DeclarationId → String → Option DeclarationId := fun _ _ => none
  fieldOffDecl : DeclarationId → String → Option Nat := fun _ _ => none
  fieldBitsDecl : DeclarationId → String → Option (Nat × Nat) := fun _ _ => none
  flexibleFieldDecl : DeclarationId → String → Bool := fun _ _ => false
  flexibleInitializerExtra : DeclarationId → Option Nat := fun _ => none
  terminalFieldDecl : DeclarationId → String → Bool := fun _ _ => false
  membersDecl : DeclarationId → Option (List (String × String)) := fun _ => none
  memberRecordDecl : DeclarationId → String → Option DeclarationId := fun _ _ => none
  isUnionDecl : DeclarationId → Bool := fun _ => false

/-- The declaration identity carried by a direct base expression.  Clang's
member access facts are keyed by the declaration that owns the object; the
spelling fallback remains only for older envelopes without that identity. -/
def directDeclId : Expr → Option DeclarationId
  | .declRef id _ _ _ _ .. => id
  | .implicitCast _ sub _ _ .. => directDeclId sub
  | .cast _ sub _ _ .. => directDeclId sub
  | .paren sub _ _ .. => directDeclId sub
  | _ => none

/-- Resolve bit-field facts through parser-native declaration identity. -/
def Layout.fieldBitsAt (layout : Layout) (base : Expr) (field : String) :
    Option (Nat × Nat) :=
  (directDeclId base).bind (fun did => layout.fieldBitsDecl did field)


/-- Resolve bit-field facts from parser-native aggregate declaration identity. -/
def Layout.fieldBitsDeclAt (layout : Layout) (decl : Option DeclarationId)
    (ty : String) (field : String) : Option (Nat × Nat) :=
  decl.bind (fun did => layout.fieldBitsDecl did field)

/-- Resolve flexible-array membership from parser-native declaration identity. -/
def Layout.flexibleFieldDeclAt (layout : Layout) (decl : Option DeclarationId)
    (ty : String) (field : String) : Bool :=
  match decl with
  | some did =>
      layout.flexibleFieldDecl did field
  | none => false

/-- Resolve a member extent through parser-native declaration identity. -/
def Layout.fieldSizeAt (layout : Layout) (base : Expr) (field : String) :
    Option Nat :=
  (directDeclId base).bind (fun did => layout.fieldSizeDecl did field)

/-- Resolve a named member offset through parser-native base declaration identity. -/
def Layout.fieldOffAt (layout : Layout) (base : Expr) (field : String) :
    Option Nat :=
  (directDeclId base).bind (fun did => layout.fieldOffDecl did field)

/-- Resolve a member offset from an object's parser-native declaration identity.
Aggregate initialization has no base expression, so its declaration identity
is passed explicitly. -/
def Layout.fieldOffDeclAt (layout : Layout) (decl : Option DeclarationId)
    (ty : String) (field : String) : Option Nat :=
  decl.bind (fun did => layout.fieldOffDecl did field)

/-- Resolve a member's own parser declaration identity. -/
def Layout.fieldDeclAt (layout : Layout) (decl : Option DeclarationId)
    (field : String) : Option DeclarationId :=
  decl.bind (fun did => layout.fieldDecl did field)

def Layout.fieldOffTypeDeclAt (layout : Layout) (decl : Option DeclarationId)
    (ty fieldTy : String) : Option Nat :=
  decl.bind (fun did => layout.fieldOffTypeDecl did fieldTy)

def Layout.fieldOffStructuredDeclAt (layout : Layout) (decl : Option DeclarationId)
    (structured : Option LeanModels.Clang.QualType) : Option Nat :=
  structured.bind (fun q => decl.bind (fun did => layout.fieldOffStructuredDecl did q))

/-- Resolve a member extent from parser-native member facts. -/
def Layout.fieldExtentAt (layout : Layout) (base : Expr) (field : String) (fieldTy : String)
    (recordLike : Bool) : Option Nat :=
  if recordLike then
    layout.fieldSizeAt base field
  else
    layout.fieldSizeAt base field

def Layout.arrayElementSizeAt (_layout : Layout) (_arrayTy _elementTy : String) :
    Option Nat := none

def Layout.sizeAt (layout : Layout) (decl : Option DeclarationId) (ty : String) :
    Option Nat :=
  decl.bind layout.declSize |>.orElse (fun _ =>
    -- Aggregate initializers carry the record declaration identity itself,
    -- while a variable's TypeLayout is keyed by the variable declaration.
    -- Consult the parser-native record layout before resolving a QualType.
    decl.bind layout.recordSizeDecl) |>.orElse (fun _ =>
    decl.bind layout.structuredType
      |>.bind (LeanModels.Clang.QualType.resolveTypedefs
        (fun declaration => layout.structuredType { value := declaration.value }) 32)
      |>.bind fun structured =>
        match structured.unqualified with
        | .record declaration => layout.recordSizeDecl { value := declaration.value }
        | _ => objectSizeOfStructured structured)

def Layout.sizeAtStructured (layout : Layout) (decl : Option DeclarationId)
    (ty : String) (structured : Option LeanModels.Clang.QualType) : Option Nat :=
  structured.bind (LeanModels.Clang.QualType.resolveTypedefs
      (fun handle => layout.structuredType { value := handle.value }) 32)
    |>.bind (fun type => objectSizeOfStructured type
      (fun handle => layout.recordSizeDecl { value := handle.value }))
    |>.orElse (fun _ => layout.sizeAt decl ty)


/-- Resolve the byte size needed by an expression load through the
declaration identity carried by that expression before consulting the
legacy type-keyed layout table. -/
def Layout.exprSizeAt (layout : Layout) (expression : Expr) (ty : String) :
    Option Nat :=
  let indexedElementSize := match expression with
    | .index base _ _ _ _ =>
        base.structuredType?.bind fun q =>
          match q.unqualified with
          | .array element _ | .pointer element =>
              match element.unqualified with
              | .record handle => layout.recordSizeDecl { value := handle.value }
              | _ => scalarSizeOfStructured element
          | _ => none
    | _ => none
  let nodeRecordSize := expression.structuredType?.bind fun q =>
    match q.unqualified with
    | .record handle => layout.recordSizeDecl { value := handle.value }
    | _ => none
  (nodeRecordSize.orElse (fun _ => indexedElementSize)).orElse (fun _ =>
    ((directDeclId expression).bind layout.structuredType |>.orElse
      (fun _ => (Expr.span expression).offset.bind (fun offset =>
        (layout.structuredExprTypeAt offset (Expr.span expression).endOffset
          expression.kindName ty).orElse (fun _ => layout.structuredExprType offset))))
      |>.bind (fun type => objectSizeOfStructured type) |>.orElse
      (fun _ => layout.sizeAt (directDeclId expression) ty))

/-- C23 §6.5.3.2p2 and §6.5.7p8 use the operand's element type. A cast can
change that type while preserving the underlying object declaration. -/
def Layout.structuredStride (layout : Layout) (type : LeanModels.Clang.QualType) :
    Option Nat := do
  let resolved := (type.resolveTypedefs
    (fun handle => layout.structuredType { value := handle.value }) 32).getD type
  let element ← match resolved.unqualified with
    | .array element _ | .pointer element => some element
    | _ => none
  objectSizeOfStructured element (fun handle => layout.recordSizeDecl { value := handle.value })

/-- Resolve the stride at the subscript's base expression. -/
def Layout.elementSizeAt (layout : Layout) (base : Expr) (ty : String) :
    Option Nat :=
  match base.structuredType? with
  | some type => layout.structuredStride type
  | none =>
      (directDeclId base).bind (fun did =>
          (layout.elementSizeDecl did).orElse (fun _ => layout.pointeeSizeDecl did))
        |>.orElse (fun _ =>
          ((directDeclId base).bind layout.structuredType |>.orElse
            (fun _ => (Expr.span base).offset.bind (fun offset =>
              (layout.structuredExprTypeAt offset (Expr.span base).endOffset base.kindName ty).orElse
                (fun _ => layout.structuredExprType offset)))).bind layout.structuredStride)

def Layout.arrayElementSizeDeclAt (layout : Layout) (decl : Option DeclarationId)
    (arrayTy elementTy : String) : Option Nat :=
  match decl.bind layout.structuredType |>.map LeanModels.Clang.QualType.unqualified with
  | some (.array element _) =>
      let resolvedElement :=
        LeanModels.Clang.QualType.resolveTypedefs
          (fun handle => layout.structuredType { value := handle.value })
          32 element |>.getD element
      decl.bind layout.elementSizeDecl |>.orElse
        (fun _ => objectSizeOfStructured resolvedElement)
  | some _ => none
  | none => none

def Layout.structuredTypeDecl (layout : Layout) (id : DeclarationId) :
    Option LeanModels.Clang.QualType :=
  (layout.structuredType id).bind (LeanModels.Clang.QualType.resolveTypedefs
    (fun declaration => layout.structuredType { value := declaration.value }) 32)

def Layout.structuredTypeAt (layout : Layout) (base : Expr) :
    Option LeanModels.Clang.QualType :=
  match base.structuredType? with
  | some q => some q
  | none =>
      ((Expr.span base).offset.bind (fun offset =>
        (layout.structuredExprTypeAt offset (Expr.span base).endOffset base.kindName base.ty).orElse
          (fun _ => layout.structuredExprType offset))).orElse (fun _ =>
        (directDeclId base).bind layout.structuredTypeDecl)

def Layout.fieldBitsAtResolved (layout : Layout) (base : Expr) (field : String) :
    Option (Nat × Nat) :=
  match layout.structuredTypeAt base with
  | some type => do
      let resolved ← type.resolveTypedefs
        (fun handle => layout.structuredType { value := handle.value }) 32
      match (resolved.pointee.getD resolved).unqualified with
      | .record handle => layout.fieldBitsDecl { value := handle.value } field
      | _ => none
  | none => layout.fieldBitsAt base field

def Layout.bitFieldOf (layout : Layout) : Expr → Option (Nat × Nat)
  | .paren sub .. => layout.bitFieldOf sub
  | .implicitCast _ sub .. | .cast _ sub .. => layout.bitFieldOf sub
  | .member base field .. => layout.fieldBitsAtResolved base field
  | _ => none

/-- Resolve an aggregate's element extent from its declaration's structured
array type before using the legacy spelling-derived element table.  The
element spelling remains the table's existing key, while the parser owns the
array shape and extent. -/
def Layout.elemDeclAt (layout : Layout) (decl : Option DeclarationId)
    (ty : String) : Option (String × Nat) :=
  match decl.bind layout.structuredTypeDecl with
  | some structured =>
      match structured.unqualified with
      | .array _ (some extent) => some (ty, extent)
      | .array _ none | _ => none
  | none => none

/-- Resolve aggregate member order from parser-native object declaration identity. -/
def Layout.membersDeclAt (layout : Layout) (decl : Option DeclarationId)
    (ty : String) : Option (List (String × String)) :=
    decl.bind layout.membersDecl

/-- Resolve a nested record's declaration identity from the parent object and
field name. Missing identity remains an explicit absence. -/
def Layout.memberRecordDeclAt (layout : Layout) (decl : Option DeclarationId)
    (field : String) : Option DeclarationId :=
  decl.bind (fun did => layout.memberRecordDecl did field)

/-- Resolve union classification from parser-native object declaration identity. -/
def Layout.isUnionDeclAt (layout : Layout) (decl : Option DeclarationId)
    (ty : String) : Bool :=
  match decl with
  | some did => layout.isUnionDecl did
  | none => false


/-- Effective-type metadata for a declaration allocation.  Parser-native
aggregate observations suppress the scalar declaration type, while legacy
layouts use their member and element tables for the same decision. -/
def Layout.storageTypeAt (layout : Layout) (decl : Option DeclarationId)
    (ty : String) : Option String :=
  match decl.bind layout.structuredTypeDecl with
  | some structured => if structured.aggregateObject then none else some ty
  | none => none

/-- Resolve a pointer stride at the pointer operand. -/
def Layout.pointeeSizeAt (layout : Layout) (base : Option Expr) (ty : String) :
    Option Nat :=
  base.bind fun expression => layout.elementSizeAt expression ty

/-- A layout that knows nothing: every query refuses. The DEFAULT, so a
missing layout fact is a loud refusal rather than a guessed offset. -/
def Layout.unknown : Layout :=
  { declSize := fun _ => none, fieldOffTypeDecl := fun _ _ => none
    pointeeSizeDecl := fun _ => none
    elementSizeDecl := fun _ => none
    fieldSizeDecl := fun _ _ => none
    fieldStructuredDecl := fun _ _ => none
    fieldOffDecl := fun _ _ => none
    fieldBitsDecl := fun _ _ => none
    flexibleFieldDecl := fun _ _ => false
    membersDecl := fun _ => none
    memberRecordDecl := fun _ _ => none, isUnionDecl := fun _ => false }

/-! ## The evaluation context

Read-only for the whole of an expression: an expression cannot change
which names are in scope, what a struct's layout is, or what a call
means. Bundled so the five mutually recursive functions below take one
parameter instead of four. -/

/-- Everything an expression evaluation reads but never writes. -/
structure Ctx where
  env : Env
  /-- Declaration-identity bindings for real extracted references. -/
  idEnv : IdEnv := []
  /-- Enumeration constants, folded to integers by the ingester
  (`docs/c-envelope-schema.md` §3.1). Measured: 11 in the corpus. -/
  enums : List (String × Int) := []
  enumIds : List (DeclarationId × Int) := []
  layout : Layout := Layout.unknown
  call : CallHandler := noCalls
  /-- Conservative effect summary for direct calls. `false` means the
  callee may write and must stay in the indeterminate-order refusal path. -/
  callPure : Expr → Bool := fun _ => false
  /-- PNVI-ae-udi address exposure hooks.  The default instance is the
  deterministic placement used by the current C runner; a Rust or fully
  quantified memory instance can replace both functions without changing
  expression semantics. -/
  pointerToInteger : Ptr → Int := Ptr.exposedAddress
  integerToPointer : Int → Option Ptr := Ptr.fromExposedAddress
  /-- Language-specific aliasing rule layered over the shared object store. -/
  aliasModel : Mem.AliasModel := Mem.cAliasModel
  /-- The current function's parser-native statement list.  A `goto` may
  jump backward to a label in this same function (§6.8.6.1); carrying the
  already-ingested list lets statement execution resume at that label
  without rebuilding a control-flow graph or parsing source text. -/
  functionBody : Option (List Stmt) := none
  /-- Direct uninitialized scalar declarations eligible for C23 §6.3.2.1p2. -/
  uninitializedRegisterCandidate : DeclarationId → Bool := fun _ => false
  /-- Parser-owned identity for the hosted `stdout` stream object. -/
  stdoutObj : Option ObjId := none
  /-- Statement-layer aggregate initialization for compound literals. -/
  compoundInit : Nat → Env → IdEnv → Layout → Ptr → String → Expr → EvalM Unit :=
    fun _ _ _ _ _ _ _ => refuseUnsupported "compound literal initializer callback unavailable"

def isStdoutRef : Expr → Bool
  | .declRef _ "stdout" _ _ _ .. => true
  | _ => false

/-! ## §6.5.14p3 — scalar truth

`&&`, `||`, `!` and every controlling expression ask one question:
does this value compare unequal to 0? A pointer answers it too
(§6.5.10p3: a null pointer constant compares equal to a null pointer),
and `undef` REFUSES rather than guessing. -/

/-- Does this value compare unequal to zero? -/
def truthy (v : CVal) : EvalM Bool :=
  match v with
  | .int _ n => pure (n != 0)
  | .float32 f => pure (!Float32.Model.beq f (Float32.Model.ofBits 0))
  | .float64 f => pure (!Float.Model.beq f (Float.Model.ofBits 0))
  | .ptr p => pure (!p.isNull)
  | .ptrInt _ => refuseUnsupported "pointer-integer value requires an unchanged cast back"
  | .funPtr _ => refuseUnsupported "function pointer used in a Boolean context"
  | .aggregate _ _ => refuseUnsupported "aggregate used as truth value"
  | .undef => refuseUnsupported "undefined value used where an integer is required (C23 6.3.2.1p2)"

@[simp] theorem truthy_renameAddress (resolve : ObjId → Nat) (v : CVal) :
    truthy (CVal.renameAddress resolve v) = truthy v := by
  cases v <;> simp [truthy, CVal.renameAddress]

/-- §6.5.9p3 / §6.5.10p3: a comparison yields `int`, 0 or 1. -/
def ofBool (b : Bool) : CVal := .int IntTy.int_ (if b then 1 else 0)

@[simp] theorem CVal.renameAddress_ofBool (resolve : ObjId → Nat) (b : Bool) :
    CVal.renameAddress resolve (ofBool b) = ofBool b := by
  simp [ofBool, CVal.renameAddress]

/-! ## §6.5.6-§6.5.13 — the binary arithmetic rules

The operands arrive ALREADY CONVERTED. Measured: of 563 arithmetic and
comparison sites, **542 have operand types that resolve equal** and the
21 that differ are 19 typedef-spelling aliases plus 2 pointer arithmetic
— so clang's implicit `IntegralCast` nodes have already performed
§6.3.1.8's usual arithmetic conversions and the tier reads a promotion
off rather than re-deriving one.

Shifts are counted apart on purpose: §6.5.8p3 promotes each operand
SEPARATELY and the result type is the left operand's, so a shift's
operands legitimately differ (measured: 17 sites, all `uint64_t << int`
or `int << int`). -/

/-- Apply an integer binary operator, at the type the frontend assigned.
Every arm is `Value.lean`'s, so the wrap/refuse split and its J.2 indices
are inherited rather than restated. -/
def evalCRes (r : CRes CVal) : EvalM CVal :=
  match r with
  | .ok v => pure v
  | .ub u => refuseValue u

theorem evalCRes_renameAddress (resolve : ObjId → Nat) (r : CRes CVal) :
    CVal.renameAddress resolve <$> evalCRes r =
      evalCRes (CRes.renameAddress resolve r) := by
  funext m
  cases r <;> rfl

def intBinop (op : String) (t : IntTy) (a b : Int) : EvalM CVal :=
  match op with
  | "+" => evalCRes (addOp t a b)
  | "-" => evalCRes (subOp t a b)
  | "*" => evalCRes (mulOp t a b)
  | "/" => evalCRes (divOp t a b)
  | "%" => evalCRes (modOp t a b)
  | "<<" => evalCRes (shlOp t a b)
  | ">>" => evalCRes (shrOp t a b)
  -- §6.5.11-§6.5.13: bitwise AND/XOR/OR. Both operands are already at `t`,
  -- and the result is in range by construction, so no arm can overflow.
  | "&" => pure (.int t (bitAnd t a b))
  | "|" => pure (.int t (bitOr t a b))
  | "^" => pure (.int t (bitXor t a b))
  -- §6.5.9p3 / §6.5.10p3: relational and equality yield `int`.
  | "<" => pure (ofBool (a < b))
  | ">" => pure (ofBool (a > b))
  | "<=" => pure (ofBool (a ≤ b))
  | ">=" => pure (ofBool (a ≥ b))
  | "==" => pure (ofBool (a == b))
  | "!=" => pure (ofBool (a != b))
  | _ => refuseUnsupported s!"binary operator '{op}'"

/-! IEEE binary arithmetic. The profile registers binary32 and binary64
round-to-nearest-even through the shared SoftFloat transfer layer. The pinned
GNU17 target follows Annex F, so floating division by zero is defined by the
IEEE result. Integer division keeps its separate C undefined-behavior rule. -/

def float32Binop (op : String) (a b : Float32.Model) : EvalM CVal :=
  match op with
  | "+" => pure (.float32 (a + b))
  | "-" => pure (.float32 (a - b))
  | "*" => pure (.float32 (a * b))
  | "/" => pure (.float32 (a / b))
  | "==" => pure (ofBool (Float32.Model.beq a b))
  | "!=" => pure (ofBool (!Float32.Model.beq a b))
  | "<" => pure (ofBool (Float32.Model.lt a b))
  | ">" => pure (ofBool (Float32.Model.lt b a))
  | "<=" => pure (ofBool (Float32.Model.le a b))
  | ">=" => pure (ofBool (Float32.Model.le b a))
  | _ => refuseUnsupported s!"binary operator '{op}' on binary32"

def float64Binop (op : String) (a b : Float.Model) : EvalM CVal :=
  match op with
  | "+" => pure (.float64 (a + b))
  | "-" => pure (.float64 (a - b))
  | "*" => pure (.float64 (a * b))
  | "/" => pure (.float64 (a / b))
  | "==" => pure (ofBool (Float.Model.beq a b))
  | "!=" => pure (ofBool (!Float.Model.beq a b))
  | "<" => pure (ofBool (Float.Model.lt a b))
  | ">" => pure (ofBool (Float.Model.lt b a))
  | "<=" => pure (ofBool (Float.Model.le a b))
  | ">=" => pure (ofBool (Float.Model.le b a))
  | _ => refuseUnsupported s!"binary operator '{op}' on binary64"

/-! C23 §6.3.1.5: binary32/binary64 conversions use the exact IEEE value
and round to the destination format.  The shared `UnpackedFloat.round`
operation performs round-to-nearest-even; widening is exact because the same
operation is used with the wider format.  NaN, infinities and signed zero
retain their special value and sign. -/

def floatCast (v : CVal) (structured : Option LeanModels.Clang.QualType) : EvalM CVal :=
  let roundTo (spec : Float.Model.Format) (u : Float.Model.UnpackedFloat) :
      Float.Model.UnpackedFloat :=
    match u with
    | .infinity s => .infinity s
    | .notANumber => .notANumber
    | .zero s => .zero s
    | .finite s m e h => .round spec s m e
  match v, structured.bind floatBitsOfStructured with
  | .float32 f, some 64 =>
      pure (.float64 (Float.Model.pack (roundTo Float.Model.Format.binary64
        (Float32.Model.unpack f))))
  | .float64 f, some 32 =>
      pure (.float32 (Float32.Model.pack (roundTo Float.Model.Format.binary32
        (Float.Model.unpack f))))
  | _, _ => refuseUnsupported "floating cast has incompatible source and destination"

@[simp] theorem floatCast_renameAddress (resolve : ObjId → Nat) (v : CVal)
    (structured : Option LeanModels.Clang.QualType) :
    floatCast (CVal.renameAddress resolve v) structured = floatCast v structured := by
  cases v <;> simp [floatCast, CVal.renameAddress]

/-! C23 §6.3.1.4: conversion from a floating type to an integer type
discards the fractional part toward zero. An infinite/NaN source, or an
integral part outside the destination range, is undefined (`J.2(16)`).
The exact source value comes from the parser-backed IEEE representation;
there is no host floating-point conversion here. -/

def float32ToInt (f : Float32.Model) (t : IntTy) : EvalM CVal :=
  match LeanModels.SoftFloat.valQ (Float32.Model.unpack f) with
  | some q =>
      let n := q.truncate
      if t.inRange n then pure (.int t n)
      else refuseValue (.floatingToIntegralOutOfRange t)
  | none => refuseValue (.floatingToIntegralOutOfRange t)

@[simp] theorem float32ToInt_renameAddress (resolve : ObjId → Nat)
    (f : Float32.Model) (t : IntTy) :
    CVal.renameAddress resolve <$> float32ToInt f t = float32ToInt f t := by
  funext m
  simp only [float32ToInt]
  cases hq : LeanModels.SoftFloat.valQ (Float32.Model.unpack f) with
  | none => simp [hq, CVal.renameAddress, map_eq_pure_bind, SemMWith.run_bind,
      SemMWith.run_pure, SemMWith.run_throw, refuseValue]
  | some q =>
      simp only [hq]
      split <;> simp [CVal.renameAddress, map_eq_pure_bind, SemMWith.run_bind,
        SemMWith.run_pure, SemMWith.run_throw, refuseValue]

def float64ToInt (f : Float.Model) (t : IntTy) : EvalM CVal :=
  match LeanModels.SoftFloat.valQ (Float.Model.unpack f) with
  | some q =>
      let n := q.truncate
      if t.inRange n then pure (.int t n)
      else refuseValue (.floatingToIntegralOutOfRange t)
  | none => refuseValue (.floatingToIntegralOutOfRange t)

@[simp] theorem float64ToInt_renameAddress (resolve : ObjId → Nat)
    (f : Float.Model) (t : IntTy) :
    CVal.renameAddress resolve <$> float64ToInt f t = float64ToInt f t := by
  funext m
  simp only [float64ToInt]
  cases hq : LeanModels.SoftFloat.valQ (Float.Model.unpack f) with
  | none => simp [hq, CVal.renameAddress, map_eq_pure_bind, SemMWith.run_bind,
      SemMWith.run_pure, SemMWith.run_throw, refuseValue]
  | some q =>
      simp only [hq]
      split <;> simp [CVal.renameAddress, map_eq_pure_bind, SemMWith.run_bind,
        SemMWith.run_pure, SemMWith.run_throw, refuseValue]

/-! C23 §6.3.1.8 gives a compound assignment the computation type recorded
by Clang.  In particular, an integer lvalue and a floating right operand are
computed in the floating type, and a `float` lvalue may be computed in
`double`.  Keep these conversions on the node's parser-native QualType so
the mixed cases do not invent a type from a spelling. -/

def asFloat64ForCompound : CVal → Option Float.Model
  | .float64 f => some f
  | .float32 f => some (Float.Model.pack (Float32.Model.unpack f))
  | .int _ n => some (Float.Model.ofInt n)
  | _ => none

def asFloat32ForCompound : CVal → Option Float32.Model
  | .float32 f => some f
  | .float64 f => some (Float32.Model.pack (Float.Model.unpack f))
  | .int _ n => some (Float32.Model.ofInt n)
  | _ => none

def compoundFloatResult (op : String) (resultBits : Nat) (lhs rhs : CVal) : EvalM CVal :=
  if resultBits == 32 then
    match asFloat32ForCompound lhs, asFloat32ForCompound rhs with
    | some a, some b => float32Binop op a b
    | _, _ => refuseUnsupported "compound assignment has a non-floating computation operand"
  else if resultBits == 64 then
    match asFloat64ForCompound lhs, asFloat64ForCompound rhs with
    | some a, some b => float64Binop op a b
    | _, _ => refuseUnsupported "compound assignment has a non-floating computation operand"
  else
    refuseUnsupported "compound assignment has an unsupported floating computation type"

def convertCompoundResult (value : CVal)
    (target : Option LeanModels.Clang.QualType) : EvalM CVal :=
  match target.bind intTyOfStructured with
  | some t =>
      match value with
      | .float32 f => float32ToInt f t
      | .float64 f => float64ToInt f t
      | _ => refuseUnsupported "compound assignment result is not floating"
  | none =>
      match target.bind floatBitsOfStructured, value with
      | some 32, .float64 _ => floatCast value target
      | some 32, .float32 _ => pure value
      | some 64, .float32 _ => floatCast value target
      | some 64, .float64 _ => pure value
      | _, _ => refuseUnsupported "compound assignment lacks parser-native storage type"


/-! ### Projecting a value

Named, because every refusal must be. -/

/-- Require a pointer. `undef` and an integer both refuse. -/
def asPtr (v : CVal) : EvalM Ptr :=
  match v with
  | .ptr p => pure p
  | .ptrInt _ => refuseUnsupported "pointer-integer value requires an unchanged cast back"
  | .funPtr _ => refuseUnsupported "function pointer used as an object pointer"
  | .int _ _ => refuseUnsupported "integer used as a pointer (no int↔ptr cast in tier)"
  | .float32 _ | .float64 _ => refuseUnsupported "floating value used as a pointer"
  | .aggregate _ _ => refuseUnsupported "aggregate used as a pointer"
  | .undef => refuseUnsupported "undefined value used as a truth value (C23 6.3.2.1p2)"

theorem asPtr_renameAddress (resolve : ObjId → Nat) (v : CVal) :
    asPtr (CVal.renameAddress resolve v) =
      (fun p => Ptr.renameAddress resolve p) <$> asPtr v := by
  funext m
  cases v <;>
    simp [asPtr, CVal.renameAddress, map_eq_pure_bind, SemMWith.run_bind,
      SemMWith.run_pure, refuseUnsupported]

/-- Require an integer, with its type. -/
def asInt (v : CVal) : EvalM (IntTy × Int) :=
  match v with
  | .int t n => pure (t, n)
  | .ptr _ => refuseUnsupported "pointer used as an integer (no ptr↔int cast in tier)"
  | .ptrInt _ => refuseUnsupported "pointer-integer value requires an unchanged cast back"
  | .funPtr _ => refuseUnsupported "function pointer used as an integer"
  | .float32 _ | .float64 _ => refuseUnsupported "floating value used as an integer"
  | .aggregate _ _ => refuseUnsupported "aggregate used as an integer"
  | .undef => refuseUnsupported "undefined value used as a pointer (C23 6.3.2.1p2)"

@[simp] theorem asInt_renameAddress (resolve : ObjId → Nat) (v : CVal) :
    asInt (CVal.renameAddress resolve v) = asInt v := by
  cases v <;> simp [asInt, CVal.renameAddress]

/-- Parser-native pointer-object classification. -/
def pointerTypeOfNode (structured : Option LeanModels.Clang.QualType) : Bool :=
  structured.map (fun type => type.unqualified.pointerObject) |>.getD false

/-! Parser-native type decisions. Missing observations remain a refusal. -/
def structuredPointerObject (structured : Option LeanModels.Clang.QualType)
    (fallback : String) : Bool :=
  pointerTypeOfNode structured

def structuredIndexable (structured : Option LeanModels.Clang.QualType)
    (fallback : String) : Bool :=
  structured.map (fun type => type.unqualified.indexable) |>.getD false

def pointerIntegerTypeOfNode (structured : Option LeanModels.Clang.QualType) : Bool :=
  -- The pinned profile has 64-bit object pointers.  A 64-bit integer type
  -- can represent every exposed address produced by this memory model, so
  -- C23's pointer/integer conversion boundary includes the profile's long
  -- and long-long spellings as well as the exact-width typedefs.
  match structured.bind intTyOfStructured with
    | some it => it.bits >= 64
    | none => false

private def signedCounterpart : LeanModels.Clang.CBuiltin → Option LeanModels.Clang.CBuiltin
  | .unsignedChar => some .signedChar
  | .unsignedShort => some .short
  | .unsignedInt => some .int
  | .unsignedLong => some .long
  | .unsignedLongLong => some .longLong
  | .uint128 => some .int128
  | _ => none

private def canonicalCallType (layout : Layout) (type : Option LeanModels.Clang.QualType) :
    Option LeanModels.Clang.QualType :=
  type.bind (LeanModels.Clang.QualType.resolveTypedefs
    (fun handle => layout.structuredType { value := handle.value }) 32)

/-- N3220 §7.16.1.1p2 compares the requested type with the type of the
next argument after default argument promotions. Equal representation
widths do not establish type compatibility. -/
def checkVaType (layout : Layout) (requested : Option LeanModels.Clang.QualType)
    (argument : CallArgument) : EvalM CVal := do
  let some expected := canonicalCallType layout requested
    | refuseUnsupported "va_arg requested type lacks canonical QualType"
  let some actual := canonicalCallType layout argument.promotedType
    | refuseUnsupported "va_arg argument lacks canonical promoted QualType"
  let expected := expected.unqualified
  let actual := actual.unqualified
  match argument.value with
  | .undef | .ptrInt _ => refuseUnsupported "va_arg argument representation is unavailable"
  | _ =>
    if expected == actual then
      return argument.value
    match expected, actual, argument.value with
    | .cBuiltinKind e, .cBuiltinKind a, .int _ n =>
      if signedCounterpart e == some a || signedCounterpart a == some e then
        match intTyOfStructured expected, intTyOfStructured actual with
        | some target, some source =>
          if target.inRange n && source.inRange n then
            pure (.int target n)
          else refuseUnsupported "va_arg value is outside the corresponding integer type"
        | _, _ => refuseUnsupported "va_arg integer representation is unavailable"
      else refuseUnsupported "va_arg incompatible argument type"
    | .pointer e, .pointer a, _ =>
      let e := e.unqualified
      let a := a.unqualified
      if e == a || (e == .void && Mem.isCharacterType a) ||
          (a == .void && Mem.isCharacterType e) then
        pure argument.value
      else refuseUnsupported "va_arg incompatible pointer argument type"
    | _, _, _ => refuseUnsupported "va_arg incompatible argument type"

/-- C23 §6.3.2.3p7 / §6.5.15p6: pointers to compatible integer types
may carry the same object provenance. The legacy envelope has no structured
target type at a cast occurrence, so only the exact parser spelling or the
standard character/void exceptions are admitted here. Incompatible legacy
spellings refuse instead of being peeled by a local type parser. -/
def compatiblePointerTypesNode
    (a b : Option LeanModels.Clang.QualType) : Bool :=
  let compatibleBuiltin := fun left right =>
    left == right ||
      match left, right with
      | .unsignedChar, .signedChar | .signedChar, .unsignedChar
      | .unsignedShort, .short | .short, .unsignedShort
      | .unsignedInt, .int | .int, .unsignedInt
      | .unsignedLong, .long | .long, .unsignedLong
      | .unsignedLongLong, .longLong | .longLong, .unsignedLongLong
      | .uint128, .int128 | .int128, .uint128 => true
      | _, _ => false
  let compatiblePointee := fun left right =>
    match left.unqualified, right.unqualified with
    | .cBuiltinKind left, .cBuiltinKind right => compatibleBuiltin left right
    | .builtin left, .builtin right =>
        left == right ||
          LeanModels.Cpp.CppIntType.unsignedCounterpart left == some right ||
          LeanModels.Cpp.CppIntType.signedCounterpart left == some right
    | _, _ => left.unqualified == right.unqualified
  match a, b with
  | some (.pointer left), some (.pointer right) => compatiblePointee left right
  | _, _ => false

def loadPtrIntOrInt (m : Mem) (alias : Mem.AliasModel) (p : Ptr)
    (t : IntTy) (ty : String)
    (structured : Option LeanModels.Clang.QualType := none) : MRes CVal :=
  match Mem.loadPtrInt m p with
  | .ok q => .ok (.ptrInt q)
  | .error _ => Mem.loadIntChecked m alias p t ty structured

/-- C23 §6.5.1p7 permits reading pointer representations through a character
lvalue. The current store lacks a placement oracle for non-null addresses
and a byte representation for function pointers. -/
def loadCharacterAt (p : Ptr) (t : IntTy)
    (couldBeUninitializedRegister : Unit → Bool := fun _ => false) : EvalM CVal := do
  let (_, object, offset) ← readMem (fun m => m.resolve p 1)
  match object.bytes[offset]? with
  | some (.funByte _) =>
      refuseUnsupported "function pointer byte representation is unavailable"
  | some (.ptrByte pointer _) | some (.ptrIntByte pointer _) =>
      if pointer.isNull then readMem (fun m => m.loadCharacter p t) couldBeUninitializedRegister
      else refuseUnsupported "pointer byte read requires an address placement oracle"
  | _ => readMem (fun m => m.loadCharacter p t) couldBeUninitializedRegister

/-- Load whatever an lvalue of this type holds — an integer or a pointer.
§6.3.2.1p2, the lvalue conversion: **1837 sites, the load-bearing
implicit of the whole corpus.** -/
def loadAt (alias : Mem.AliasModel) (p : Ptr) (ty : String) (size : Option Nat)
    (structured : Option LeanModels.Clang.QualType := none)
    (zeroNullPointer : Bool := false)
    (couldBeUninitializedRegister : Unit → Bool := fun _ => false) : EvalM CVal :=
  if structured.bind floatBitsOfStructured == some 32 then
    readMem (fun m => Mem.loadFloat32 m p) couldBeUninitializedRegister
  else if structured.bind floatBitsOfStructured == some 64 then
    readMem (fun m => Mem.loadFloat64 m p) couldBeUninitializedRegister
  else if structured.bind intTyOfStructured |>.map (fun t => t.bits == 8) |>.getD false then
    match structured.bind intTyOfStructured with
    | some t => loadCharacterAt p t couldBeUninitializedRegister
    | none => refuseUnsupported s!"character type '{ty}' has no integer representation"
  else if structuredPointerObject structured ty then do
    let q ← readMem (fun m => do
      let (o, c, off) ← m.resolve p 8
      Mem.checkEffectiveAt m alias o c off ty structured
      m.loadPtr p zeroNullPointer) couldBeUninitializedRegister
    match q with
    | some q => pure (.ptr q)
    | none => refuseUnsupported "pointer representation lacks provenance or target ABI evidence"
  else do
    match structured.bind intTyOfStructured with
    | some t =>
        if pointerIntegerTypeOfNode structured then
          -- A uintptr_t object may contain the profile's preserved pointer
          -- token or an ordinary integer.  Try the parser-native pointer
          -- representation first, then use the ordinary integer rule.
          readMem (fun m => loadPtrIntOrInt m alias p t ty structured) couldBeUninitializedRegister
        else
          readMem (fun m => Mem.loadIntChecked m alias p t ty structured) couldBeUninitializedRegister
    | none =>
        match size with
        | some n => do
            let bs ← readMem (fun m => Mem.loadBytes m p n)
            pure (.aggregate ty bs)
        | none => refuseUnsupported s!"aggregate load without a layout '{ty}'"

private def directVariable : Expr → Option DeclarationId
  | .declRef id _ "VarDecl" .. => id
  | .paren sub .. => directVariable sub
  | _ => none

abbrev Ctx.loadAt (ctx : Ctx) (p : Ptr) (ty : String) (size : Option Nat)
    (structured : Option LeanModels.Clang.QualType := none)
    (lvalue : Option Expr := none) : EvalM CVal :=
  LeanModels.C.C23.loadAt ctx.aliasModel p ty size structured ctx.layout.zeroNullPointer
    (fun _ => (lvalue.bind directVariable).any ctx.uninitializedRegisterCandidate)

/-- Store a value at an address, at the lvalue's type. -/
def storeAt (alias : Mem.AliasModel) (p : Ptr) (ty : String) (v : CVal)
    (structured : Option LeanModels.Clang.QualType := none) : EvalM Unit :=
  match v with
  | .funPtr id => writeMem (fun m => do
      let (o, c, off) ← m.resolve p 8
      Mem.checkEffectiveAt m alias o c off ty structured
      m.storeFunction p id)
  | .ptr q => writeMem (fun m => do
      let (o, c, off) ← m.resolve p 8
      Mem.checkEffectiveAt m alias o c off ty structured
      m.storePtr p q)
  | .ptrInt q =>
      if pointerIntegerTypeOfNode structured then writeMem (fun m => Mem.storePtrInt m p q)
      else refuseUnsupported "pointer-integer value stored outside uintptr_t/intptr_t"
  | .int _ n => do
      let t ← match structured.bind intTyOfStructured with
        | some projected => pure projected
        | none => refuseUnsupported "integer store lacks parser-native QualType"
      writeMem (fun m => Mem.storeIntChecked m alias p t ty n structured)
  | .float32 f => if structured.bind floatBitsOfStructured == some 32 then writeMem (fun m => Mem.storeFloat32 m p f)
                 else refuseUnsupported "floating store without a floating layout"
  | .float64 f => if structured.bind floatBitsOfStructured == some 64 then writeMem (fun m => Mem.storeFloat64 m p f)
                 else refuseUnsupported "floating store without a floating layout"
  | .aggregate _ bs => writeMem (fun m => Mem.storeBytes m p bs)
  | .undef => refuseUnsupported "storing an indeterminate value"

/-- Peel the conversions clang wraps a callee in and read its name.
`none` is an INDIRECT call — measured 19, every one through `movecb`. -/
def calleeName : Expr → Option String
  | .implicitCast _ s _ _ .. => calleeName s
  | .cast _ s _ _ .. => calleeName s
  | .paren s _ _ .. => calleeName s
  | .declRef _ n "FunctionDecl" _ _ .. => some n
  | _ => none

def calleeId : Expr → Option DeclarationId
  | .implicitCast _ s _ _ .. => calleeId s
  | .cast _ s _ _ .. => calleeId s
  | .paren s _ _ .. => calleeId s
  | .declRef (some id) _ "FunctionDecl" _ _ .. => some id
  | _ => none

def functionPointerBitCast : Expr → Bool
  | .paren s _ _ .. => functionPointerBitCast s
  | .cast "BitCast" .. =>
      -- A call target's recursive QualType observation is not attached to
      -- this cast node in the c-0.1 envelope.  Refuse the whole BitCast call
      -- class until that parser fact is available rather than classifying the
      -- target by searching clang's display spelling.
      true
  | _ => false

/-! ## §6.5 — the evaluator

Two mutually recursive functions and one list helper, all STRUCTURALLY
recursive on `Expr` (module docstring: this layer is fuel-free).

`evalLValue` yields the ADDRESS an expression designates; `evalExpr`
yields its VALUE. The census says the first has exactly five shapes. -/

/-- The arithmetic operator inside a compound assignment.

TABLED, not derived by dropping the `=`: the census says the corpus uses
exactly five (`+=` 10, `|=` 6, `^=` 3, `-=` 3, `*=` 2), and a table
refuses an unmeasured spelling where string surgery would quietly accept
one. The empty string is not an operator, so an unlisted spelling reaches
`evalArith`'s own refusal. -/
def compoundBase : String → String
  | "+=" => "+" | "-=" => "-" | "*=" => "*" | "/=" => "/" | "%=" => "%"
  | "&=" => "&" | "|=" => "|" | "^=" => "^"
  | "<<=" => "<<" | ">>=" => ">>"
  | _ => ""

/-! Clang's JSON records an ordinary high-bit character constant as the
32-bit unsigned representation of its signed `char` value (for example
`'\\xff'` is `4294967295`). C's ordinary character constant is an `int`
whose value is the execution-character value, so recover the profile's
signed 8-bit byte before constructing the value. Multi-character constants
remain below the sign-extension marker and retain Clang's folded value. -/
def charLiteralValue (n : Int) : Int :=
  if n >= (2 : Int) ^ 31 then
    let b := n % 256
    if b >= 128 then b - 256 else b
  else n

def chooseCond : Expr → Option Bool
  | .constExpr value _ _ _ .. =>
      match value.toInt? with
      | some n => some (n != 0)
      | none => none
  | .paren sub _ _ .. => chooseCond sub
  | _ => none

/-- The non-short-circuit binary rules, once both operands have values. -/
def evalArith (ctx : Ctx) (op : String) (lv rv : CVal) (ty : String)
    (elemTy : Option String := none) (base : Option Expr := none)
    (structured : Option LeanModels.Clang.QualType := none) : EvalM CVal :=
  match lv, rv with
  | .float32 a, .float32 b => float32Binop op a b
  | .float64 a, .float64 b => float64Binop op a b
  -- §6.5.7p8 — pointer + integer, and it is the pointer rule that applies
  -- whenever either operand is one. Measured: 8 `+`, 4 `-`.
  | .ptr p, .int _ i =>
      if op == "+" || op == "-" then
        let stride := (ctx.layout.pointeeSizeAt base ty).orElse (fun _ =>
          base.bind (fun expression => (ctx.layout.structuredTypeAt expression).bind fun q =>
            match q.unqualified with
            | .pointer pointee => if pointee.unqualified == .void then some 1 else none
            | _ => none))
        match stride with
        | some esz => do
            let d := if op == "+" then i else -i
            let q ← readMem (fun m => Mem.offsetPtr m p esz d)
            pure (.ptr q)
        | none => refuseUnsupported s!"no size for pointee of '{ty}'"
      else refuseUnsupported s!"operator '{op}' on a pointer and an integer"
  | .int _ i, .ptr p =>
      if op == "+" then
        let stride := (ctx.layout.pointeeSizeAt base ty).orElse (fun _ =>
          base.bind (fun expression => (ctx.layout.structuredTypeAt expression).bind fun q =>
            match q.unqualified with
            | .pointer pointee => if pointee.unqualified == .void then some 1 else none
            | _ => none))
        match stride with
        | some esz => do
            let q ← readMem (fun m => Mem.offsetPtr m p esz i)
            pure (.ptr q)
        | none => refuseUnsupported s!"no size for pointee of '{ty}'"
      else refuseUnsupported s!"operator '{op}' on an integer and a pointer"
  -- §6.5.10p7 vs §6.5.9p6 — the asymmetry: `==`/`!=` across unrelated
  -- objects is DEFINED, `<` and friends are UNDEFINED.
  | .ptr a, .ptr b =>
      if op == "-" then
        -- C23 §6.5.7p9: subtracting pointers is defined only within one
        -- array (including its one-past element), and the byte distance must
        -- be an exact multiple of the element size.  The envelope retains
        -- the object and array-bound provenance; a missing or mismatched
        -- bound is refused rather than treated as a fabricated address.
        match a.obj, b.obj, a.bound, b.bound with
        | some ao, some bo, some ab, some bb =>
            if ao != bo || ab != bb then
              refuseUnsupported "operator '-' on pointers from different arrays"
            else
              match elemTy.bind (ctx.layout.pointeeSizeAt base) with
              | none => refuseUnsupported "operator '-' on pointers with unknown element size"
              | some esz =>
                  if esz == 0 then
                    refuseUnsupported "operator '-' on pointers with zero element size"
                  else
                    let d := a.off - b.off
                    if d % (esz : Int) != 0 then
                      refuseUnsupported "operator '-' on pointers with non-integral element distance"
                    else
                      let q := d / (esz : Int)
                      match structured.bind intTyOfStructured with
                      | none => refuseUnsupported "operator '-' pointer difference lacks parser-native result type"
                      | some rt =>
                          if !rt.inRange q then
                            refuseUnsupported "operator '-' pointer difference is out of range"
                          else pure (.int rt q)
        | _, _, _, _ =>
            refuseUnsupported "operator '-' on pointers without array provenance"
      else if op == "==" || op == "!=" then do
        let boundary ← readMem (fun m => .ok (Mem.ptrEqBoundary m a b))
        if boundary then
          refuseUnsupported "pointer equality at an unspecified adjacent boundary"
        else if op == "==" then pure (ofBool (Mem.ptrEq a b))
        else pure (ofBool (!Mem.ptrEq a b))
      else if op == "<" then do let c ← readMem (fun _ => Mem.ptrLt a b); pure (ofBool c)
      else if op == ">" then do let c ← readMem (fun _ => Mem.ptrLt b a); pure (ofBool c)
      else if op == "<=" then do let c ← readMem (fun _ => Mem.ptrLt b a); pure (ofBool (!c))
      else if op == ">=" then do let c ← readMem (fun _ => Mem.ptrLt a b); pure (ofBool (!c))
      else refuseUnsupported s!"operator '{op}' on two pointers"
  | .ptrInt _, .ptrInt _
  | .ptrInt _, .int _ _
  | .int _ _, .ptrInt _ =>
      refuseUnsupported "pointer-integer value requires an unchanged cast back"
  | .int t a, .int _ b =>
      -- Shifts take the LEFT operand's type (§6.5.8p3); every other
      -- operator has already had both operands converted to a common type.
      if op == "<<" || op == ">>" then intBinop op t a b
      else match structured.bind intTyOfStructured with
        | some rt => intBinop op rt a b
        | none => refuseUnsupported "integer operator lacks parser-native result type"
  | _, _ => refuseUnsupported "operator operands have unsupported value kinds (C23 6.5)"

/-! ## §6.5 — the evaluator

Two mutually recursive functions, both STRUCTURALLY recursive on `Expr`
(module docstring: this layer is fuel-free). `evalLValue` yields the
ADDRESS an expression designates; `evalExpr` yields its VALUE.

Written in the CENSUS's order, not the standard's: the conversion lattice
first (1837 + 405 sites), then the short-circuits whose rule is not
"evaluate both", then everything else. -/

/-! Refuse calls whose indeterminately sequenced arguments can both write.
The check is conservative and happens before either argument runs. -/
def mayWrite (ctx : Ctx) (e : Expr) : Bool :=
  (e.subexprs false).any fun n => match n with
    | .call callee .. =>
        let builtinPure := match calleeName callee with
          | some nm => nm == "__builtin_fabs" || nm == "__builtin_fabsf" ||
              nm == "__builtin_isinf" || nm == "__builtin_isnan" ||
              nm == "__builtin_isfinite" || nm == "__builtin_signbit" ||
              nm == "__builtin_isunordered" ||
              nm == "__builtin_inf" || nm == "__builtin_inff" ||
              nm == "__builtin_huge_val" || nm == "__builtin_huge_valf" ||
              nm == "__builtin_nanf" || nm == "__builtin_nan" ||
              nm == "__builtin_copysign" || nm == "__builtin_copysignf" || nm == "fabs" ||
              nm == "floor" || nm == "floorf" ||
              nm == "__builtin_bswap16" || nm == "__builtin_bswap32" ||
              nm == "__builtin_bswap64" || nm == "__builtin_ffs" ||
              nm.contains "ctz" || nm.contains "clz" || nm.contains "clrsb" ||
              nm.contains "popcount" || nm.contains "parity" ||
              nm == "__builtin_abs" || nm == "abs"
          | none => false
        !ctx.callPure callee && !builtinPure
    | .compoundAssign .. => true
    | .unop op .. => op == "++" || op == "--"
    | _ => false

/-! A postfix update in the right operand is not sequenced before the
assignment store when it targets the assigned object (§6.5.17.1p3). Calls
are deliberately absent: a call's effects complete during the right-hand
evaluation, before the assignment store, so `x = f(y)` is defined even when
`f` writes memory. -/
def lvalueKey : Expr → Option String
  | .declRef (some id) .. => some ("id:" ++ id.value)
  | .declRef none name .. => some ("name:" ++ name)
  | .paren sub .. => lvalueKey sub
  | .implicitCast _ sub .. | .cast _ sub .. => lvalueKey sub
  | .unop op sub .. =>
      if op == "*" then (lvalueKey sub).map ("*" ++ ·)
      else if op == "++" || op == "--" then lvalueKey sub
      else none
  | .member base field .. => (lvalueKey base).map (· ++ "." ++ field)
  | _ => none

def directWriteTargets (e : Expr) : List (Option String) :=
  (e.subexprs false).flatMap fun n => match n with
    | .unop op sub .. =>
        if op == "++" || op == "--" then [lvalueKey sub] else []
    | .compoundAssign _ lhs .. => [lvalueKey lhs]
    | .binop "=" lhs .. => [lvalueKey lhs]
    | _ => []

def readKeys (e : Expr) : List String :=
  (e.subexprs false).flatMap fun n => match n with
    | .declRef (some id) .. => ["id:" ++ id.value]
    | .declRef none name .. => ["name:" ++ name]
    | _ => []

def assignmentHasUnsequencedWrite (lhs rhs : Expr) : Bool :=
  let target := lvalueKey lhs
  let writes := directWriteTargets rhs
  match target with
  | some a => writes.any fun written => written == some a
  | none =>
      -- An indexed/dereferenced lvalue has no single scalar key. Its own
      -- address expression can still carry a key (`a[i++]`), and a RHS
      -- update of that key is unsequenced with the address computation.
      if (directWriteTargets lhs).any (·.isNone) then true
      else writes.any fun written =>
        match written with
        | some b => (readKeys lhs).any (· == b)
        | none => false

def compoundAssignmentHasUnsequencedWrite (lhs rhs : Expr) : Bool :=
  let target := lvalueKey lhs
  let writes := directWriteTargets rhs
  match target with
  | some a => writes.any fun written => written == some a
  | none =>
      if (directWriteTargets lhs).any (·.isNone) then true
      else writes.any fun written =>
        match written with
        | some b => (readKeys lhs).any (· == b)
        | none => false

/-! For an unsequenced operator or a pair of call arguments, a modification
conflicts with a read in the other expression when the same scalar is
involved. Calls do not interleave, so independent argument updates are
defined. An unknown write target conflicts with the other expression's
reads, and a known target conflicts when its key is read or written there.
This is the sufficient refusal condition from §6.5.1p2-3 and J.2 for the
scalar cases represented by the envelope. -/
def writesKeyIn (writes : List (Option String)) (reads : List String) : Bool :=
  writes.any fun written =>
    match written with
    | none => !reads.isEmpty
    | some key => reads.any (· == key)

def writesOverlap (left right : List (Option String)) : Bool :=
  left.any fun a => right.any fun b =>
    match a, b with
    | some x, some y => x == y
    | none, _ | _, none => true

def binaryHasUnsequencedWrite (lhs rhs : Expr) : Bool :=
  let leftWrites := directWriteTargets lhs
  let rightWrites := directWriteTargets rhs
  let leftReads := readKeys lhs
  let rightReads := readKeys rhs
  writesOverlap leftWrites rightWrites ||
    writesKeyIn leftWrites rightReads ||
    writesKeyIn rightWrites leftReads

def hasArgConflict : List Expr → Bool
  | [] => false
  | e :: es => es.any (binaryHasUnsequencedWrite e) || hasArgConflict es

/-! ### C23 §6.7.3.2 — bit-field object representation

Bit-fields share the record's storage bytes.  The offset and width below are
the parser-native `ASTRecordLayout` observations carried by the envelope;
the evaluator performs only the byte/bit extraction required by the clause.
No ABI packing rule is reconstructed here. -/

def bitFieldBytesNat : List CByte → Option Nat
  | bs =>
      if bs.any (fun b => match b with | .conc _ => false | _ => true) then none
      else some (Mem.natOfBytes (bs.map (fun b => match b with | .conc x => x | _ => 0)))

def bitFieldSignedValue (t : IntTy) (width raw : Nat) : Int :=
  let modulus := (2 : Nat) ^ width
  let value := raw % modulus
  if t.signed && width > 0 && value >= (2 : Nat) ^ (width - 1) then
    (value : Int) - (modulus : Int)
  else value

def mergeBitFieldBytes (bs : List CByte) (mask value : Nat) : Option (List CByte) :=
  bs.zipIdx.mapM fun (byte, i) => do
    let factor := 256 ^ i
    let written := mask / factor % 256
    if written == 0 then return byte
    -- A bit-field assignment updates a storage unit.  Bits outside the field
    -- keep their prior value when it is concrete.  If that prior value is
    -- indeterminate, the standard leaves the representation choice open, so
    -- choose zero for the untouched bits and continue.  This is the same
    -- per-byte choice used for padding and partial initialization.
    let original ← match byte with
      | .conc b => some b.toNat
      | _ => some 0
    let result := (original &&& Nat.xor written 255) ||| ((value / factor % 256) &&& written)
    pure (.conc (UInt8.ofNat result))

def bitFieldByteCount (offsetBits width : Nat) : Nat :=
  (offsetBits % 8 + width + 7) / 8

def bitFieldIntTy (structured : Option LeanModels.Clang.QualType) (width : Nat) :
    Option IntTy := do
  let type ← structured
  -- The compatible integer type of an enum is implementation-defined.
  -- A declaration handle alone carries no signedness observation.
  match type.unqualified with
  | .enumeration _ => none
  | _ =>
      let t ← intTyOfStructured type
      if width > 0 && width ≤ t.bits then some t else none

def bitFieldTypeError (structured : Option LeanModels.Clang.QualType)
    (fieldTy : String) (width : Nat) : String :=
  match structured.map LeanModels.Clang.QualType.unqualified with
  | some (.enumeration _) => "enum bit-field lacks parser-native compatible integer type"
  | _ => s!"unsupported bit-field width {width} for '{fieldTy}'"

def bitFieldResidue (t : IntTy) (width : Nat) (n : Int) : Nat :=
  let converted := if t == IntTy.bool_ then (if n == 0 then 0 else 1) else n
  (converted % ((2 : Int) ^ width)).toNat

def loadBitFieldAt (fieldTy : String) (fieldPtr : Ptr) (offsetBits width : Nat)
    (structured : Option LeanModels.Clang.QualType) : EvalM CVal := do
  let storageTy ← match bitFieldIntTy structured width with
    | some t => pure t
    | none => refuseUnsupported (bitFieldTypeError structured fieldTy width)
  let bs ← readMem (fun m => m.loadBytes fieldPtr (bitFieldByteCount offsetBits width))
  match bitFieldBytesNat bs with
  | none => refuseUnsupported "bit-field reads an indeterminate representation"
  | some raw =>
      pure (.int storageTy (bitFieldSignedValue storageTy width
        (raw / ((2 : Nat) ^ (offsetBits % 8)))))

/-- Update the bit-field's bytes for assignment or initialization. The offset
is record-relative, while `fieldPtr` already points to the first byte. -/
def storeBitField (fieldTy : String) (fieldPtr : Ptr) (offsetBits width : Nat)
    (structured : Option LeanModels.Clang.QualType) (v : CVal) : EvalM CVal := do
  match bitFieldIntTy structured width, v with
  | some storageTy, .int _ n =>
      let bs ← readMem (fun m => m.loadBytes fieldPtr (bitFieldByteCount offsetBits width))
      -- The pinned two's-complement conversion retains the low field bits.
      -- Boolean conversion first maps all nonzero values to one.
      let fieldValue := bitFieldResidue storageTy width n
      let factor := 2 ^ (offsetBits % 8)
      match mergeBitFieldBytes bs ((2 ^ width - 1) * factor) (fieldValue * factor) with
      | some bytes =>
          writeMem (fun m => m.storeBytes fieldPtr bytes)
          pure (.int storageTy (bitFieldSignedValue storageTy width fieldValue))
      | none => refuseUnsupported "partly initialized bit-field byte"
  | none, _ => refuseUnsupported (bitFieldTypeError structured fieldTy width)
  | _, _ => refuseUnsupported s!"unsupported bit-field store '{fieldTy}'"


/-- Record identities and byte offsets along a terminal projection from
the complete object to the immediate owner. A struct contributes its last
member and a union can contribute any member. -/
private def Layout.trailingRecordPath (layout : Layout) (owner : DeclarationId) :
    Expr → Option (List (DeclarationId × Nat))
  | .paren base .. => layout.trailingRecordPath owner base
  | .member base field arrow _ _ (some parent) _ => do
      if !layout.terminalFieldDecl parent field then none else do
        let off ← layout.fieldOffDecl parent field
        let path ← if arrow then some [(parent, 0)] else layout.trailingRecordPath parent base
        let (_, parentOff) ← path.getLast?
        pure (path ++ [(owner, parentOff + off)])
  | .declRef .. | .unop "*" .. => some [(owner, 0)]
  | _ => none

/-- C23 §6.7.3.2p20 and GCC's Arrays of Length Zero. The longest array
must fit the complete allocation or an observed declared root object.
Every enclosing record's padding and alignment constrain the available
bytes. GNU zero- and one-element arrays extend into additional storage.
Their ordinary declared size is still used by `sizeof`. -/
private def Layout.trailingArrayExtent (layout : Layout) (m : Mem) (p : Ptr)
    (path : List (DeclarationId × Nat)) (fieldOffset stride : Nat)
    (count : Option Nat) : Option Nat := do
  let (root, _) ← path.head?
  let (owner, ownerOffset) ← path.getLast?
  let id ← p.obj
  let object ← m.get? id
  let wholeObject := match (m.structuredType? id).map LeanModels.Clang.QualType.unqualified with
    | some (.record record) => record.value == root.value
    | none => object.dur == .allocated &&
        (path.length > 1 || p.bound == some (object.size : Int))
    | _ => false
  if !wholeObject || !object.live || p.off != (ownerOffset : Int) || stride == 0 then none
  else do
    let limit ← path.foldlM (fun limit (record, start) => do
      let alignment ← layout.recordAlignmentDecl record
      let size ← layout.recordSizeDecl record
      if alignment == 0 || start + size > limit then none
      else some (start + ((limit - start) / alignment) * alignment)) object.size
    let size ← layout.recordSizeDecl owner
    let start := ownerOffset + fieldOffset
    if start > limit || (count.isSome && ownerOffset + size >= limit) then none
    else some (((limit - start) / stride) * stride)

mutual

def evalCall (ctx : Ctx) (callee : Expr) (args : List Expr) : EvalM CVal := do
  if functionPointerBitCast callee then
    refuseUnsupported "call through an incompatible function-pointer cast"
  if hasArgConflict args then
    refuseUnsupported "unsequenced side effects in call arguments"
  match calleeName callee with
  | some _ =>
      match calleeName callee with
      | some "__builtin_constant_p" =>
          let placeholders := args.map (fun e =>
            { value := .undef, promotedType := e.structuredType?, sourceExpr := some e })
          ctx.call callee none placeholders
      | _ =>
          let vs ← evalArgs ctx args
          ctx.call callee none (args.zipWith (fun e v =>
            { value := v, promotedType := e.structuredType?, sourceExpr := some e }) vs)
  | none =>
      let target ← evalExpr ctx callee
      let vs ← evalArgs ctx args
      ctx.call callee (some target) (args.zipWith (fun e v =>
        { value := v, promotedType := e.structuredType?, sourceExpr := some e }) vs)
  termination_by 2 * (callee.size + Expr.sizes args) + 2
  decreasing_by
    all_goals simp_wf
    all_goals have hc := Expr.size_pos callee
    all_goals have hcle : 1 ≤ callee.size := by omega
    all_goals simp [Expr.sizes_cons, Expr.sizes, Expr.size] at *
    all_goals omega

/-- §6.3.2.1p1 — an expression in LVALUE position, yielding the address
it designates.

**Five cases, and the census chose them**: the 1837 lvalue conversions
take their operand from `DeclRefExpr` 1406, `MemberExpr` 248,
`ArraySubscriptExpr` 169, `UnaryOperator` (`*`) 13 and
`CompoundLiteralExpr` 1; the 287 assignments and 63 increments target the
same kinds. Anything else in lvalue position is a refusal, never a
fallthrough. -/
def evalLValue (ctx : Ctx) : Expr → EvalM Ptr
  | .paren sub _ _ .. => evalLValue ctx sub
  | .exprWithCleanups sub _ _ .. => evalLValue ctx sub
  | .materializeTemporary sub _ _ .. => evalLValue ctx sub
  | .strLit value decoded _ _ .. => do
      let bs ← match decoded with
        | some bytes => pure (bytes.map (fun b => CByte.conc (UInt8.ofNat b)))
        | none => match plainStringBytes value with
          | some bs => pure (bs ++ [CByte.conc 0])
          | none => refuseUnsupported "string literal with escape or non-ASCII spelling"
      let m ← get
      let (m', o) := m.alloc .static_ bs.length (some "char[]")
      set m'
      writeMem (fun m => m.storeBytes (Ptr.toObjectBound o bs.length) bs)
      pure (Ptr.toObjectBound o bs.length)
  -- §6.5.2p2: an identifier designating an object is an lvalue.
  | .declRef (some _) _ "FunctionDecl" _ _ .. =>
      -- A function designator has no object address.  The address-of arm
      -- recognizes this parser node and returns its declaration identity;
      -- this placeholder keeps the shared lvalue recursion well-founded.
      pure Ptr.null
  | .declRef (some id) name _ ty _ .. =>
      if name == "stdout" then
        match ctx.stdoutObj with
        | some o => pure (Ptr.toObject o)
        | none => pure (Ptr.toObject 0)
      else match ctx.idEnv.lookup? id with
      | some o =>
          pure (match ctx.layout.sizeAt (some id) ty with
            | some sz => Ptr.toObjectBound o sz
            | none => Ptr.toObject o)
      | none => refuseUnsupported s!"unbound declaration '{id.value}' (name '{name}')"
  | .declRef none name _ ty _ .. =>
      if name == "stdout" then
        match ctx.stdoutObj with
        | some o => pure (Ptr.toObject o)
        | none => pure (Ptr.toObject 0)
      else match ctx.env.lookup? name with
      | some o =>
          pure (match ctx.layout.sizeAt none ty with
            | some sz => Ptr.toObjectBound o sz
            | none => Ptr.toObject o)
      | none => refuseUnsupported s!"unbound name '{name}'"
  -- §6.5.3.4p4: `p->f` is DEFINED as `(*p).f`, so the two spellings are
  -- ONE rule here. 226 arrow sites, 184 dot.
  | .member base field arrow ty span recordId structuredType =>
      memberAddr ctx (.member base field arrow ty span recordId structuredType)
        base field arrow ty recordId
  -- §6.5.3.2p2: `a[i]` is DEFINED as `*(a + i)`. The base arrives already
  -- decayed (clang inserts ArrayToPointerDecay), so it is a VALUE here.
  | .index base idx ty _ .. => indexAddr ctx base idx ty
  | .call callee args ty _ _ => do
      let value ← evalCall ctx callee args
      match value with
      | .aggregate _ bytes => do
          let m ← get
          let (m', fresh) := m.alloc .automatic bytes.length (some ty)
          set m'
          writeMem (fun m => m.storeBytes (Ptr.toObjectBound fresh bytes.length) bytes)
          pure (Ptr.toObjectBound fresh bytes.length)
      | _ => refuseUnsupported "call result is not an aggregate lvalue"
  -- §6.5.4.2p4: the operand of unary `*` is a pointer VALUE.
  | .unop op sub _ _ _ .. =>
      if op == "*" then (do let v ← evalExpr ctx sub; asPtr v)
      else refuseUnsupported s!"unary '{op}' is not an lvalue"
  | .compoundLit init ty span structured => do
      match ctx.layout.sizeAtStructured none ty structured with
      | none => refuseUnsupported s!"no layout for compound literal type '{ty}'"
      | some sz => do
          let m ← get
          let o ← match m.compoundObject? span with
            | some existing => pure existing
            | none =>
            let storageTy :=
              none
            let (m', fresh) := m.alloc .automatic sz storageTy
            set (m'.rememberCompound span fresh)
            pure fresh
          ctx.compoundInit 64 ctx.env ctx.idEnv ctx.layout (Ptr.toObject o) ty init
          pure (Ptr.toObject o)
  | e => refuseUnsupported s!"not an lvalue: {e.kindName}"
  termination_by e => 2 * e.size + 1
  decreasing_by all_goals (simp_wf <;> omega)

/-- §6.5 — an expression in VALUE position. -/
def evalExpr (ctx : Ctx) : Expr → EvalM CVal
  | .paren sub _ _ .. => evalExpr ctx sub
  | .exprWithCleanups sub _ _ .. =>
      -- C has no temporary-destructor cleanup action. Preserve Clang's
      -- full-expression node and evaluate its child under C23's rules.
      evalExpr ctx sub
  | .materializeTemporary sub _ _ .. => evalExpr ctx sub
  | .compoundLit init ty span structured => do
      match ctx.layout.sizeAtStructured none ty structured with
      | none => refuseUnsupported s!"no layout for compound literal type '{ty}'"
      | some sz => do
          let m ← get
          let o ← match m.compoundObject? span with
            | some existing => pure existing
            | none =>
            let storageTy :=
              none
            let (m', fresh) := m.alloc .automatic sz storageTy
            set (m'.rememberCompound span fresh)
            pure fresh
          ctx.compoundInit 64 ctx.env ctx.idEnv ctx.layout (Ptr.toObject o) ty init
          pure (CVal.ptr (Ptr.toObject o))

  -- ===== §6.3 — the conversion lattice, all eight castKinds =====
  | .implicitCast ck sub ty span structuredType
  | .cast ck sub ty span structuredType =>
      if ck == "LValueToRValue" then do
        if isStdoutRef sub then
          match ctx.stdoutObj with
          | some o => pure (.ptr (Ptr.toObject o))
          | none => pure (.ptr (Ptr.toObject 0))
        else
        -- §6.3.2.1p2 — 1837 sites, the load-bearing implicit of the corpus.
          let p ← evalLValue ctx sub
          let functionValue ←
            match (ctx.layout.structuredTypeAt sub).bind LeanModels.Clang.QualType.pointee with
            | some (.function ..) => readMem (fun m => Mem.loadFunction m p)
            | _ => pure none
          match functionValue with
          | some id => pure (.funPtr id)
          | none =>
              match ctx.layout.bitFieldOf sub with
              | some (offsetBits, width) =>
                  loadBitFieldAt sub.ty p offsetBits width (ctx.layout.structuredTypeAt sub)
              | none =>
                  ctx.loadAt p ty
                    (ctx.layout.exprSizeAt sub ty)
                    (ctx.layout.structuredTypeAt sub) (some sub)
      else if ck == "ArrayToPointerDecay" then do
        -- §6.3.2.1p3 — 405 sites, the LARGEST pointer producer there is.
        let p ← evalLValue ctx sub
        pure (.ptr p)
      else if ck == "NullToPointer" then
        -- §6.3.2.3p3 — a null pointer constant becomes a null pointer.
        do
          let _ ← evalExpr ctx sub
          pure (.ptr Ptr.null)
      else if ck == "IntegralCast" then do
        -- §6.3.1.3 — defined to unsigned; to signed it is the PROFILE's
        -- answer to `J.3.6(3)`, not the standard's (see `Value.convert`).
        let v ← evalExpr ctx sub
        let (_, n) ← asInt v
        let t ← match structuredType.bind intTyOfStructured with
          | some projected => pure projected
          | none => refuseUnsupported "integral cast lacks parser-native destination type"
        pure (convert t n)
      else if ck == "IntegralToBoolean" then do
        let v ← evalExpr ctx sub
        let (_, n) ← asInt v
        pure (convert IntTy.bool_ n)
      else if ck == "NoOp" then
        -- A qualifier or typedef change: the VALUE is untouched. 217 sites,
        -- and they are why type equality must be resolution, not spelling.
        evalExpr ctx sub
      else if ck == "ToVoid" then
        do
        let _ ← evalExpr ctx sub
        pure .undef
      else if ck == "BitCast" then
        -- C23 §6.3.2.3p7 defines conversion between object-pointer types.
        -- The conversion preserves provenance and does not inspect the
        -- pointed-to object.  Effective-type compatibility is checked when a
        -- later lvalue access loads or stores through the converted pointer
        -- under §6.5p6-p7.
        let sourceIsPointer := sub.structuredType?.any fun q =>
          match q.unqualified with
          | .pointer _ => true
          | _ => false
        let targetIsPointer := structuredType.any fun q =>
          match q.unqualified with
          | .pointer _ => true
          | _ => false
        if sourceIsPointer && targetIsPointer then
          evalExpr ctx sub
        else
          refuseUnsupported "BitCast requires parser-native object pointer types"
      else if ck == "FunctionToPointerDecay" then
        match sub with
        | .declRef (some id) _ "FunctionDecl" _ _ .. => pure (.funPtr id)
        | .paren (.unop "*" ptr _ _ _ ..) _ _ .. => do
            -- §6.3.2.1p4: a function designator produced by indirection is
            -- converted without inventing an address.
            let v ← evalExpr ctx ptr
            match v with
            | .funPtr id => pure (.funPtr id)
            | _ => refuseUnsupported "function-to-pointer decay of an unresolved function"
        | _ => refuseUnsupported "function-to-pointer decay of an unresolved function"
      else if ck == "IntegralToFloating" then
        do
        let v ← evalExpr ctx sub
        let (_, n) ← asInt v
        match structuredType.bind floatBitsOfStructured with
        | some 32 => pure (.float32 (Float32.Model.ofInt n))
        | some 64 => pure (.float64 (Float.Model.ofInt n))
        | _ => refuseUnsupported "integer-to-floating conversion lacks parser-native destination type"
      else if ck == "FloatingCast" then
        do
          let v ← evalExpr ctx sub
          floatCast v structuredType
      else if ck == "FloatingToIntegral" then
        do
        let v ← evalExpr ctx sub
        let t ← intTyOfNode structuredType
        match v with
        | .float32 f => float32ToInt f t
        | .float64 f => float64ToInt f t
        | _ => refuseUnsupported "non-floating value in floating-to-integral conversion"
      else if ck == "PointerToIntegral" then
        -- C23 §6.3.2.3p6 leaves the representation implementation-defined.
        -- The pinned LP64 profile admits the unchanged round-trip token. It
        -- retains the pointer provenance and is consumed only by the
        -- corresponding parser-node IntegralToPointer case. Arithmetic on
        -- the token remains a separate refusal, so this does not invent an
        -- address or recover provenance from an arbitrary integer.
        do
          let v ← evalExpr ctx sub
          match v with
          | .ptr p => pure (.ptrInt p)
          | .funPtr _ => refuseUnsupported "nonValueRepresentation"
          | _ => refuseUnsupported "nonValueRepresentation"
      else if ck == "IntegralToPointer" then
        if pointerTypeOfNode structuredType then do
          let v ← evalExpr ctx sub
          match v with
          | .ptrInt p => pure (.ptr p)
          | .int _ _ =>
              refuseUnsupported "isolated non-null integer-to-pointer cast requires PNVI-ae exposure and recovery"
          | _ =>
              refuseUnsupported "integer-to-pointer conversion is not an unchanged uintptr_t/intptr_t round-trip"
        else refuseUnsupported "integer-to-pointer conversion outside pointer type"
      else refuseUnsupported s!"castKind '{ck}'"

  -- ===== §6.5.14 / §6.5.15 — THE DRAIN AMENDMENT =====
  -- A short-circuiting construct's out-memory is a function of its ANSWER.
  -- The unevaluated operand is never run, so the memory it WOULD have
  -- produced never exists — there is nothing to speak about, which is
  -- precisely what the amendment forbids concluding. 181 sites in all.
  | .binop op l r ty _ structuredType =>
      if op != "&&" && op != "||" && op != "," && op != "=" &&
          binaryHasUnsequencedWrite l r then
        refuseUnsupported "unsequenced side effects in binary operands"
      else
      if op == "&&" then do
        -- §6.5.14p4: the right operand is evaluated ONLY if the left
        -- compares unequal to 0 — and §6.5.14p4 also makes this a SEQUENCE
        -- POINT, which is what makes a two-step threading expressible.
        let lv ← evalExpr ctx l
        let lb ← truthy lv
        if !lb then pure (ofBool false)
        else do let rv ← evalExpr ctx r; let rb ← truthy rv; pure (ofBool rb)
      else if op == "||" then do
        -- §6.5.15p4: …only if the left compares EQUAL to 0.
        let lv ← evalExpr ctx l
        let lb ← truthy lv
        if lb then pure (ofBool true)
        else do let rv ← evalExpr ctx r; let rb ← truthy rv; pure (ofBool rb)
      else if op == "," then do
        -- §6.5.18p2: both, in order, the left value discarded. 1 site.
        let _ ← evalExpr ctx l
        evalExpr ctx r
      else if op == "=" then do
        -- §6.5.17.2 — simple assignment, 287 sites. The store is sequenced
        -- after the right operand's value computation, which is why the
        -- sequencing census could admit 53 of its 73 multi-effect full
        -- expressions by inspection (`docs/c-semantics-design.md` §4.4).
        if assignmentHasUnsequencedWrite l r then
          refuseUnsupported "unsequenced side effects in assignment"
        let p ← evalLValue ctx l
        let v ← evalExpr ctx r
        let lStructured := ctx.layout.structuredTypeAt l
        match ctx.layout.bitFieldOf l with
        | some (offsetBits, width) =>
            storeBitField l.ty p offsetBits width lStructured v
        | none =>
            storeAt ctx.aliasModel p l.ty v lStructured
            match lStructured.bind intTyOfStructured, v with
            | some t, .int _ n => pure (convert t n)
            | _, _ => pure v
      else do
        let lv ← evalExpr ctx l
        let rv ← evalExpr ctx r
        let wideBitField :=
          (ctx.layout.bitFieldOf l).orElse (fun _ => ctx.layout.bitFieldOf r) |>.any
            (fun (_, width) => width > 32 && (op == "*" || op == "<<" || op == ">>"))
        if wideBitField then
          refuseUnsupported "arithmetic on bit-fields wider than int requires exact promotion semantics"
        else
          let pointerBase := match lv, rv with
            | .ptr _, _ => some l
            | _, .ptr _ => some r
            | _, _ => some l
          evalArith ctx op lv rv ty (some l.ty) pointerBase structuredType

  -- §6.5.16p4 — `?:`, the third short-circuit: EXACTLY ONE arm runs. 42 sites.
  | .cond c t e _ _ .. => do
      let cv ← evalExpr ctx c
      let b ← truthy cv
      if b then evalExpr ctx t else evalExpr ctx e

  -- ===== §6.5.3.5 / §6.5.4 — unary =====
  | .unop op sub post ty _ .. =>
      if op == "&" then do
        -- §6.5.4.2p3 — address-of, 106 sites. It does NOT read the object.
        let p ← evalLValue ctx sub
        match sub with
        | .declRef (some id) _ "FunctionDecl" _ _ .. => pure (.funPtr id)
        | _ => pure (.ptr p)
      else if op == "*" then do
        -- §6.5.4.2p4 — indirection reaching value position directly.
        let v ← evalExpr ctx sub
        match v with
        | .funPtr id => pure (.funPtr id)
        | _ =>
            let p ← asPtr v
            let pointee := (ctx.layout.structuredTypeAt sub).bind
              LeanModels.Clang.QualType.pointee
            ctx.loadAt p ty
              (ctx.layout.exprSizeAt sub ty) pointee
      else if op == "!" then do
        -- §6.5.4.3p5 — `!x` is `(0 == x)`. 80 sites.
        let v ← evalExpr ctx sub
        let b ← truthy v
        pure (ofBool (!b))
      else if op == "~" then do
        -- C23 §6.5.4.3p4: integer promotions precede bitwise complement.
        let v ← evalExpr ctx sub
        let (t, n) ← asInt v
        pure (.int t (bitNot t n))
      else if op == "-" then do
        -- §6.5.4.3p3 — unary minus OVERFLOWS at `-INT_MIN`: `J.2(35)`.
        let v ← evalExpr ctx sub
        match v with
        | .float32 f => pure (.float32 (-f))
        | .float64 f => pure (.float64 (-f))
        | _ =>
            let (t, n) ← asInt v
            match negOp t n with
            | .ok r => pure r
            | .ub u => refuseValue u
      else if op == "+" then evalExpr ctx sub
      else if op == "++" || op == "--" then do
        -- §6.5.3.5 — and MEASURED: all 63 increment sites in the corpus are
        -- POSTFIX; it never writes `++i`. Postfix yields the value BEFORE
        -- the update, and the update itself can overflow (`J.2(35)`).
        let p ← evalLValue ctx sub
        let subStructured := ctx.layout.structuredTypeAt sub
        let bits := ctx.layout.bitFieldOf sub
        let old ← match bits with
          | some (offsetBits, width) => loadBitFieldAt sub.ty p offsetBits width subStructured
          | none => ctx.loadAt p sub.ty (ctx.layout.exprSizeAt sub sub.ty) subStructured (some sub)
        match old with
        | .ptr _ =>
            -- C23 §6.5.3.5p2 defines pointer increment/decrement in terms
            -- of compound assignment. Reuse the provenance-checked pointer
            -- arithmetic rule, so one-past and object bounds stay exact.
            let nv ← evalArith ctx (if op == "++" then "+" else "-") old
              (.int IntTy.int_ 1) sub.ty none (some sub) subStructured
            storeAt ctx.aliasModel p sub.ty nv subStructured
            pure (if post then old else nv)
        | .float32 f => do
            let one := Float32.Model.ofInt 1
            let nv ← float32Binop (if op == "++" then "+" else "-") f one
            storeAt ctx.aliasModel p sub.ty nv subStructured
            pure (if post then old else nv)
        | .float64 f => do
            let one := Float.Model.ofInt 1
            let nv ← float64Binop (if op == "++" then "+" else "-") f one
            storeAt ctx.aliasModel p sub.ty nv subStructured
            pure (if post then old else nv)
        | _ =>
            let (storageT, n) ← asInt old
            -- C23 §6.3.1.1p2 uses the bit-field's value range for
            -- integer promotions of bool, signed int, and unsigned int.
            let t ← match bits with
              | none => pure (promoteIntTy storageT)
              | some (_, width) =>
                  if storageT == IntTy.bool_ || storageT == IntTy.int_ ||
                      (storageT == IntTy.uint && width < IntTy.int_.bits) then
                    pure IntTy.int_
                  else if storageT == IntTy.uint then pure IntTy.uint
                  else refuseUnsupported "increment of an extended-type bit-field"
            match (if op == "++" then addOp t n 1 else subOp t n 1) with
            | .ub u => refuseValue u
            | .ok (.int _ nv) => do
                let storedT ← match subStructured.bind intTyOfStructured with
                  | some projected => pure projected
                  | none => refuseUnsupported "increment lacks parser-native storage type"
                let stored := convert storedT nv
                let updated ← match bits with
                  | some (offsetBits, width) =>
                      storeBitField sub.ty p offsetBits width subStructured stored
                  | none =>
                      storeAt ctx.aliasModel p sub.ty stored subStructured
                      pure stored
                pure (if post then old else updated)
            | .ok _ => refuseUnsupported "increment of a non-integer value"
      else refuseUnsupported s!"unary operator '{op}'"

  -- §6.5.17.3 — compound assignment: `a op= b` is `a = a op b` with the
  -- lvalue evaluated ONCE. 24 sites (`+=` 10, `|=` 6, `^=` 3, `-=` 3, `*=` 2).
  | .compoundAssign op l r computeLHSType computeResultType ty _ lNodeType computeLhsNodeType computeResultNodeType => do
      if compoundAssignmentHasUnsequencedWrite l r then
        refuseUnsupported "unsequenced side effects in compound assignment"
      let bits := ctx.layout.bitFieldOf l
      let p ← evalLValue ctx l
      let lStructured := ctx.layout.structuredTypeAt l
      let rv ← evalExpr ctx r
      -- C23 §6.5.16.3: the update is sequenced after the value
      -- computations of both operands.  The lvalue is evaluated once for
      -- its address, while its stored value is read only after the RHS has
      -- completed; this preserves writes made by a called RHS (for example
      -- `x |= foo()` where `foo` updates `x`).
      let old ← match bits with
        | some (offsetBits, width) =>
            loadBitFieldAt l.ty p offsetBits width lStructured
        | none =>
            ctx.loadAt p l.ty
              (ctx.layout.exprSizeAt l (Expr.ty l)) lStructured (some l)
      match old, rv with
      | .ptr _, .int _ _ => do
          -- §6.5.17.3: pointer compound assignment uses the same
          -- pointer-plus/minus-integer rule as the corresponding binary
          -- operator, with the lvalue evaluated once.  `evalArith` already
          -- performs the provenance, bound, and element-size checks.
          let nv ← evalArith ctx (compoundBase op) old rv computeResultType none (some l) lStructured
          storeAt ctx.aliasModel p l.ty nv lStructured
          pure nv
      | .float32 a, .float32 b => do
          let nv ← float32Binop (compoundBase op) a b
          storeAt ctx.aliasModel p l.ty nv lStructured
          pure nv
      | .float64 a, .float64 b => do
          let nv ← float64Binop (compoundBase op) a b
          storeAt ctx.aliasModel p l.ty nv lStructured
          pure nv
      | .int oldT oldN, .int _ rvN => do
          match computeLhsNodeType.bind intTyOfStructured,
              computeResultNodeType.bind intTyOfStructured,
              lNodeType.bind intTyOfStructured with
          | some lhsTy, some resultTy, some storedTy =>
              let lhs := convert lhsTy oldN
              let rhs := convert resultTy rvN
              let computed ← evalArith ctx (compoundBase op)
                lhs rhs computeResultType
                none (some l) computeResultNodeType
              match computed with
              | .int _ n =>
                  let stored := convert storedTy n
                  match bits with
                  | some (offsetBits, width) =>
                      storeBitField l.ty p offsetBits width lStructured stored
                  | none =>
                      storeAt ctx.aliasModel p l.ty stored lStructured
                      pure stored
              | _ => refuseUnsupported "integer compound assignment produced a non-integer value"
          | _, _, _ =>
              refuseUnsupported
                "compound assignment lacks parser-native compute type observations"
      | _, _ => do
          match computeResultNodeType.bind floatBitsOfStructured with
          | some resultBits =>
              let computed ← compoundFloatResult (compoundBase op) resultBits old rv
              let stored ← convertCompoundResult computed lNodeType
              match bits with
              | some (offsetBits, width) =>
                  storeBitField l.ty p offsetBits width lStructured stored
              | none =>
                  storeAt ctx.aliasModel p l.ty stored lStructured
                  pure stored
          | none =>
              refuseUnsupported
                "compound assignment lacks parser-native compute type observations"

  -- ===== lvalues reaching value position without a conversion =====
  -- Clang wraps scalar reads in `LValueToRValue`, so these are the
  -- aggregate-valued cases; evaluating the address and loading is the rule
  -- either way (§6.3.2.1p2).
  | .member base field arrow ty span recordId structuredType => do
      let memberExpr := .member base field arrow ty span recordId structuredType
      let p ← memberAddr ctx memberExpr base field arrow ty recordId
      match ctx.layout.fieldBitsAtResolved base field with
      | some (offsetBits, width) => loadBitFieldAt ty p offsetBits width structuredType
      | none =>
          ctx.loadAt p ty
            (ctx.layout.exprSizeAt (.member base field arrow ty span recordId structuredType) ty)
            structuredType
  | .index base idx ty _ .. => do
      let p ← indexAddr ctx base idx ty
      let elementStructured := (ctx.layout.structuredTypeAt base).bind fun q =>
        match q.unqualified with
        | .array element _ | .pointer element => some element
        | _ => none
      ctx.loadAt p ty
        (ctx.layout.elementSizeAt base ty) elementStructured

  -- ===== §6.4.4 — constants =====
  | .intLit v _ _ structuredType => do
      let t ← intTyOfNode structuredType
      match v.toInt? with
      | some n => pure (.int t n)
      | none => refuseUnsupported s!"integer literal spelling '{v}'"
  | .boolLit b _ _ .. =>
      pure (.int IntTy.bool_ (if b then 1 else 0))
  | .nullPtrLit _ _ _ =>
      -- C23 §6.3.2.3: the parser-native nullptr literal is a null pointer
      -- value before any contextual conversion is applied.
      pure (.ptr Ptr.null)
  | .choose cond yes no _ _ .. =>
      match chooseCond cond with
      | some true => evalExpr ctx yes
      | some false => evalExpr ctx no
      | none => refuseUnsupported "ChooseExpr condition is not a folded integer constant"
  | .charLit v _ _ structuredType => do
      let t ← intTyOfNode structuredType
      match v.toInt? with
      | some n => pure (.int t (if t == IntTy.int_ then charLiteralValue n else n))
      | none => refuseUnsupported s!"character literal spelling '{v}'"
  | .strLit value decoded _ _ .. => do
      let bs ← match decoded with
        | some bytes => pure (bytes.map (fun b => CByte.conc (UInt8.ofNat b)))
        | none => match plainStringBytes value with
          | some bs => pure (bs ++ [CByte.conc 0])
          | none => refuseUnsupported "string literal with escape or non-ASCII spelling"
      let m ← get
      let (m', o) := m.alloc .static_ bs.length (some "char[]")
      set m'
      writeMem (fun m => m.storeBytes (Ptr.toObjectBound o bs.length) bs)
      pure (.ptr (Ptr.toObjectBound o bs.length))
  | .floatLit _ bitsHex bitWidth _ _ .. => floatLiteralValue bitsHex bitWidth

  -- A bare name in value position is an enumeration constant; every other
  -- name arrives wrapped in a conversion or a decay.
  | e@(.declRef (some id) name declKind ty _ structuredType) =>
      if declKind == "EnumConstantDecl" then
        match (ctx.enumIds.find? (·.1 == id)).map (·.2) with
        | some n => do
            match structuredType.bind intTyOfStructured with
            | some t => pure (.int t n)
            | none => refuseUnsupported "enumeration constant lacks parser-native QualType"
        | none => refuseUnsupported s!"unknown enum declaration '{id.value}' (name '{name}')"
      else match ctx.idEnv.lookup? id with
        | some o =>
            let p := match ctx.layout.sizeAt (some id) ty with
              | some sz => Ptr.toObjectBound o sz | none => Ptr.toObject o
            ctx.loadAt p ty (ctx.layout.sizeAt (some id) ty)
              (ctx.layout.structuredTypeDecl id) (some e)
        | none => refuseUnsupported s!"unbound declaration '{id.value}' (name '{name}')"
  | .declRef none name declKind ty _ structuredType =>
      if declKind == "EnumConstantDecl" then
        match (ctx.enums.find? (·.1 == name)).map (·.2) with
        | some n =>
            match structuredType.bind intTyOfStructured with
            | some t => pure (.int t n)
            | none => refuseUnsupported "enumeration constant lacks parser-native QualType"
        | none => refuseUnsupported s!"unknown enum constant '{name}'"
      else match ctx.env.lookup? name with
        | some o =>
            let p := match ctx.layout.sizeAt none ty with
              | some sz => Ptr.toObjectBound o sz | none => Ptr.toObject o
            ctx.loadAt p ty (ctx.layout.sizeAt none ty)
        | none => refuseUnsupported s!"unbound name '{name}'"

  -- §6.5.3.3p4 — the arguments are evaluated HERE, in the caller's scope,
  -- and the handler receives VALUES. Still fuel-free: `evalArgs` is in this
  -- mutual block and shrinks the same `Expr` measure.
  | .call callee args _ _ .. => evalCall ctx callee args

  -- N3220 §6.5.4.4p2–5: fixed-size operands and alignof operands are
  -- unevaluated. The pinned ABI supplies the size/alignment and size_t.
  | .typeTrait trait _ _ _ _ _ operandSize operandAlignment structuredType => do
      let n ← match trait with
        | "sizeof" => match operandSize with
          | some n => pure n
          | none => refuseUnsupported "sizeof: no static ABI size for operand"
        | "alignof" | "__alignof" => match operandAlignment with
          | some n => pure n
          | none => refuseUnsupported s!"{trait}: no ABI alignment for operand"
        | _ => refuseUnsupported s!"type trait '{trait}'"
      match structuredType.bind intTyOfStructured with
      | some t => pure (.int t (n : Int))
      | none => refuseUnsupported s!"{trait} result lacks parser-native QualType"

  | .offsetOf _ _ offsetBytes structuredType => do
      let n ← match offsetBytes with
        | some value => pure value
        | none => refuseUnsupported "offsetof: parser supplied no constant byte offset"
      match structuredType.bind intTyOfStructured with
      | some t => pure (.int t (n : Int))
      | none => refuseUnsupported "offsetof result lacks parser-native QualType"

  | .constExpr v (some sub) ty _ structuredType => do
      -- Clang's folded spelling drops the sign from a negative constant
      -- (`value = "1"`, with `sub = -1`).  The approved AST keeps that
      -- operand, so evaluate it rather than treating the diagnostic value as
      -- the program's value (§6.6 constant expressions).
      let sv ← evalExpr ctx sub
      match sv with
      | .ptr p => pure (.ptr p)
      | .funPtr id => pure (.funPtr id)
      | _ =>
          let (_, n) ← asInt sv
          match structuredType.bind intTyOfStructured with
          | some t => pure (.int t n)
          | none => refuseUnsupported "constant expression lacks parser-native QualType"
  | .constExpr v none ty _ structuredType => do
      let t ← match structuredType.bind intTyOfStructured with
        | some t => pure t
        | none => refuseUnsupported "constant expression lacks parser-native QualType"
      match v.toInt? with
      | some n => pure (.int t n)
      | none => refuseUnsupported s!"constant expression '{v}'"
  | .vaArg ap ty _ structuredType => do
      -- C23 §7.16.1.1: consume the next actual argument from the abstract
      -- cursor. Compatibility is checked against the parser-resolved,
      -- default-promoted value; no ABI width or address is invented.
      let av ← evalExpr ctx ap
      let p ← asPtr av
      let v ← popVaArg p
      checkVaType ctx.layout structuredType v
  | .initList .. => refuseUnsupported "initializer list (inch 4)"
  | .arrayInitList .. => refuseUnsupported "initializer list in value position"
  | .designatedUpdate .. => refuseUnsupported "designated initializer update in value position"
  | .implicitValueInit .. => refuseUnsupported "implicit value initialization in value position"
  | .unsupported k _ _ => refuseUnsupported s!"out of tier: {k}"
  termination_by e => 2 * e.size + 1
  decreasing_by
    all_goals (simp_wf <;> (try simp [Expr.sizes_cons, Expr.size_unop, Expr.size_pos, Expr.sizes, Expr.size_constExpr, Expr.size, Expr.subexprs]) <;> omega)

/-- §6.5.3.3p4 — a call's arguments, evaluated in the CALLER's scope,
**left to right**.

This is the function inch 5 named and could not write, and it is in the
mutual block for the reason the failure taught: the recursion it needs is
`evalExpr`'s, so it must sit where `evalExpr`'s measure does. Handing the
evaluator OUT to a handler put the recursion somewhere nothing could
constrain it; keeping it here costs one extra decrease goal.

**LEFT-TO-RIGHT IS THE CANONICAL ORDER, NOT THE CLAIM.** §6.5.3.3p10
leaves argument evaluation *indeterminately sequenced* — `J.1(16)`, the
one Annex J entry this tier's `∀ order` ruling actually ranges over — so
this definition is how a WITNESS is extracted, and correctness is the
separate `∀ order` obligation over the 7 sites `docs/c23-spec-mirror.md`
§5.3 measured. Writing the canonical order down is what makes that
obligation STATABLE; it does not discharge it, and nothing here should be
read as if it did.

The measure is `2 * Expr.sizes es + 2`, and the `+ 2` is load-bearing:
the head step must beat `evalExpr`'s `2 * e.size + 1` for a list whose
tail is empty, and the tail step needs `0 < e.size` — which is why
`Expr.size_pos` had to come back. -/
def evalArgs (ctx : Ctx) : List Expr → EvalM (List CVal)
  | [] => pure []
  | e :: es => do
      let v ← evalExpr ctx e
      let vs ← evalArgs ctx es
      pure (v :: vs)
  termination_by es => 2 * Expr.sizes es + 2
  decreasing_by all_goals (simp_wf <;> omega)

/-- §6.5.3.4 — the ADDRESS of `base.field` / `base->field`.

Takes `base` — a strict SUBTERM — rather than the reassembled node. The
node this replaces was rebuilt as `.member base field arrow ty sp`, which
is not a subterm of anything, and that is what defeated the recursion. -/
def memberAddr (ctx : Ctx) (memberExpr : Expr) (base : Expr) (field : String) (arrow : Bool)
    (fieldTy : String) (recordId : Option DeclarationId) : EvalM Ptr := do
  let basePtr ← if arrow then (do let v ← evalExpr ctx base; asPtr v)
                else evalLValue ctx base
  match ctx.layout.fieldBitsAtResolved base field with
  | some (offsetBits, _) =>
      -- The field operation supplies its byte count. Keep the parent bound.
      pure (Mem.member basePtr (offsetBits / 8))
  | none =>
      let declaration := recordId.orElse (fun _ => directDeclId base)
      let off? := if field.isEmpty then
          ctx.layout.fieldOffStructuredDeclAt declaration memberExpr.structuredType?
            |>.orElse (fun _ => ctx.layout.fieldOffTypeDeclAt declaration base.ty fieldTy)
        else ctx.layout.fieldOffDeclAt declaration base.ty field
      match off? with
      | some off =>
          let recordLike := (ctx.layout.structuredTypeAt base).map
            LeanModels.Clang.QualType.recordLike |>.getD false
          let fieldSize :=
            (ctx.layout.fieldExtentAt base field fieldTy recordLike).orElse
              (fun _ => recordId.bind (fun rid => ctx.layout.fieldSizeDecl rid field))
          let structured := declaration.bind (fun did => ctx.layout.fieldStructuredDecl did field)
            |>.bind (LeanModels.Clang.QualType.resolveTypedefs
              (fun handle => ctx.layout.structuredType { value := handle.value }) 32)
          let extent ← match structured.map LeanModels.Clang.QualType.unqualified with
            | some type@(.array _ count) =>
                match ctx.layout.structuredStride type with
                | none =>
                    -- Opaque fixed-size fields, such as the native va_list,
                    -- retain their observed storage slot for address-taking.
                    pure (count.bind fun _ => fieldSize)
                | some stride => do
                    let fixed := count.map (· * stride)
                    let tailPath := do
                      let owner ← declaration
                      if count.getD 0 > 1 || !ctx.layout.terminalFieldDecl owner field then none
                      else if arrow then some [(owner, 0)]
                      else ctx.layout.trailingRecordPath owner base
                    let m ← get
                    pure ((tailPath.bind fun path =>
                      ctx.layout.trailingArrayExtent m basePtr path off stride count).orElse
                        (fun _ => fixed))
            | _ => pure fieldSize
          match extent with
          | some sz => pure (Mem.memberRange basePtr off sz)
          | none => refuseUnsupported s!"no layout for field '{field}'"
      | none => refuseUnsupported s!"no layout for field '{field}'"
  termination_by 2 * base.size + 2
  decreasing_by all_goals (simp_wf <;> omega)

/-- §6.5.3.2p2 — the ADDRESS of `base[idx]`. Same discipline: the parts,
never the rebuilt node. -/
def indexAddr (ctx : Ctx) (base idx : Expr) (ty : String) : EvalM Ptr := do
  match ctx.layout.structuredTypeAt base with
  | some structuredType =>
      if !structuredIndexable (some structuredType) base.ty then
        refuseUnsupported "subscript base is not an array or pointer type"
  | none => pure ()
  let bv ← evalExpr ctx base
  let bp ← asPtr bv
  let iv ← evalExpr ctx idx
  let (_, i) ← asInt iv
  let elementSize := ctx.layout.elementSizeAt base ty
  match elementSize with
  | some esz => readMem (fun m => Mem.subscript m bp esz i)
  | none => refuseUnsupported s!"no size for element type '{ty}'"
  termination_by 2 * (base.size + idx.size) + 2
  decreasing_by all_goals (simp_wf <;> omega)

end

/-! ### The termination argument, STATED

`docs/backlog/c.md` 2026-08-23-c-5: **a green build is not a termination
argument.** Inch 3 built green with `evalExpr` REBUILDING its
`.member`/`.index` nodes — which are not subterms — and it only worked
because structural inference had slack elsewhere. Inch 5 removed the
slack and the whole block fell over, exposing a defect that had been
latent through three landings.

So the measure is written down rather than inferred. `Expr.size` counts
expression nodes (`Ast.lean`); the main pair carries `2 * size + 1` and
the address helpers `2 * size + 2`, so a helper is strictly smaller than
the node that called it and strictly larger than the subterms it
evaluates. The doubling is what buys room for that middle rung. -/
/-! ## Spec lemmas — arm level, and the drain amendment

`docs/backlog.md` §L61 measured what altitude buys here: unfolded
primitives produced **259 verification conditions and FAILED**, four
triples produced **12 and closed**. So the primitives get lemmas at ARM
granularity — one per branch, not one per function — because a branch is
what a proof actually lands on.

These are stated as plain rewrite lemmas rather than `Std.Do` `@[spec]`
triples. The SHAPE is the same (a pre-condition on the arm, a determined
post), which is what `docs/c-semantics-design.md` §4.1a asks for; wiring
them to `mvcgen` is inch 4's, once `CWorld` fixes the state type. -/

section Spec

variable {α : Type}

/-- `truthy`'s nonzero arm. -/
@[simp] theorem truthy_int_ne (t : IntTy) (n : Int) (h : n ≠ 0) :
    truthy (.int t n) = pure true := by
  have hb : (n != 0) = true := by simp [h]
  simp [truthy, hb]

/-- `truthy`'s zero arm — the one the short circuit turns on. -/
@[simp] theorem truthy_int_zero (t : IntTy) : truthy (.int t 0) = pure false := by
  simp [truthy]

/-- `truthy`'s null-pointer arm (§6.5.10p3). -/
@[simp] theorem truthy_ptr_null : truthy (.ptr Ptr.null) = pure false := by
  simp [truthy, Ptr.isNull, Ptr.null]

/-- `asInt`'s success arm. -/
@[simp] theorem asInt_int (t : IntTy) (n : Int) : asInt (.int t n) = pure (t, n) := by
  simp [asInt]

/-- `asPtr`'s success arm. -/
@[simp] theorem asPtr_ptr (p : Ptr) : asPtr (.ptr p) = pure p := by
  simp [asPtr]

/-- Running a `pure` keeps the memory it was handed. -/
@[simp] theorem run_pure (m : Mem) (a : α) :
    EvalM.run m (pure a : EvalM α) = .ok (.ok a, m) := rfl

end Spec

/-! ### §6.5.14p4 — the drain amendment, as a theorem

> **A short-circuiting construct's out-world is a function of its ANSWER;
> the world goes in the HYPOTHESIS, never the conclusion.**

Read the statement below for what it does NOT say. `r` — the right
operand — appears only as an argument to the constructor. It appears in
no hypothesis and in no part of the conclusion. The out-memory named in
the conclusion is `m'`, which the HYPOTHESIS introduced as the LEFT
operand's out-memory.

That is the amendment: when the left operand answers 0, the memory the
right operand would have produced never exists, so the theorem cannot and
does not mention it. A statement of the form "…the out-world is the
right's…" would be unprovable here, which is the point. -/

/-- §6.5.14p4 — `&&` short-circuits: a false left operand answers 0 **in
the left operand's own out-memory**, whatever the right operand is. -/
theorem and_shortCircuits (ctx : Ctx) (l r : Expr) (ty : String) (sp : CSpan)
    (m m' : Mem) (t : IntTy)
    (hl : EvalM.run m (evalExpr ctx l) = .ok (.ok (.int t 0), m')) :
    EvalM.run m (evalExpr ctx (.binop "&&" l r ty sp none)) = .ok (.ok (ofBool false), m') := by
  simp only [EvalM.run, StateT.run] at hl ⊢
  simp [evalExpr, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, bind, StateT.bind,
    Except.bind, Except.pure,
    hl, truthy, ofBool, pure, ExceptT.pure, StateT.pure]

/-- §6.5.15p4 — `||` is the mirror: a TRUE left operand answers 1 in the
left operand's own out-memory, and the right operand is not evaluated. -/
theorem or_shortCircuits (ctx : Ctx) (l r : Expr) (ty : String) (sp : CSpan)
    (m m' : Mem) (t : IntTy) (n : Int) (hn : n ≠ 0)
    (hl : EvalM.run m (evalExpr ctx l) = .ok (.ok (.int t n), m')) :
    EvalM.run m (evalExpr ctx (.binop "||" l r ty sp none)) = .ok (.ok (ofBool true), m') := by
  simp only [EvalM.run, StateT.run] at hl ⊢
  simp [evalExpr, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, bind, StateT.bind,
    Except.bind, Except.pure,
    hl, hn, truthy, ofBool, pure, ExceptT.pure, StateT.pure]

/-- §6.5.16p4 — `?:` evaluates EXACTLY ONE arm, and the theorem names
only the arm that ran. -/
theorem cond_takesOneArm (ctx : Ctx) (c t e : Expr) (ty : String) (sp : CSpan)
    (m m' : Mem) (it : IntTy)
    (hc : EvalM.run m (evalExpr ctx c) = .ok (.ok (.int it 0), m')) :
    EvalM.run m (evalExpr ctx (.cond c t e ty sp none)) = EvalM.run m' (evalExpr ctx e) := by
  simp only [EvalM.run, StateT.run] at hc ⊢
  simp [evalExpr, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, bind, StateT.bind,
    Except.bind, Except.pure,
    hc, truthy, pure, ExceptT.pure, StateT.pure]

#print axioms and_shortCircuits
#print axioms or_shortCircuits
#print axioms cond_takesOneArm

/-! ## RUNG A — §6.5.3.3p10 / `J.1(16)`: PURITY, and the half of the ∀-order
obligation a syntax check can pay

`docs/c23-spec-mirror.md` §5.3 states the `J.1(16)` obligation per call
site as *"can this callee write what these siblings read"*. That is a
CONJUNCTION, and only its second half needs an effect summary:

1. **the siblings do not WRITE** — decidable from the term, and this
   section;
2. the one effectful argument does not write what the siblings READ —
   the effect-summary argument, which is **Rung B and is not claimed
   anywhere below.**

**The measurement is why (1) is worth landing on its own.** Over the
ingested corpus, gated in `Examples/c/sunfish/expr.lean` and reached
independently by `harness/c_construct_census.py`: of **320** call sites,
**215** take two or more arguments, and **208 of those 215 have EVERY
argument pure** — so at 208 of 215 multi-argument sites the ∀-order
obligation needs no effect summary at all: no order can differ, because
no order can write. The residue is exactly the **7** sites §5.3 already
names, and at none of them do two arguments carry an effect. **The
predicate that prices Rung B is the same predicate that cuts its domain
from 215 sites to 7.**

**`isPure` is an OVER-approximation, deliberately.** It is `nodeIsPure` at
EVERY node of the term — through `Expr.subexprs`, so it introduces no new
recursion, exactly as `Expr.size` does not — which means it calls an
expression impure whenever a write-capable node occurs anywhere inside
it, including under a `&&` that would never run it and under a `sizeof`
whose operand §6.5.4.4p2 does not evaluate at all. A sharper predicate
exists and is not needed: soundness is what the theorem consumes, and the
census says the coarseness costs nothing here — **the only impure node
kind occurring inside any call argument anywhere in the corpus is a
CALL** (10 occurrences), so the slack misclassifies no argument.

**What `isPure` is NOT.** It is not "has no observable effect". An
out-of-tier node is classified IMPURE even though this evaluator refuses
it, because *"the model declines"* is not *"the construct does not
write"*, and a predicate that pooled the two would silently become
unsound the day the construct is modelled. Likewise `initList` and
`compoundLit`, whose §6.7.11 semantics WRITES through the layout
(`docs/backlog/c.md` 2026-08-23-c-3). -/

/-- The write-capable NODE kinds, and nothing about their operands.

Read this against `evalExpr`'s clauses one for one: `storeAt` is reached
from exactly three of them — simple assignment (§6.5.17.2), compound
assignment (§6.5.17.3) and the increments (§6.5.3.5) — and `Ctx.call`
hands control to a handler this tier cannot see inside. Every other
clause in the block reaches memory only through `readMem`. -/
def Expr.nodeIsPure : Expr → Bool
  -- §6.5.17.2 — the store is `=`, and only `=`. Every other binary
  -- operator, `&&`/`||`/`,` included, is a value computation.
  | .binop op _ _ _ _ .. => op != "="
  -- §6.5.3.5 — measured: all 63 increment sites in the corpus are postfix,
  -- and both spellings write.
  | .unop op _ _ _ _ .. => op != "++" && op != "--"
  -- §6.5.17.3 — `a op= b` stores.
  | .compoundAssign .. => false
  | .choose .. => false
  -- §6.5.3.3 — an opaque callee. This is the constructor that makes the
  -- J.1(16) domain non-empty, and inch 5's repair is what made it REACHABLE.
  | .call .. => false
  | .vaArg .. => false
  -- §6.7.11 — aggregate initialization writes through the layout.
  | .initList .. | .arrayInitList .. | .implicitValueInit .. | .compoundLit .. => false
  | .designatedUpdate .. => false
  | .strLit .. => false
  -- Out of tier: unknown, therefore not pure.
  | .unsupported .. => false
  | .implicitCast _ (.paren (.unop "*" _ _ _ _ ..) _ _ ..) _ _ .. => false
  -- Function designator decay is semantically read-only, but its parser
  -- shape may evaluate an indirect designator. Keep the purity theorem's
  -- fragment conservative until that recursive identity path is covered.
  | .implicitCast ck _ _ _ .. => ck != "FunctionToPointerDecay"
  | .cast _ (.paren (.unop "*" _ _ _ _ ..) _ _ ..) _ _ .. => false
  | .cast ck _ _ _ .. => ck != "FunctionToPointerDecay"
  | _ => true

/-- An expression whose evaluation cannot change memory — `nodeIsPure` at
every node, itself included.

Stated through `Expr.subexprs` so that it introduces **no new recursion**:
the nested `List Expr` under `call` and `initList` is elaborated there,
once, which is the same reason `Expr.size` is defined that way
(`LeanModels/C/Ast.lean`). -/
def Expr.isPure (e : Expr) : Bool := e.subexprs.all Expr.nodeIsPure

/-! ### Reading a purity fact off a node

One general lemma for the HEAD, and one extraction per constructor the
evaluator recurses into. Only the forward direction is ever needed, which
is why none of these is stated as an equivalence. -/

/-- Every `subexprs` clause emits `e` itself, so a pure term has a pure
head. -/
theorem Expr.nodeIsPure_of_isPure {e : Expr} (h : Expr.isPure e = true) :
    Expr.nodeIsPure e = true := by
  cases e <;>
    simp_all [Expr.isPure, Expr.subexprs, Expr.nodeIsPure, List.all_cons, List.all_append]

theorem Expr.isPure_paren {s : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.paren s t sp q) = true) : Expr.isPure s = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_implicitCast {ck : String} {s : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.implicitCast ck s t sp q) = true) : Expr.isPure s = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_cast {ck : String} {s : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.cast ck s t sp q) = true) : Expr.isPure s = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_member {b : Expr} {f : String} {a : Bool} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    {recordId : Option DeclarationId}
    (h : Expr.isPure (.member b f a t sp recordId q) = true) : Expr.isPure b = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_unop {op : String} {s : Expr} {post : Bool} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.unop op s post t sp q) = true) : Expr.isPure s = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_index_base {b i : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.index b i t sp q) = true) : Expr.isPure b = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.1

theorem Expr.isPure_index_idx {b i : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.index b i t sp q) = true) : Expr.isPure i = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.2

theorem Expr.isPure_binop_l {op : String} {l r : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.binop op l r t sp q) = true) : Expr.isPure l = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.1

theorem Expr.isPure_binop_r {op : String} {l r : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.binop op l r t sp q) = true) : Expr.isPure r = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.2

theorem Expr.isPure_cond_c {c a b : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.cond c a b t sp q) = true) : Expr.isPure c = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.1.1

theorem Expr.isPure_cond_t {c a b : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.cond c a b t sp q) = true) : Expr.isPure a = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.1.2

theorem Expr.isPure_cond_e {c a b : Expr} {t : String} {sp : CSpan} {q : Option LeanModels.Clang.QualType}
    (h : Expr.isPure (.cond c a b t sp q) = true) : Expr.isPure b = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.2

/-! ### THE RUN SEAM — ADOPTED FROM `Core`, not restated here

This tier used to carry its own `run_bind` and its four step lemmas. They
are gone: `LeanModels/Core/Outcome.lean` §4 now holds them, generic in all
four of `SemMWith`'s parameters, and this file uses `SemMWith.run_bind`,
`run_bind_ok`, `run_bind_loud`, `run_bind_raise`, `run_pure`, `run_get`
and `run_throw` directly.

**The lift is what the convergence asked for and the paragraph that
carried it is deleted with it.** `2026-08-24-c-12` recorded that
`LeanModels/Go/Obs.lean` §1 had the same seam for `GoM`, that `GoM` and
`EvalM` are both `SemMWith`, and that the two proofs differed only by four
type substitutions — and it said the lift was a spine landing to be
priced rather than taken from a tier commit. It has now been taken, so
the note describing the duplication has no subject left.

> **A paragraph that exists to make a duplication visible is deleted by
> the commit that removes the duplication — carrying it afterwards
> documents a state the tree is no longer in.**

**One row stays, and it is genuinely this tier's.** `refuseUnsupported`
captures the memory AS IT STOOD at the refusal site — `fun m => .error (…
(some m))` — which is not Core's `refuseWith`, whose snapshot is a fixed
argument. §3.4's ruling put the capture in the primitive so no call site
can forget it; that makes the primitive C's, and so is its row. -/

section Seam
variable {α : Type}

/-- An out-of-tier refusal answers in the `Halt` BASE and carries the
memory it found, so there is no `.ok` for it to produce at all. Not
Core's `run_refuseWith`: the snapshot here is CAPTURED, not passed. -/
theorem EvalM.run_refuseUnsupported (what : String) (m : Mem) :
    (refuseUnsupported what : EvalM α) m
      = .error (.unsupported (.unsupported ()) what (some m)) := rfl

end Seam

/-! ### MEMORY INVARIANCE, and the algebra that makes it cheap -/

/-- A computation that cannot change memory: **whatever it answers**, the
memory it hands back is the memory it was handed.

The quantifier ranges over `r : Except Refusal α`, so this covers the
refusal branch too — which is not decoration. `ExceptT` OUTSIDE `StateT`
is the state-RETAINING order (`LeanModels/Core/Outcome.lean`), so a
refusal carries a memory, and a predicate that spoke only about success
would say nothing about the branch the layer order exists to keep
world-aware.

**A STRUCTURE, not a `def` returning `∀`, and the difference cost a
tenure.** As a `def` it unfolded under `intro` — so the closing tactic's
`intro` fired on `MemInvariant (…)` itself, stripped the predicate to a
raw `m' = m`, and every subsequent `apply` matched that instead of the
computation. Thirteen goals, one cause. A structure is opaque to `intro`
by construction, which is the property the tactic actually depends on.

> **A tactic that dispatches on a goal's HEAD needs the head to be
> stable; a `def` that unfolds to a binder has no stable head.** -/
structure MemInvariant {α : Type} (x : EvalM α) : Prop where
  /-- Whatever `x` answers, it hands back the memory it was handed. -/
  out : ∀ (m : Mem) (r : Except Refusal α) (m' : Mem), x m = .ok (r, m') → m' = m

namespace MemInvariant

variable {α β : Type}

theorem pure' (a : α) : MemInvariant (pure a : EvalM α) := by
  constructor
  intro m r m' h
  rw [SemMWith.run_pure] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem get' : MemInvariant (get : EvalM Mem) := by
  constructor
  intro m r m' h
  rw [SemMWith.run_get] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem throw' (e : Refusal) : MemInvariant (throw e : EvalM α) := by
  constructor
  intro m r m' h
  rw [SemMWith.run_throw] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem refuseUB' (f : MemFault) : MemInvariant (refuseUB f : EvalM α) := throw' (.memUB f)
theorem refuseValue' (u : UB) : MemInvariant (refuseValue u : EvalM α) := throw' (.valueUB u)
theorem refuseLibc' (n : String) : MemInvariant (refuseLibc n : EvalM α) := throw' (.libc n)

theorem refuseUnsupported' (what : String) :
    MemInvariant (refuseUnsupported what : EvalM α) := by
  constructor
  intro m r m' h
  rw [EvalM.run_refuseUnsupported] at h
  simp at h

theorem ite' {p : Prop} [Decidable p] {x y : EvalM α}
    (hx : MemInvariant x) (hy : MemInvariant y) :
    MemInvariant (if p then x else y) := by
  split <;> assumption

theorem bif' {p : Bool} {x y : EvalM α}
    (hx : MemInvariant x) (hy : MemInvariant y) :
    MemInvariant (if p then x else y) := by
  cases p <;> assumption

/-- The composition rule, and the refusal branch is where the layer order
becomes visible: the head's out-memory is `m` by `hx` applied **to the
refusal result**, which is exactly the quantifier `MemInvariant` carries. -/
theorem bind {x : EvalM α} {f : α → EvalM β}
    (hx : MemInvariant x) (hf : ∀ a, MemInvariant (f a)) : MemInvariant (x >>= f) := by
  constructor
  intro m r m' h
  cases hxm : x m with
  | error l =>
      rw [SemMWith.run_bind_loud hxm] at h
      simp at h
  | ok p =>
      obtain ⟨r₀, m₀⟩ := p
      have hm₀ : m₀ = m := hx.out m r₀ m₀ hxm
      cases r₀ with
      | error e =>
          rw [SemMWith.run_bind_raise hxm] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact h.2.symm.trans hm₀
      | ok a =>
          rw [SemMWith.run_bind_ok hxm] at h
          exact ((hf a).out m₀ r m' h).trans hm₀

/-- `map` needs no second opening: it is `pure`-after-`bind`. Present
because `simp` normalizes `x >>= fun a => pure (g a)` into `g <$> x`, so a
goal that started as a bind can arrive here wearing the other spelling. -/
theorem map' {x : EvalM α} (g : α → β) (hx : MemInvariant x) :
    MemInvariant (g <$> x) := by
  rw [map_eq_pure_bind]
  exact bind hx fun _ => pure' _

/-- Reading is invariant, and outside `storeAt` it is the ONLY way this
block reaches memory at all. -/
theorem readMem' (f : Mem → MRes α) (couldBeUninitializedRegister : Unit → Bool := fun _ => false) :
    MemInvariant (readMem f couldBeUninitializedRegister) := by
  refine bind get' fun m0 => ?_
  cases f m0 with
  | ok a => exact pure' a
  | error e =>
      cases e
      all_goals first
        | exact throw' _
        | exact ite' (refuseUB' _) (refuseUnsupported' _)

theorem evalCRes' (r : CRes CVal) : MemInvariant (evalCRes r) := by
  cases r
  · exact pure' _
  · exact refuseValue' _

theorem intTyOfNode' (structured : Option LeanModels.Clang.QualType) :
    MemInvariant (intTyOfNode structured) := by
  unfold intTyOfNode
  match structured.bind intTyOfStructured with
  | some _ => exact pure' _
  | none => exact refuseUnsupported' _

theorem intLiteralNode' (value : String)
    (structured : Option LeanModels.Clang.QualType) :
    MemInvariant (do
      let t ← intTyOfNode structured
      match value.toInt? with
      | some n => pure (CVal.int t n)
      | none => refuseUnsupported s!"integer literal spelling '{value}'") := by
  refine bind (intTyOfNode' structured) ?_
  intro t
  cases h : value.toInt? with
  | some n => exact pure' _
  | none => exact refuseUnsupported' _

theorem charLiteralNode' (value : String)
    (structured : Option LeanModels.Clang.QualType) :
    MemInvariant (do
      let t ← intTyOfNode structured
      match value.toInt? with
      | some n => pure (CVal.int t (if t == IntTy.int_ then charLiteralValue n else n))
      | none => refuseUnsupported s!"character literal spelling '{value}'") := by
  refine bind (intTyOfNode' structured) ?_
  intro t
  cases h : value.toInt? with
  | some n => exact pure' _
  | none => exact refuseUnsupported' _

theorem truthy' (v : CVal) : MemInvariant (truthy v) := by
  cases v <;> first | exact pure' _ | exact refuseUnsupported' _ | exact refuseUB' _

theorem asPtr' (v : CVal) : MemInvariant (asPtr v) := by
  cases v <;> first | exact pure' _ | exact refuseUnsupported' _ | exact refuseUB' _

theorem asInt' (v : CVal) : MemInvariant (asInt v) := by
  cases v <;> first | exact pure' _ | exact refuseUnsupported' _ | exact refuseUB' _

theorem loadCharacterAt' (p : Ptr) (t : IntTy)
    (couldBeUninitializedRegister : Unit → Bool := fun _ => false) :
    MemInvariant (loadCharacterAt p t couldBeUninitializedRegister) := by
  unfold loadCharacterAt
  apply bind (readMem' _)
  rintro ⟨_, object, offset⟩
  cases observed : object.bytes[offset]? with
  | none => simpa only [observed] using (readMem' (fun m => m.loadCharacter p t) couldBeUninitializedRegister)
  | some byte =>
      cases byte <;> simp only [observed]
      all_goals first
        | exact refuseUnsupported' _
        | exact readMem' _ _
        | exact bif' (readMem' _ _) (refuseUnsupported' _)

theorem loadAt' (alias : Mem.AliasModel) (p : Ptr) (ty : String) (size : Option Nat)
    (structured : Option LeanModels.Clang.QualType := none)
    (zeroNullPointer : Bool := false)
    (couldBeUninitializedRegister : Unit → Bool := fun _ => false) :
    MemInvariant (loadAt alias p ty size structured zeroNullPointer couldBeUninitializedRegister) := by
  unfold loadAt
  repeat
    first
    | exact readMem' _ _
    | exact loadCharacterAt' _ _ _
    | exact bind (readMem' _ _) fun _ => pure' _
    | exact bind (readMem' _ _) fun
        | some _ => pure' _
        | none => refuseUnsupported' _
    | exact refuseUnsupported' _
    | split

theorem intBinop' (op : String) (t : IntTy) (a b : Int) :
    MemInvariant (intBinop op t a b) := by
  first | simp only [intBinop] | rw [intBinop.eq_def]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseValue' _
    | exact refuseUB' _
    | exact refuseUnsupported' _
    | exact evalCRes' _

theorem float32Binop' (op : String) (a b : Float32.Model) :
    MemInvariant (float32Binop op a b) := by
  first | simp only [float32Binop] | rw [float32Binop.eq_def]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseValue' _
    | exact refuseUnsupported' _

theorem float64Binop' (op : String) (a b : Float.Model) :
    MemInvariant (float64Binop op a b) := by
  first | simp only [float64Binop] | rw [float64Binop.eq_def]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseValue' _
    | exact refuseUnsupported' _

theorem float32ToInt' (f : Float32.Model) (t : IntTy) :
    MemInvariant (float32ToInt f t) := by
  first | simp only [float32ToInt] | rw [float32ToInt.eq_def]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseValue' _

theorem float64ToInt' (f : Float.Model) (t : IntTy) :
    MemInvariant (float64ToInt f t) := by
  first | simp only [float64ToInt] | rw [float64ToInt.eq_def]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseValue' _

theorem floatLiteralValue' (bitsHex : Option String) (bitWidth : Option Nat) :
    MemInvariant (floatLiteralValue bitsHex bitWidth) := by
  simp only [floatLiteralValue]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseUnsupported' _

theorem floatCast' (v : CVal) (structured : Option LeanModels.Clang.QualType) :
    MemInvariant (floatCast v structured) := by
  simp only [floatCast]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseUnsupported' _

theorem evalArith' (ctx : Ctx) (op : String) (lv rv : CVal) (ty : String)
    (elemTy : Option String := none) (base : Option Expr := none)
    (structured : Option LeanModels.Clang.QualType := none) :
    MemInvariant (evalArith ctx op lv rv ty elemTy base structured) := by
  cases elemTy <;> cases base <;> cases structured <;> cases lv <;> cases rv <;>
    first | simp only [evalArith] | rw [evalArith.eq_def]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseValue' _
    | exact refuseUB' _
    | exact refuseUnsupported' _
    | exact float32Binop' _ _ _
    | exact float64Binop' _ _ _
    | exact intBinop' _ _ _ _
    | exact bind (readMem' _) fun _ => pure' _
    | exact bind (readMem' _) fun _ =>
        ite' (refuseUnsupported' _) (pure' _)
    | exact ite' (refuseUnsupported' _) (pure' _)

end MemInvariant

/-- Close a `MemInvariant` goal for a computation assembled out of the
memory-READING primitives alone.

Nothing here can unfold a recursive function by accident: the five
functions of the mutual block are well-founded definitions and therefore
irreducible, so an `evalExpr` obligation is closed by `assumption` from an
induction hypothesis, or it is not closed at all.

**Every `apply` runs `with_reducible`, and that is a COST fix, not a
style one.** At default transparency a failing `apply MemInvariant.evalArith'`
delta-unfolds `evalArith` and matches its nineteen-way `String` match
against the goal before giving up — a search this tactic runs at every one
of its steps, on every goal. Tenure 2 died of it: two `(deterministic)
timeout at whnf` errors on the two arms whose goals carry the deepest
terms (`sizeof`'s `Option.bind` through an opaque `Layout` field, and a
`String.toInt?`). At reducible transparency each of these lemmas matches
only when the goal's head IS the constant it names, so every failure is
one comparison instead of one unfolding.

> **A tactic assembled from `first | apply …` pays its whole alternative
> list at DEFAULT transparency on every goal; if the alternatives name
> non-reducible constants, the list is a search over their bodies.**

**`contradiction` is in the list for the UNREACHABLE arms.** When a clause
is opened through `eq_def` rather than its per-clause equation, `split`
produces one goal per arm of the WHOLE match — nineteen of which carry a
hypothesis equating two different constructors. They are not hard goals;
they simply have to be recognised as impossible, and `contradiction` is
the tactic that does it by `noConfusion`. Without it a fallback path that
opens more than it needs to leaves goals nothing else in the list can
speak to. -/
macro "mem_inv" : tactic => `(tactic|
  repeat (any_goals (first
    | assumption
    | contradiction
    | (with_reducible apply MemInvariant.pure')
    | (with_reducible apply MemInvariant.get')
    | (with_reducible apply MemInvariant.throw')
    | (with_reducible apply MemInvariant.refuseUB')
    | (with_reducible apply MemInvariant.refuseValue')
    | (with_reducible apply MemInvariant.refuseLibc')
    | (with_reducible apply MemInvariant.refuseUnsupported')
    | (with_reducible apply MemInvariant.readMem')
    | (with_reducible apply MemInvariant.intTyOfNode')
    | (with_reducible apply MemInvariant.truthy')
    | (with_reducible apply MemInvariant.asPtr')
    | (with_reducible apply MemInvariant.asInt')
    | (with_reducible apply MemInvariant.loadAt')
    | (with_reducible apply MemInvariant.intBinop')
    | (with_reducible apply MemInvariant.float32ToInt')
    | (with_reducible apply MemInvariant.float64ToInt')
    | (with_reducible apply MemInvariant.evalArith')
    | (with_reducible apply MemInvariant.ite')
    | (with_reducible apply MemInvariant.bif')
    | (with_reducible apply MemInvariant.bind)
    | (with_reducible apply MemInvariant.map')
    | (simp only [letFun])
    | intro _
    | split)))

/-- Open `evalExpr`'s clause at a KNOWN head. Two spellings because Lean
generates per-clause equations where the patterns are constructors and a
GUARDED default where they are not, and only one of the two fires in each
case; if neither opens the clause the proof below fails loudly. -/
macro "open_eval" : tactic => `(tactic| first | simp only [evalExpr] | rw [evalExpr.eq_def])

/-- The same for `evalLValue`, whose catch-all *is* the guarded default. -/
macro "open_lvalue" : tactic => `(tactic| first | simp only [evalLValue] | rw [evalLValue.eq_def])

/-! ### The address helpers

Stated with their sub-evaluations' invariance as HYPOTHESES, so neither
needs an induction of its own: both take strict SUBTERMS, which is the
same property that made the termination measure work. -/

theorem MemInvariant.memberAddr' {ctx : Ctx} {memberExpr base : Expr} {field : String} {arrow : Bool}
    {fieldTy : String} {recordId : Option DeclarationId}
    (hv : MemInvariant (evalExpr ctx base)) (hl : MemInvariant (evalLValue ctx base)) :
    MemInvariant (memberAddr ctx memberExpr base field arrow fieldTy recordId) := by
  first | simp only [memberAddr] | rw [memberAddr.eq_def]
  mem_inv

theorem MemInvariant.indexAddr' {ctx : Ctx} {base idx : Expr} {ty : String}
    (hb : MemInvariant (evalExpr ctx base)) (hi : MemInvariant (evalExpr ctx idx)) :
    MemInvariant (indexAddr ctx base idx ty) := by
  first | simp only [indexAddr] | rw [indexAddr.eq_def]
  mem_inv

/-! ### THE THEOREM

Strong induction on `Expr.size`, and the two functions are proved TOGETHER
because they are defined together. `evalArgs` never appears: `nodeIsPure`
makes a `call` node impure, so the arm that would reach it is vacuous —
which is the honest shape, since a call is precisely what this theorem
cannot speak for. -/

-- A twenty-constructor case analysis, each arm running a tactic search: the
-- default 200 000 is a PER-DECLARATION budget sized for ordinary proofs, and
-- this declaration is twenty of them. The budget is not the fix — the fix is
-- `mem_inv`'s `with_reducible`, which is what made the search cheap; this only
-- stops the sum of twenty cheap searches from hitting a single-proof ceiling.
set_option maxHeartbeats 1000000 in
private theorem memInvariant_core (ctx : Ctx) : ∀ (n : Nat) (e : Expr), e.size ≤ n →
    Expr.isPure e = true →
    MemInvariant (evalExpr ctx e) ∧ MemInvariant (evalLValue ctx e) := by
  intro n
  induction n with
  | zero =>
      intro e he _
      exact absurd (Expr.size_pos e) (by omega)
  | succ n ih =>
      intro e he hp
      have hnode := Expr.nodeIsPure_of_isPure hp
      cases e with
      | intLit value _ _ structuredType => exact ⟨by open_eval; exact MemInvariant.intLiteralNode' value structuredType, by open_lvalue; mem_inv⟩
      | boolLit _ _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | nullPtrLit _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | choose _ _ _ _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | charLit value _ _ structuredType => exact ⟨by open_eval; exact MemInvariant.charLiteralNode' value structuredType, by open_lvalue; mem_inv⟩
      | strLit _ _ _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | floatLit _ bitsHex bitWidth ty _ _ =>
          exact ⟨by open_eval; exact MemInvariant.floatLiteralValue' bitsHex bitWidth,
            by open_lvalue; mem_inv⟩
      | declRef _ _ _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | typeTrait _ _ _ _ _ _ _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | offsetOf _ _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | constExpr value sub ty span _ =>
          cases sub with
          | none => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
          | some sub =>
              have hsub : sub.size ≤ n := by
                change sub.subexprs.length ≤ n
                simp only [Expr.size, Expr.subexprs, List.length_cons] at he
                omega
              have hpure : Expr.isPure sub = true := by
                simp only [Expr.isPure, Expr.subexprs, List.all_cons,
                  Bool.and_eq_true] at hp
                exact hp.2
              obtain ⟨i1, i2⟩ := ih sub hsub hpure
              exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | vaArg ap ty span _ =>
          have hbad := Expr.nodeIsPure_of_isPure hp
          simp [Expr.nodeIsPure] at hbad
      | paren s _ _ _ =>
          obtain ⟨i1, i2⟩ := ih s (by simp only [Expr.size_paren] at he; omega)
            (Expr.isPure_paren hp)
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | exprWithCleanups s _ _ _ =>
          have hp' := hp
          simp only [Expr.isPure, Expr.subexprs, List.all_cons,
            Bool.and_eq_true] at hp'
          have hsub : Expr.isPure s = true := by
            exact hp'.2
          obtain ⟨i1, i2⟩ := ih s (by simp only [Expr.size_exprWithCleanups] at he; omega) hsub
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | materializeTemporary s _ _ _ =>
          have hp' := hp
          simp only [Expr.isPure, Expr.subexprs, List.all_cons,
            Bool.and_eq_true] at hp'
          have hsub : Expr.isPure s = true := by
            exact hp'.2
          obtain ⟨i1, i2⟩ := ih s (by simp only [Expr.size_materializeTemporary] at he; omega) hsub
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | implicitCast _ s _ _ _ =>
          obtain ⟨i1, i2⟩ := ih s (by simp only [Expr.size_implicitCast] at he; omega)
            (Expr.isPure_implicitCast hp)
          refine ⟨?_, by open_lvalue; mem_inv⟩
          open_eval
          apply MemInvariant.ite' <;>
            first | (simp [floatCast]; mem_inv) | exact MemInvariant.floatCast' _ _ | mem_inv
          all_goals (simp [loadBitFieldAt]; mem_inv)
      | cast _ s _ _ _ =>
          obtain ⟨i1, i2⟩ := ih s (by simp only [Expr.size_cast] at he; omega)
            (Expr.isPure_cast hp)
          refine ⟨?_, by open_lvalue; mem_inv⟩
          open_eval
          apply MemInvariant.ite' <;>
            first | (simp [floatCast]; mem_inv) | exact MemInvariant.floatCast' _ _ | mem_inv
          all_goals (simp [loadBitFieldAt]; mem_inv)
      | member b f a fieldTy span recordId structuredType =>
          obtain ⟨i1, i2⟩ := ih b (by simp only [Expr.size_member] at he; omega)
            (Expr.isPure_member hp)
          let memberExpr := Expr.member b f a fieldTy span recordId structuredType
          have hma : MemInvariant (memberAddr ctx memberExpr b f a fieldTy recordId) :=
            MemInvariant.memberAddr' i1 i2
          exact ⟨by open_eval; simp [loadBitFieldAt]; mem_inv,
            by open_lvalue; mem_inv⟩
      | index b i ty _ _ =>
          obtain ⟨b1, _⟩ := ih b (by simp only [Expr.size_index] at he; omega)
            (Expr.isPure_index_base hp)
          obtain ⟨i1, _⟩ := ih i (by simp only [Expr.size_index] at he; omega)
            (Expr.isPure_index_idx hp)
          have hia : MemInvariant (indexAddr ctx b i ty) := MemInvariant.indexAddr' b1 i1
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | cond cc tt ee _ _ _ =>
          obtain ⟨c1, _⟩ := ih cc (by simp only [Expr.size_cond] at he; omega)
            (Expr.isPure_cond_c hp)
          obtain ⟨t1, _⟩ := ih tt (by simp only [Expr.size_cond] at he; omega)
            (Expr.isPure_cond_t hp)
          obtain ⟨e1, _⟩ := ih ee (by simp only [Expr.size_cond] at he; omega)
            (Expr.isPure_cond_e hp)
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | binop op l r _ _ _ =>
          obtain ⟨l1, _⟩ := ih l (by simp only [Expr.size_binop] at he; omega)
            (Expr.isPure_binop_l hp)
          obtain ⟨r1, _⟩ := ih r (by simp only [Expr.size_binop] at he; omega)
            (Expr.isPure_binop_r hp)
          simp only [Expr.nodeIsPure] at hnode
          refine ⟨?_, by open_lvalue; mem_inv⟩
          -- The `=` arm is the one clause of this constructor that stores,
          -- and `hnode` is exactly the fact that excludes it.
          open_eval
          repeat (any_goals split)
          all_goals first | (mem_inv; done) | simp_all
      | unop op s post _ _ _ =>
          obtain ⟨s1, s2⟩ := ih s (by simp only [Expr.size_unop] at he; omega)
            (Expr.isPure_unop hp)
          simp only [Expr.nodeIsPure] at hnode
          constructor
          · -- `++`/`--` store; `hnode` excludes both spellings.
            open_eval
            repeat (any_goals split)
            all_goals first | (simp_all [loadBitFieldAt, storeBitField]; mem_inv; done) | (mem_inv; done) | simp_all
          · open_lvalue
            repeat (any_goals split)
            all_goals first | (mem_inv; done) | simp_all
      -- The five impure heads. Each arm is vacuous, and each is vacuous for
      -- a DIFFERENT reason worth keeping: a call is opaque; an assignment
      -- and an increment store; aggregate initialization writes through the
      -- layout; an out-of-tier node is unknown rather than harmless.
      | call _ _ _ _ _ => simp [Expr.nodeIsPure] at hnode
      | compoundAssign _ _ _ _ _ _ _ _ => simp [Expr.nodeIsPure] at hnode
      | initList _ _ _ _ _ => simp [Expr.nodeIsPure] at hnode
      | arrayInitList _ _ _ _ _ _ => simp [Expr.nodeIsPure] at hnode
      | designatedUpdate _ _ _ _ _ => simp [Expr.nodeIsPure] at hnode
      | implicitValueInit _ _ _ => simp [Expr.nodeIsPure] at hnode
      | compoundLit _ _ _ _ => simp [Expr.nodeIsPure] at hnode
      | unsupported _ _ _ => simp [Expr.nodeIsPure] at hnode

/-- **RUNG A.** A pure expression's evaluation leaves memory exactly as it
found it — on the value branch AND on the refusal branch. -/
theorem evalExpr_memInvariant (ctx : Ctx) (e : Expr) (h : Expr.isPure e = true) :
    MemInvariant (evalExpr ctx e) :=
  (memInvariant_core ctx e.size e (Nat.le_refl _) h).1

/-- The same in LVALUE position: taking an address does not write either. -/
theorem evalLValue_memInvariant (ctx : Ctx) (e : Expr) (h : Expr.isPure e = true) :
    MemInvariant (evalLValue ctx e) :=
  (memInvariant_core ctx e.size e (Nat.le_refl _) h).2

/-- **The `J.1(16)`-facing corollary**: an argument LIST whose every member
is pure is evaluated without touching memory. At a call site whose
siblings are pure, the effectful argument is therefore the only writer —
whichever order §6.5.3.3p10 lets the implementation choose.

That is the SIBLING half, and it is the half a syntax check decides. The
other half — that the one effectful argument does not write what the
siblings READ — is Rung B, and nothing here is evidence for it. -/
theorem evalArgs_memInvariant (ctx : Ctx) : ∀ (es : List Expr),
    es.all Expr.isPure = true → MemInvariant (evalArgs ctx es) := by
  intro es
  induction es with
  | nil =>
      intro _
      first | simp only [evalArgs] | rw [evalArgs.eq_def]
      exact MemInvariant.pure' _
  | cons e es ihs =>
      intro h
      simp only [List.all_cons, Bool.and_eq_true] at h
      first | simp only [evalArgs] | rw [evalArgs.eq_def]
      exact MemInvariant.bind (evalExpr_memInvariant ctx e h.1) fun _ =>
        MemInvariant.bind (ihs h.2) fun _ => MemInvariant.pure' _


/-! ## RUNG B — §6.5.3.3p10 / `J.1(16)`: the order becomes a PARAMETER, and
the 208 fall

Rung A proved that a pure expression does not WRITE. This section spends
that, and the spending splits the same way the obligation does:

* **the 208 multi-argument sites whose every argument is pure** — settled
  here, unconditionally. The argument is short once purity is in hand:
  memory never changes, so every argument's value is a function of the
  memory the CALL started in, and a function of that memory cannot depend
  on when it was applied;
* **the 7** — one nested call each, and whether it writes what its
  siblings read. That is an effect summary, it is **not** proved here, and
  it appears below as a NAMED hypothesis with a theorem saying exactly
  what discharging it buys.

**THE ORDER PARAMETER TURNED OUT NOT TO NEED A TAGGED EVALUATOR.** The
plan was an `evalArgsAt` over position-tagged arguments, so that two
orders could be compared. Purity makes it unnecessary: once every argument
is a function of ONE memory, "the value of argument `i`" is
`valOf? ctx m eᵢ` no matter which walk produced it, and the ∀-order
statement is about `List.Perm` directly. The tagging existed to carry
information across the reordering, and Rung A had already made that
information order-free.

> **A parameter you were going to thread is a sign the property is not yet
> stated at the right level: when the order stops being observable, the
> machinery for observing it stops being needed.**

**AND THE OBSERVABLE IS THE ANSWER, NEVER THE RUN.** Every theorem below
takes the canonical run's success as a HYPOTHESIS rather than assuming it
in prose, and that is not fussiness. Two orders can disagree about *which
refusal is reported* whenever more than one argument would refuse —
`f(g(), h())` with both refusing answers with `g`'s cause left-to-right
and `h`'s right-to-left, and §3.1 never pools the causes, so the
difference is visible in the verdict.

> **Order-independence is a property of the VALUE and the MEMORY, never of
> the trace: a ∀-order theorem quantified over the run would be false for
> a reason that has nothing to do with sequencing.** -/

/-- The value an expression yields at a given memory, or `none` if it
yields none — it refused, or the model halted.

This is the function the whole ∀-order argument turns on. `evalExpr ctx e`
IS a function of the memory it is handed, so if the memory is the same
then so is the answer, and *when* the argument ran cannot enter into it.
Saying that requires naming the function. -/
def valOf? (ctx : Ctx) (m : Mem) (e : Expr) : Option CVal :=
  match evalExpr ctx e m with
  | .ok (.ok v, _) => some v
  | _ => none

theorem valOf?_of_run {ctx : Ctx} {m m' : Mem} {e : Expr} {v : CVal}
    (h : evalExpr ctx e m = .ok (.ok v, m')) : valOf? ctx m e = some v := by
  simp only [valOf?, h]

/-- The converse, **for a pure expression**, and purity is exactly what
makes it a converse rather than something weaker: it pins the out-memory
to the in-memory, so the whole run can be reconstructed and not just its
value. -/
theorem run_of_valOf? {ctx : Ctx} {m : Mem} {e : Expr} {v : CVal}
    (hp : Expr.isPure e = true) (h : valOf? ctx m e = some v) :
    evalExpr ctx e m = .ok (.ok v, m) := by
  rw [valOf?] at h
  split at h
  · rename_i v₀ m₀ heq
    have hm : m₀ = m := (evalExpr_memInvariant ctx e hp).out m _ m₀ heq
    simp only [Option.some.injEq] at h
    subst h
    subst hm
    exact heq
  · simp at h

/-! ### The argument walk, opened once

Two lemmas — build a `cons` step and take one apart — so that neither
theorem below has to unfold the monad again. This is `Core` §4's discipline
one level up: **one opening, and the rest are corollaries.** -/

theorem evalArgs_nil (ctx : Ctx) (m : Mem) :
    evalArgs ctx [] m = .ok (.ok [], m) := by
  simp only [evalArgs]
  exact SemMWith.run_pure _ _

theorem evalArgs_cons_ok {ctx : Ctx} {e : Expr} {es : List Expr} {m m₀ m₁ : Mem}
    {v : CVal} {vs : List CVal}
    (he : evalExpr ctx e m = .ok (.ok v, m₀))
    (hes : evalArgs ctx es m₀ = .ok (.ok vs, m₁)) :
    evalArgs ctx (e :: es) m = .ok (.ok (v :: vs), m₁) := by
  simp only [evalArgs]
  rw [SemMWith.run_bind_ok he, SemMWith.run_bind_ok hes, SemMWith.run_pure]

/-- Taking a successful walk apart: the head ran, the tail ran from where
the head left off, and the answer is their cons. **A successful `cons` has
no other shape** — which is what makes the case analysis below a case
analysis rather than a guess. -/
theorem evalArgs_cons_inv {ctx : Ctx} {e : Expr} {es : List Expr} {m m₁ : Mem}
    {vs' : List CVal} (h : evalArgs ctx (e :: es) m = .ok (.ok vs', m₁)) :
    ∃ (v : CVal) (m₀ : Mem) (vs : List CVal),
      evalExpr ctx e m = .ok (.ok v, m₀) ∧ evalArgs ctx es m₀ = .ok (.ok vs, m₁)
        ∧ vs' = v :: vs := by
  simp only [evalArgs] at h
  cases he : evalExpr ctx e m with
  | error l => rw [SemMWith.run_bind_loud he] at h; simp at h
  | ok pr =>
      obtain ⟨r, m₀⟩ := pr
      cases r with
      | error r' => rw [SemMWith.run_bind_raise he] at h; simp at h
      | ok v =>
          rw [SemMWith.run_bind_ok he] at h
          cases hts : evalArgs ctx es m₀ with
          | error l => rw [SemMWith.run_bind_loud hts] at h; simp at h
          | ok pr2 =>
              obtain ⟨r2, m₂⟩ := pr2
              cases r2 with
              | error r2' => rw [SemMWith.run_bind_raise hts] at h; simp at h
              | ok tvs =>
                  rw [SemMWith.run_bind_ok hts, SemMWith.run_pure] at h
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨hl, hm⟩ := h
                  subst hm
                  subst hl
                  exact ⟨v, m₀, tvs, rfl, hts, rfl⟩

/-! ### The pointwise law — and it is the whole of the 208

An all-pure argument list is evaluated **at one memory**, the one the call
started in, however long the list is. So the list's answer is
`valOf? ctx m` applied pointwise, and nothing about the walk survives into
it. -/

/-- **THE POINTWISE LAW.** A pure argument list's values are `valOf? ctx m`
applied to it, at the INCOMING memory, and the memory comes back
untouched. -/
theorem evalArgs_pure_pointwise (ctx : Ctx) : ∀ (es : List Expr),
    es.all Expr.isPure = true → ∀ (m : Mem) (vs : List CVal) (m' : Mem),
      evalArgs ctx es m = .ok (.ok vs, m') →
        m' = m ∧ es.map (valOf? ctx m) = vs.map some := by
  intro es
  induction es with
  | nil =>
      intro _ m vs m' h
      rw [evalArgs_nil] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hl, hm⟩ := h
      subst hl
      exact ⟨hm.symm, rfl⟩
  | cons e es ih =>
      intro hp m vs m' h
      simp only [List.all_cons, Bool.and_eq_true] at hp
      obtain ⟨v, m₀, tvs, he, hts, hvs⟩ := evalArgs_cons_inv h
      have hm₀ : m₀ = m := (evalExpr_memInvariant ctx e hp.1).out m _ m₀ he
      rw [hm₀] at hts
      obtain ⟨htm, htv⟩ := ih hp.2 m tvs m' hts
      subst hvs
      exact ⟨htm, by simp only [List.map_cons, htv, valOf?_of_run he]⟩

/-- The converse at a GIVEN value list: a pure argument list whose values
`valOf? ctx m` supplies really does run to them, in whatever order it is
written. **This is the half that makes the claim about EVERY order** and
not only about the ones that happen to succeed. -/
theorem evalArgs_pure_ofPointwise (ctx : Ctx) : ∀ (es : List Expr),
    es.all Expr.isPure = true → ∀ (m : Mem) (vs : List CVal),
      es.map (valOf? ctx m) = vs.map some →
        evalArgs ctx es m = .ok (.ok vs, m) := by
  intro es
  induction es with
  | nil =>
      intro _ m vs h
      cases vs with
      | nil => exact evalArgs_nil ctx m
      | cons w ws => simp at h
  | cons e es ih =>
      intro hp m vs h
      simp only [List.all_cons, Bool.and_eq_true] at hp
      cases vs with
      | nil => simp at h
      | cons v ws =>
          simp only [List.map_cons, List.cons.injEq] at h
          exact evalArgs_cons_ok (run_of_valOf? hp.1 h.1) (ih hp.2 m ws h.2)

/-! ### ∀ ORDER, for the 208 -/

/-- **THE ∀-ORDER THEOREM for an all-pure argument list.** Any two orders
agree on the values — as multisets, which is what "the same arguments in a
different order" means — and both leave the memory they were handed.

`hperm` is an ARBITRARY permutation and the conclusion is an equation, so
this is the unconditional discharge of the **208 of 215** multi-argument
call sites whose every argument is pure. No effect summary appears, because
no effects do. -/
theorem evalArgs_orderIndependent (ctx : Ctx) {es fs : List Expr} {vs ws : List CVal}
    {m m₁ m₂ : Mem} (hperm : es.Perm fs) (hp : es.all Expr.isPure = true)
    (h₁ : evalArgs ctx es m = .ok (.ok vs, m₁))
    (h₂ : evalArgs ctx fs m = .ok (.ok ws, m₂)) :
    m₁ = m ∧ m₂ = m ∧ (vs.map some).Perm (ws.map some) := by
  have hpf : fs.all Expr.isPure = true := by
    simp only [List.all_eq_true] at hp ⊢
    intro x hx
    exact hp x (hperm.mem_iff.mpr hx)
  obtain ⟨hm₁, hv⟩ := evalArgs_pure_pointwise ctx es hp m vs m₁ h₁
  obtain ⟨hm₂, hw⟩ := evalArgs_pure_pointwise ctx fs hpf m ws m₂ h₂
  refine ⟨hm₁, hm₂, ?_⟩
  rw [← hv, ← hw]
  exact hperm.map _

/-- The two-argument instance, spelled out because **four of the seven
sites have arity two** and because it is the one shape where the other
order can be exhibited rather than merely compared: the swapped call runs,
and it runs to the swapped values. -/
theorem evalArgs_pair_swap (ctx : Ctx) (a b : Expr) {m m₁ : Mem} {va vb : CVal}
    (ha : Expr.isPure a = true) (hb : Expr.isPure b = true)
    (h : evalArgs ctx [a, b] m = .ok (.ok [va, vb], m₁)) :
    m₁ = m ∧ evalArgs ctx [b, a] m = .ok (.ok [vb, va], m) := by
  have hall : [a, b].all Expr.isPure = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true]
    exact ⟨ha, hb, trivial⟩
  obtain ⟨hm, hv⟩ := evalArgs_pure_pointwise ctx [a, b] hall m [va, vb] m₁ h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hv
  refine ⟨hm, evalArgs_pure_ofPointwise ctx [b, a] ?_ m [vb, va] ?_⟩
  · simp only [List.all_cons, List.all_nil, Bool.and_eq_true]
    exact ⟨hb, ha, trivial⟩
  · simp only [List.map_cons, List.map_nil, List.cons.injEq]
    exact ⟨hv.2.1, hv.1, trivial⟩

/-! ### THE 7 — the residue, as an OBLIGATION rather than a paragraph

At each of the seven sites `docs/c23-spec-mirror.md` §5.3 names, exactly
one argument is impure and it is a nested call. Rung A retires the
siblings' half; what remains is whether the callee writes what a sibling
READS, and this tier has no read-set.

So it is written down as a predicate, and the theorem below says exactly
what discharging it buys. That is inch 5's move reused: **make the
property statable about a function first, and the discharge becomes a
separate nameable step instead of a paragraph.** -/

/-- **THE EFFECT SUMMARY, as an obligation.** Running `x` leaves `e`'s
value alone.

Stated OBSERVATIONALLY, over `valOf?`, rather than as a footprint — because
the observable is what Thomas's ∀-order ruling quantifies over, and a
footprint would be a strictly stronger claim than the obligation needs. A
callee that writes a location the sibling reads and writes it back is
non-interfering here and would not be under a footprint reading; the
standard asks about the value, so this does too. -/
def NonInterfering {α : Type} (ctx : Ctx) (x : EvalM α) (e : Expr) : Prop :=
  ∀ (m : Mem) (a : α) (m' : Mem), x m = .ok (.ok a, m') → valOf? ctx m' e = valOf? ctx m e

/-- **WHAT THE EFFECT SUMMARY BUYS**, at the seven sites' shape: two
arguments, the first pure, the second doing whatever it likes.

Read which hypothesis carries which half. **`hp` is Rung A** — the pure
sibling does not write, so the call still starts from `m` when it runs
second, which is why `hec` can be stated at `m` at all. **`hni` is the
residue** — the call does not disturb what the sibling reads, so the
sibling still answers `vp` when it runs second. Neither implies the other
and the theorem needs both; that is the honest shape of a half-discharged
obligation. -/
theorem evalArgs_pair_oneEffect (ctx : Ctx) (p c : Expr) {m m₀ m₁ : Mem} {vp vc : CVal}
    (hp : Expr.isPure p = true) (hni : NonInterfering ctx (evalExpr ctx c) p)
    (hep : evalExpr ctx p m = .ok (.ok vp, m₀))
    (hec : evalExpr ctx c m = .ok (.ok vc, m₁)) :
    evalArgs ctx [p, c] m = .ok (.ok [vp, vc], m₁)
      ∧ evalArgs ctx [c, p] m = .ok (.ok [vc, vp], m₁) := by
  -- Rung A: the pure argument's out-memory IS its in-memory.
  have hm₀ : m₀ = m := (evalExpr_memInvariant ctx p hp).out m _ m₀ hep
  rw [hm₀] at hep
  refine ⟨evalArgs_cons_ok hep (evalArgs_cons_ok hec (evalArgs_nil ctx m₁)), ?_⟩
  -- The residue: after the call, the sibling still answers what it answered.
  have hsame : valOf? ctx m₁ p = some vp := by
    rw [hni m vc m₁ hec]
    exact valOf?_of_run hep
  exact evalArgs_cons_ok hec
    (evalArgs_cons_ok (run_of_valOf? hp hsame) (evalArgs_nil ctx m₁))

/-- **AND THE HALF THAT IS FREE.** A pure argument is non-interfering with
anything — including itself — so the seven sites' hypothesis is only ever
about the ONE impure argument. This is what makes the residue seven
obligations and not fourteen. -/
theorem nonInterfering_of_isPure {ctx : Ctx} {x : Expr} {e : Expr}
    (hx : Expr.isPure x = true) : NonInterfering ctx (evalExpr ctx x) e := by
  intro m a m' h
  have : m' = m := (evalExpr_memInvariant ctx x hx).out m _ m' h
  rw [this]

#print axioms evalArgs_pure_pointwise
#print axioms evalArgs_orderIndependent
#print axioms evalArgs_pair_swap
#print axioms evalArgs_pair_oneEffect

#print axioms evalExpr_memInvariant
#print axioms evalLValue_memInvariant
#print axioms evalArgs_memInvariant

end LeanModels.C.C23
