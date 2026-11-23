import LeanModels.C.C23.Expr

/-!
# §6.8 Statements and blocks — M2 inch 4

C23 (N3220) §6.8. Citations follow `docs/c23-spec-mirror.md`; refusals
name their Annex J.2 index.

## Fuel arrives HERE, and the census is why

`Expr.lean` is fuel-free and says so at length. Statements are not.
Measured on the shipped corpus:

| | |
| --- | ---: |
| loops (`for` 50, `do` 29, `while` 5) | **84** |
| …containing a call | 64 |
| **…containing NO call at all** | **20** |

**It is the loop, not the call, that forces fuel** — those 20 need it
just the same — which is what corrected the inch-3 draft's "fuel arrives
at inch 5". `execStmt` therefore takes a fuel argument and recurses on it
at exactly ONE place: the loop step. Every other statement recurses
structurally on `Stmt`, so the fuel-free reasoning of inch 3 keeps
working underneath.

The `∃ n, ∀ fuel ≥ n, … = .ok …` threshold form
(`docs/c-semantics-design.md` §4.2) is assembled AROUND `execStmt`.
`fuelMono` — that more fuel never changes a decided answer — is stated
and proved below, because it is the lemma every later threshold argument
rests on.

## TIMEOUT is not a refusal, so it does not live in `Except`

`docs/c23-goal.md` §3: *"TIMEOUT — fuel exhausted. The only exhaustion
outcome; never conflated with REFUSE."* The Python tier's `Run` agrees
structurally: `.ok` and `.exn` carry state, **`.timeout` carries none**,
because a timeout is not an observation of anything.

So the stack gains a base:

```
ExecM α := SemMWith Mem Refusal CDetail Mem α
        = ExceptT Refusal (StateT Mem (Except (Loud CDetail Mem))) α
```

where Core's `Loud` carries fuel exhaustion and the out-of-tier frontier,
and nothing else. A timeout discards
the memory, correctly — there is no world to report.

## WHERE REFUSAL LIVES — RULED, at `docs/family-architecture.md` §3.4

This file first argued that `unsupported` should ride in `ExceptT`
(state-carrying), against Python's `Run` and the ES lane's `Halt`, so an
inch-6 REFUSE row could say what had happened by the time the model
declined.

**The ruling went the other way, and this lane's own census is part of
why.** Putting a refusal in `ExceptT` makes it catchable in principle,
and the implicit defence was that nothing in C intercepts control flow.
The corpus refutes that: **`setjmp` 2, `longjmp` 2, 5 `jmp_buf`
objects** — and signal handlers in the language at large. Inside `ρ`,
"no catch reaches a refusal" is a per-language, per-construct proof
obligation; uncatchability belongs to the definition.

So `unsupported` lives in Core's `Loud` base, and the diagnostic need
is met the better way: **`Loud.unsupported` carries a structured payload
— the cause, plus an OPTIONAL memory snapshot captured AT the refusal
site.** §3.4's existing law pays for it, because every refusal already
routes through a NAMED primitive with its own `@[spec]` lemma, and that
primitive performs the `get` itself (`refuseUnsupported`), so no call
site can forget to.

**Two guards, both structural rather than advisory**: the snapshot is
optional, and it is NEVER an observable — `Halt`'s `BEq` ignores it, and
`Outcome`, which is what a scoreboard compares, has nowhere to put a
`Mem` at all.

`Halt` carrying `timeout` with no state was already aligned and the
ruling confirms it on the merits: state at fuel exhaustion would invite
treating a TIMEOUT as an observation.
-/

namespace LeanModels.C.C23

open LeanModels.C (Expr Stmt Decl)

/-! ## The monad

`Loud` and the stack are `Core`'s now (`LeanModels/Core/Outcome.lean`),
so statements and expressions run in the SAME stack — `ExecM` is `EvalM`.
That is not a coincidence to tidy away: it is what the ruling bought. An
expression cannot time out (inch 3 is fuel-free) and a statement can, but
neither can catch a refusal, so one type serves both. -/

/-- The statement evaluator's monad — the same stack expressions use. -/
abbrev ExecM (α : Type) := EvalM α

/-- Run a statement against a starting memory. -/
def ExecM.run (m : Mem) (x : ExecM α) :
    Except (Loud CDetail Mem) (Except Refusal α × Mem) :=
  EvalM.run m x

/-- The verdict, in `docs/c23-goal.md` §3's vocabulary. -/
def ExecM.verdict (m : Mem) (x : ExecM α) : Outcome α := EvalM.verdict m x

/-- Fuel exhaustion, as a named primitive — never a bare `throw`, and not
a `Refusal` at all. Carries no state: a timeout is not an observation. -/
def exhausted : ExecM α := fun _ => .error .timeout

/-! ## §6.8.7 — how a statement can finish

A C statement does not simply complete: it can leave its block in five
ways, and the enclosing construct decides what each one means. -/

/-- The completion of a statement (§6.8.7). -/
inductive Flow where
  /-- Fell off the end. -/
  | normal
  /-- §6.8.7.3 `break` — 8 sites. -/
  | brk
  /-- §6.8.7.2 `continue` — 6 sites. -/
  | cont
  /-- §6.8.7.4 `return`, with a value at 98 of its 103 sites. -/
  | ret (value : Option CVal)
  /-- §6.8.7.1 `goto` — 7 sites reaching exactly 3 labels, every one a
  FORWARD jump within the same function. A `Flow.goto` propagating
  outward to a labelled statement serves that shape; a general `goto`
  needs a CFG, and the census says this corpus does not have one. -/
  | goto (label : String)
deriving Repr, Inhabited, BEq

/-- Does this completion escape the enclosing block? -/
def Flow.escapes : Flow → Bool
  | .normal => false
  | _ => true

/-! ## Reaching inch 3

`ExecM` IS `EvalM`, so there is no lift — the ruling that put `Halt`
underneath both is what removed it. `liftEval` remains as a name, because
naming the boundary is worth more than saving a line: it marks every
place a statement reaches into the expression layer. -/

/-- Reach into the expression evaluator. The identity, deliberately. -/
@[inline] def liftEval (x : EvalM α) : ExecM α := x

/-- Evaluate an expression for its value. -/
def evalE (ctx : Ctx) (e : Expr) : ExecM CVal := liftEval (evalExpr ctx e)

/-- Evaluate an expression for its truth (§6.8.5, §6.8.6: a controlling
expression is compared unequal to 0). -/
def evalCond (ctx : Ctx) (e : Expr) : ExecM Bool :=
  liftEval (do let v ← evalExpr ctx e; truthy v)

/-! ## §6.7.11 — initialization of omitted members

The original census reported every corpus initializer as full. That claim
missed Clang's `array_filler` representation and is not evidence that partial
initialization is absent. §6.7.11p10 initializes unmentioned members as
objects with static storage duration, i.e. to zero.

The interpreter implements this rule and tests partial initializers against
the native compiler.

§6.7.11p10–11 directs zero-initialization by type. An unmentioned
pointer member receives a null pointer value, regardless of the target's
byte representation for null. -/

private def bitFieldInitValue (ctx : Ctx) : Option Expr → ExecM CVal
  | none | some (.implicitValueInit ..) => pure (.int IntTy.int_ 0)
  | some e => evalE ctx e

private def initBitField (ctx : Ctx) (p : Ptr) (declaration : Option DeclarationId)
    (name ty : String) (offsetBits width : Nat) (initializer : Option Expr) : ExecM Unit := do
  let structured := declaration.bind (fun did => ctx.layout.fieldStructuredDecl did name)
  let value ← bitFieldInitValue ctx initializer
  let _ ← liftEval (storeBitField ty (Mem.member p (offsetBits / 8)) offsetBits width structured value)
  pure ()

/-- C23 §6.7.11p20 orders initialization, while p24 leaves initializer
expression evaluation order open. These expressions cannot observe the
object under initialization or perform side effects. Compose only their
known bits, then commit shared bytes together. -/
private def bitFieldInitBits (ctx : Ctx) (ty : String) (declaration : Option DeclarationId) :
    List (String × String) → List Expr → ExecM (Nat × Nat)
  | [], [] => pure (0, 0)
  | [], _ :: _ => refuseUnsupported "more initializers than structure members"
  | (name, fieldTy) :: rest, initializers => do
      if name.isEmpty then
        bitFieldInitBits ctx ty declaration rest initializers
      else
        let some (offset, width) := ctx.layout.fieldBitsDeclAt declaration ty name
          | refuseUnsupported s!"no bit-field layout for '{name}'"
        let structured := declaration.bind (fun did => ctx.layout.fieldStructuredDecl did name)
        let some t := bitFieldIntTy structured width
          | refuseUnsupported (bitFieldTypeError structured fieldTy width)
        let value ← bitFieldInitValue ctx initializers.head?
        let (_, n) ← liftEval (asInt value)
        let (laterMask, laterBits) ← bitFieldInitBits ctx ty declaration rest initializers.tail
        let factor := 2 ^ offset
        let mask := (2 ^ width - 1) * factor
        if mask &&& laterMask != 0 then
          refuseUnsupported "overlapping bit-field layout in structure initializer"
        let bits := bitFieldResidue t width n * factor
        pure (mask ||| laterMask, bits ||| laterBits)

private def independentBitFieldInitializer : Expr → Bool
  | .implicitValueInit .. => true
  | e => Expr.isPure e && (readKeys e).isEmpty

private def initBitFieldRecord (ctx : Ctx) (p : Ptr) (ty : String)
    (declaration : Option DeclarationId) (members : List (String × String))
    (initializers : List Expr) : ExecM Unit := do
  let some size := ctx.layout.sizeAt declaration ty
    | refuseUnsupported s!"no layout for bit-field record '{ty}'"
  let (mask, bits) ← bitFieldInitBits ctx ty declaration members initializers
  if mask ≥ 256 ^ size then
    refuseUnsupported "bit-field extent exceeds its record layout"
  let old ← liftEval (readMem (fun m => m.loadBytes p size))
  match mergeBitFieldBytes old mask bits with
  | some bytes => liftEval (writeMem (fun m => m.storeBytes p bytes))
  | none => refuseUnsupported "partly initialized bit-field byte"

private def initializationType (layout : Layout)
    (structured : Option LeanModels.Clang.QualType) (declaration : Option LeanModels.C.DeclarationId) :
    Option LeanModels.Clang.QualType :=
  (structured.orElse (fun _ => declaration.bind layout.structuredType)).bind
    (LeanModels.Clang.QualType.resolveTypedefs
      (fun handle => layout.structuredType { value := handle.value }) 32)

private def initializationSize (layout : Layout) (type : LeanModels.Clang.QualType) :
    Option Nat :=
  objectSizeOfStructured type (fun handle => layout.recordSizeDecl { value := handle.value })

private def initializationStride (layout : Layout) (declaration : Option LeanModels.C.DeclarationId)
    (elementType : LeanModels.Clang.QualType) : Option Nat :=
  (declaration.bind layout.elementSizeDecl).orElse (fun _ => initializationSize layout elementType)

private def initializerHasEffects (ctx : Ctx) (expression : Expr) : Bool :=
  mayWrite ctx expression || !(directWriteTargets expression).isEmpty ||
    (expression.subexprs false).any fun
      | .vaArg .. => true
      | .implicitCast "LValueToRValue" source .. | .cast "LValueToRValue" source .. =>
          match source.structuredType? with
          | some (.qualified _ isVolatile _) => isVolatile
          | _ => false
      | _ => false

/-- N3220 §6.7.11p24 leaves the order of initializer expression evaluation
open. The admitted lists either have no effects, or have one effectful
initializer and no other access to stored values. -/
private def checkInitializerOrder (ctx : Ctx) (declaration : Option LeanModels.C.DeclarationId)
    (initializers : List Expr) : ExecM Unit := do
  let effectful := initializerHasEffects ctx
  if initializers.any effectful &&
      initializers.countP (fun expression => effectful expression || !(readKeys expression).isEmpty) > 1 then
    refuseUnsupported "initializer evaluations have an unspecified order"
  if let some objectId := declaration then
    let mentionsObject := fun (expression : Expr) =>
      (expression.subexprs false).any fun
        | .declRef (some id) .. => id == objectId
        | _ => false
    let usesObject := fun (expression : Expr) =>
      (expression.subexprs false).any fun
        | .implicitCast "LValueToRValue" sub .. | .cast "LValueToRValue" sub .. =>
            mentionsObject sub
        | .call _ args .. => args.any mentionsObject
        | .binop "=" lhs .. | .compoundAssign _ lhs .. => mentionsObject lhs
        | .unop "++" sub .. | .unop "--" sub .. | .unop "*" sub .. => mentionsObject sub
        | _ => false
    if initializers.any usesObject then
      refuseUnsupported "initializer may access the object under initialization"

/-- Resolve a member of the canonical record. Its FieldDecl supplies any
member-specific layout, and the type carried by that field preserves the
shape of a nested array or record. -/
private def initializerField (layout : Layout) (owner : LeanModels.C.DeclarationId)
    (name : String) : Option (Nat × LeanModels.Clang.QualType × Option LeanModels.C.DeclarationId) := do
  let offset ← layout.fieldOffDecl owner name
  let field := layout.fieldDecl owner name
  let type ← initializationType layout (layout.fieldStructuredDecl owner name) field
  return (offset, type, field)

/-- N3220 §6.7.11p11 gives a default-initialized structure zero
padding. Leave complete named member ranges untouched for the recursive
initializer. In particular, a member which is a union retains its own
inactive bytes. Named bit-fields and the padding in their storage bytes
all start at zero. -/
private def zeroStructurePadding (ctx : Ctx) (p : Ptr) (owner : LeanModels.C.DeclarationId)
    (size : Nat) (members : List (String × String)) : ExecM Unit := do
  let zeroRange := fun start count =>
    if count == 0 then pure ()
    else liftEval (writeMem (fun m => m.storeBytes (Mem.member p start)
      (List.replicate count (CByte.conc 0))))
  let occupied ← members.foldlM (init := 0) fun cursor (name, _) => do
    if (ctx.layout.fieldBitsDecl owner name).isSome || ctx.layout.flexibleFieldDecl owner name then
      pure cursor
    else
      let some (offset, type, _) := initializerField ctx.layout owner name
        | refuseUnsupported s!"default initialization lacks layout for member '{name}'"
      let some width := (ctx.layout.fieldSizeDecl owner name).orElse (fun _ =>
          initializationSize ctx.layout type)
        | refuseUnsupported s!"default initialization lacks extent for member '{name}'"
      if offset < cursor || offset + width > size then
        refuseUnsupported "default structure initialization has overlapping or out-of-range members"
      zeroRange cursor (offset - cursor)
      pure (offset + width)
  zeroRange occupied (size - occupied)

mutual

/-- N3220 §6.7.11p11, p22. Default initialization is recursive in the
canonical type. The numeric zero, null pointer, and padding rules each
use the layout of the subobject they initialize. -/
def zeroInitStructured : Nat → Ctx → Ptr → String →
    Option LeanModels.Clang.QualType → Option LeanModels.C.DeclarationId → ExecM Unit
  | 0, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty, structured, declaration => do
      let some type := initializationType ctx.layout structured declaration
        | refuseUnsupported s!"zero initialization lacks parser-native QualType for '{ty}'"
      match type.unqualified with
      | .pointer _ => liftEval (writeMem (fun m => Mem.storePtr m p Ptr.null))
      | .array element (some extent) =>
          let some stride := initializationStride ctx.layout declaration element
            | refuseUnsupported s!"zero initialization lacks array element layout for '{ty}'"
          zeroElems fuel ctx p ty stride extent 0 (some element)
      | .record handle =>
          let owner : LeanModels.C.DeclarationId := { value := handle.value }
          let some members := ctx.layout.membersDecl owner
            | refuseUnsupported s!"zero initialization lacks record layout for '{ty}'"
          let some size := ctx.layout.recordSizeDecl owner
            | refuseUnsupported s!"zero initialization lacks record extent for '{ty}'"
          if members.any (·.1.isEmpty) then
            refuseUnsupported "default initialization with an unnamed member"
          else if ctx.layout.isUnionDecl owner then
            let some (name, memberTy) := members.head?
              | refuseUnsupported "default union initialization has no named member"
            -- A single byte range above every member is padding. Bytes of
            -- inactive members below that limit remain indeterminate.
            let memberExtent ← members.foldlM (init := 0) fun extent (member, _) => do
              let some width := ctx.layout.fieldSizeDecl owner member
                | refuseUnsupported "default union initialization lacks member extent"
              if ctx.layout.fieldOffDecl owner member != some 0 ||
                  (ctx.layout.fieldBitsDecl owner member).isSome || width > size then
                refuseUnsupported "default union initialization lacks byte-aligned member layout"
              pure (max extent width)
            let padding := List.replicate (size - memberExtent) (CByte.conc 0)
            unless padding.isEmpty do
              liftEval (writeMem (fun m => m.storeBytes (Mem.member p memberExtent) padding))
            zeroMembers fuel ctx p ty [(name, memberTy)] (some owner)
          else
            zeroStructurePadding ctx p owner size members
            zeroMembers fuel ctx p ty members (some owner)
      | _ =>
          match intTyOfStructured type with
          | some t =>
              liftEval (writeMem (fun m =>
                Mem.storeIntChecked m Mem.cAliasModel p t ty 0 (some type)))
          | none =>
              match floatBitsOfStructured type with
              | some 32 => liftEval (writeMem (fun m =>
                  Mem.storeFloat32 m p (Float32.Model.ofBits (UInt32.ofNat 0))))
              | some 64 => liftEval (writeMem (fun m =>
                  Mem.storeFloat64 m p (Float.Model.ofBits (UInt64.ofNat 0))))
              | _ => refuseUnsupported s!"no default value for parser-native type '{ty}'"

/-- Default-initialize the remaining array elements. -/
def zeroElems : Nat → Ctx → Ptr → String → Nat → Nat → Nat →
    Option LeanModels.Clang.QualType → ExecM Unit
  | 0, _, _, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty, stride, extent, index, structured =>
      if index ≥ extent then pure ()
      else do
        zeroInitStructured fuel ctx (Mem.memberRange p (index * stride) stride) ty structured none
        zeroElems fuel ctx p ty stride extent (index + 1) structured

/-- Default-initialize the remaining record members in declaration order. -/
def zeroMembers : Nat → Ctx → Ptr → String → List (String × String) →
    Option LeanModels.C.DeclarationId → ExecM Unit
  | 0, _, _, _, _, _ => exhausted
  | _, _, _, _, [], _ => pure ()
  | fuel + 1, ctx, p, ty, (name, memberTy) :: rest, declaration => do
      unless ctx.layout.flexibleFieldDeclAt declaration ty name do
        match ctx.layout.fieldBitsDeclAt declaration ty name with
        | some (offsetBits, width) =>
            unless name.isEmpty do
              initBitField ctx p declaration name memberTy offsetBits width none
        | none =>
            let some (offset, type, field) := declaration.bind (fun owner =>
                initializerField ctx.layout owner name)
              | refuseUnsupported s!"default initialization lacks layout for member '{name}'"
            zeroInitStructured fuel ctx (Mem.member p offset) memberTy (some type) field
      zeroMembers fuel ctx p ty rest declaration

end

/-! ### The initializer proper -/

mutual

/-- N3220 §6.7.11. Clang's initializer nodes already identify the current
subobject, including omitted and designated elements. Each recursive call
uses the canonical type of that subobject and the same layout as ordinary
member and array access. -/
def initObject : Nat → Ctx → Ptr → String → Expr →
    Option LeanModels.Clang.QualType → Option LeanModels.C.DeclarationId → ExecM Unit
  | 0, _, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty, e, structured, declaration =>
    let structured := initializationType ctx.layout structured declaration
    match e with
    | .implicitValueInit .. => zeroInitStructured fuel ctx p ty structured declaration
    | .constExpr _ (some sub@(.initList ..)) _ _ ..
    | .constExpr _ (some sub@(.arrayInitList ..)) _ _ .. =>
        initObject fuel ctx p ty sub structured declaration
    | .designatedUpdate base update _ _ .. => do
        checkInitializerOrder ctx declaration [base, update]
        initObject fuel ctx p ty base structured declaration
        initObject fuel ctx p ty update structured declaration
    | .arrayInitList inits filler _ _ _ nodeType =>
        let type := structured.orElse (fun _ => initializationType ctx.layout nodeType none)
        -- The first entry is Clang's default filler. Further entries
        -- preserve their position, including ImplicitValueInitExpr holes.
        match inits, filler, type.map LeanModels.Clang.QualType.unqualified with
        | [], .implicitValueInit .. :: entries, some (.array element (some extent)) => do
            checkInitializerOrder ctx declaration entries
            let some stride := initializationStride ctx.layout declaration element
              | refuseUnsupported s!"no array element layout for '{ty}'"
            initElems fuel ctx p ty stride extent 0 entries (some element)
        | _, _, _ => refuseUnsupported "unsupported Clang array_filler initializer"
    | .initList inits field _ _ nodeType => do
        let type := structured.orElse (fun _ => initializationType ctx.layout nodeType none)
        checkInitializerOrder ctx declaration inits
        if inits.isEmpty then zeroInitStructured fuel ctx p ty type declaration
        else
          match type.map LeanModels.Clang.QualType.unqualified with
          | some (.array element (some extent)) =>
              let some stride := initializationStride ctx.layout declaration element
                | refuseUnsupported s!"no array element layout for '{ty}'"
              initElems fuel ctx p ty stride extent 0 inits (some element)
          | some (.array ..) => refuseUnsupported s!"initializer lacks array extent for '{ty}'"
          | some (.record handle) =>
              let owner : LeanModels.C.DeclarationId := { value := handle.value }
              let some members := ctx.layout.membersDecl owner
                | refuseUnsupported s!"initializer lacks record layout for '{ty}'"
              if ctx.layout.isUnionDecl owner then
                match inits, field.orElse (fun _ => (members.find? (fun member => !member.1.isEmpty)).map (·.1)) with
                | [value], some name =>
                    let some (_, fieldTy) := members.find? (·.1 == name)
                      | refuseUnsupported s!"unknown union initializer member '{name}'"
                    match ctx.layout.fieldBitsDecl owner name with
                    | some (offsetBits, width) =>
                        initBitField ctx p owner name fieldTy offsetBits width (some value)
                    | none =>
                        let some (offset, memberType, fieldId) := initializerField ctx.layout owner name
                          | refuseUnsupported s!"initializer lacks layout for union member '{name}'"
                        initObject fuel ctx (Mem.member p offset) fieldTy value (some memberType) fieldId
                | _, _ => refuseUnsupported "union initializer has no single selected member"
              else if !members.isEmpty &&
                  members.all (fun (name, _) => (ctx.layout.fieldBitsDecl owner name).isSome) &&
                  inits.all independentBitFieldInitializer then
                initBitFieldRecord ctx p ty owner members inits
              else initMembers fuel ctx p ty members inits owner
          | some _ =>
              match inits with
              | [value] => initObject fuel ctx p ty value type declaration
              | _ => refuseUnsupported "more than one initializer for a scalar"
          | none => refuseUnsupported s!"initializer lacks parser-native QualType for '{ty}'"
    | .strLit _ decoded _ _ .. => do
        match structured.map LeanModels.Clang.QualType.unqualified with
        | some (.array element (some extent)) =>
            let some stride := initializationStride ctx.layout declaration element
              | refuseUnsupported "string initializer lacks element layout"
            let some bytes := decoded
              | refuseUnsupported "string initializer lacks Clang literal bytes"
            if stride == 0 || bytes.length % stride != 0 then
              refuseUnsupported "string initializer has incomplete element bytes"
            let width := extent * stride
            if bytes.length > width + stride || (bytes.drop width).any (· != 0) then
              refuseUnsupported "non-null string initializer element exceeds the array extent"
            let copied := (bytes.take width).map (fun byte => CByte.conc (UInt8.ofNat byte))
            let padded := copied ++ List.replicate (width - copied.length) (CByte.conc 0)
            liftEval (writeMem (fun m => m.storeBytes p padded))
        | _ =>
            let value ← evalE ctx e
            liftEval (storeAt Mem.cAliasModel p ty value structured)
    | _ => do
        let value ← evalE ctx e
        liftEval (storeAt Mem.cAliasModel p ty value structured)

/-- Initialize positional array entries and then default-initialize the tail. -/
def initElems : Nat → Ctx → Ptr → String → Nat → Nat → Nat → List Expr →
    Option LeanModels.Clang.QualType → ExecM Unit
  | 0, _, _, _, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty, stride, extent, index, entries, structured =>
      match entries with
      | [] => zeroElems fuel ctx p ty stride extent index structured
      | value :: rest =>
          if index ≥ extent then
            refuseUnsupported "more initializers than array elements"
          else do
            initObject fuel ctx (Mem.memberRange p (index * stride) stride) ty value structured none
            initElems fuel ctx p ty stride extent (index + 1) rest structured

/-- Structure members in declaration order, then zero-fill. -/
def initMembers : Nat → Ctx → Ptr → String → List (String × String) → List Expr → Option DeclarationId → ExecM Unit
  | 0, _, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty, ms, es, declaration =>
    match ms, es with
    | [], [] => pure ()
    | [], _ :: _ => refuseUnsupported "more initializers than structure members"
    -- the list ran out: §6.7.11p10 zeroes every member it did not reach
    | rest, [] => zeroMembers fuel ctx p ty rest declaration
    | (nm, mty) :: mrest, e :: erest =>
        let bits := ctx.layout.fieldBitsDeclAt declaration ty nm
        let fieldIsFlexible := declaration.bind (fun owner =>
          (ctx.layout.fieldStructuredDecl owner nm).map fun fieldType =>
            match fieldType.unqualified with
            | .array _ none => true
            | _ => false) |>.getD false
        if ctx.layout.flexibleFieldDeclAt declaration ty nm || fieldIsFlexible then
          match e with
          | .implicitValueInit _ _ .. => initMembers fuel ctx p ty mrest erest declaration
          | _ => refuseUnsupported s!"explicit initializer for flexible array member '{nm}'"
        else if nm.isEmpty && bits.isSome then
          -- §6.7.11p9: an unnamed bit-field has no member and consumes no
          -- initializer.  The parser-native layout still carries its
          -- storage range, but the initializer sequence skips it.
          initMembers fuel ctx p ty mrest es declaration
        else do
          match bits with
          | some (offsetBits, width) =>
              initBitField ctx p declaration nm mty offsetBits width (some e)
          | none =>
              let some (offset, type, field) := declaration.bind (fun owner =>
                  initializerField ctx.layout owner nm)
                | refuseUnsupported s!"initializer lacks layout for member '{nm}'"
              initObject fuel ctx (Mem.member p offset) mty e (some type) field
          initMembers fuel ctx p ty mrest erest declaration

end

/-! Install the statement-layer initializer callback used by compound
literals in the expression evaluator. -/
mutual
def compoundInitContext : Nat → Ctx → Ctx
  | 0, ctx => ctx
  | depth + 1, ctx =>
      { ctx with compoundInit := compoundInitCallback depth ctx }

def compoundInitCallback : Nat → Ctx → Nat → Env → IdEnv → Layout → Ptr → String → Expr → EvalM Unit
  | depth, ctx, fuel, env, ids, layout, p, ty, e =>
      let nested := compoundInitContext depth
        { ctx with env := env, idEnv := ids, layout := layout }
      initObject fuel nested p ty e none none
end

def Ctx.withCompoundInit (ctx : Ctx) : Ctx :=
  -- Compound literal nesting is bounded by the interpreter fuel.  Keeping a
  -- structural callback depth makes nested parser nodes retain the same
  -- initializer semantics without an unrestricted recursive definition.
  compoundInitContext 512 ctx

/-! ## §6.8.7.1 — `goto`, and why a label search is enough

Measured: the corpus's **7 `goto`s reach exactly 3 labels**
(`after_moves` x3, `out` x3, `reset_ok` x1), and **every one is a FORWARD
jump to a label in the same function at the same or an enclosing block
level.** That is precisely the shape a block can serve by scanning the
statements it has not run yet; a backward or into-a-block jump would need
a control-flow graph, and this corpus has none. A jump whose label is not
found propagates outward, and reaching the top of a function unmatched is
a refusal rather than a silent fall-through. -/

/-- The statements from `label` onward, if it is among these. -/
def findLabel (name : String) : List Stmt → Option (List Stmt)
  | [] => none
  | s :: rest =>
      match s with
      | .label n body sp => if n == name then some (.label n body sp :: rest)
                            else findLabel name rest
      | _ => findLabel name rest

def hasDecl : List Stmt → Bool
  | [] => false
  | .decl _ _ :: _ => true
  | _ :: rest => hasDecl rest

/-! ## §6.8 — the statement evaluator

Fuel decreases on EVERY recursive call, not only at the loop step. That
is stricter than §4.6.1 needs — a block is not an iteration — but it
makes the recursion structural on `Nat` with no measure to justify, and
fuel is a bound on total work rather than on iterations alone. The
`∃ n, ∀ fuel ≥ n` threshold form is unaffected: it quantifies over fuel
from outside. -/

inductive SwitchItem where
  | label (value : Option Expr)
  | rangeLabel (lo hi : Expr)
  | stmt (s : Stmt)

def switchCaseTail : Stmt → List SwitchItem
  | .caseS v b _ => .label (some v) :: switchCaseTail b
  | .caseRange lo hi b _ => .rangeLabel lo hi :: switchCaseTail b
  | .defaultS b _ => .label none :: switchCaseTail b
  | s => [.stmt s]

def switchItems : Stmt → List SwitchItem
  | .compound body _ => body.flatMap switchItems
  | .caseS v b _ => .label (some v) :: switchCaseTail b
  | .caseRange lo hi b _ => .rangeLabel lo hi :: switchCaseTail b
  | .defaultS b _ => .label none :: switchCaseTail b
  | s => [.stmt s]

def containsCaseLabel (s : Stmt) : Bool :=
  s.substmts.any fun t => match t with
    | .caseS .. | .caseRange .. | .defaultS .. => true
    | _ => false

def switchHasNestedLabel : Stmt → Bool
  | .compound body _ => body.any fun s =>
      match s with
      | .caseS _ b _ | .caseRange _ _ b _ | .defaultS b _ => containsCaseLabel b
      | _ => containsCaseLabel s
  | s => containsCaseLabel s

def switchHasControlNestedLabel (s : Stmt) : Bool :=
  s.substmts.any fun t =>
    match t with
    | .ifS .. | .forS .. | .whileS .. | .doS .. | .switchS .. => containsCaseLabel t
    | _ => false

def switchFindAux (ctx : Ctx) (cv : CVal) :
    List SwitchItem → Option (List Stmt) → Option (List Stmt) → EvalM (Option (List Stmt))
  | [], selected, fallback =>
      pure ((selected.orElse (fun _ => fallback)).map List.reverse)
  | .label label :: rest, selected, fallback =>
      match selected with
      | some _ => switchFindAux ctx cv rest selected fallback
      | none =>
          match label with
          | none => switchFindAux ctx cv rest none (some [])
          | some e => do
              let v ← evalExpr ctx e
              let (_, a) ← asInt cv
              let (_, b) ← asInt v
              if a == b then switchFindAux ctx cv rest (some []) fallback
              else switchFindAux ctx cv rest none fallback
  | .rangeLabel lo hi :: rest, selected, fallback =>
      match selected with
      | some _ => switchFindAux ctx cv rest selected fallback
      | none => do
          let lv ← evalExpr ctx lo
          let hv ← evalExpr ctx hi
          let (_, a) ← asInt cv
          let (_, l) ← asInt lv
          let (_, h) ← asInt hv
          if l ≤ a && a ≤ h then switchFindAux ctx cv rest (some []) fallback
          else switchFindAux ctx cv rest none fallback
  | .stmt s :: rest, selected, fallback =>
      match selected, fallback with
      | some acc, _ => switchFindAux ctx cv rest (some (s :: acc)) fallback
      | none, some acc => switchFindAux ctx cv rest none (some (s :: acc))
      | none, none => switchFindAux ctx cv rest none none
  termination_by items _ _ => items.length

def switchFind (ctx : Ctx) (cv : CVal) (body : Stmt) : EvalM (Option (List Stmt)) :=
  switchFindAux ctx cv (switchItems body) none none

mutual

def execSwitch : Nat → Ctx → Expr → Stmt → ExecM Flow
  | 0, _, _, _ => exhausted
  | fuel + 1, ctx, cond, body => do
      if switchHasControlNestedLabel body then
        refuseUnsupported "case label nested in a control statement"
      let cv ← evalE ctx cond
      let selected ← switchFind ctx cv body
      match selected with
      | none => pure .normal
      | some statements => do
          -- A goto from a case body targets the enclosing function's label
          -- set.  The temporary case block must not resolve `functionBody`
          -- itself, or the outer block would resume after the switch and run
          -- the label tail a second time (C23 §6.8.4p3, §6.8.7.1).
          let f ← execBlock fuel { ctx with functionBody := none } statements
          match f with
          | .brk => pure .normal
          | other => pure other

/-- §6.8 — execute one statement, yielding how it completed. -/
def execStmt : Nat → Ctx → Stmt → ExecM Flow
  | 0, _, _ => exhausted
  | fuel + 1, ctx, s => match s with
    -- §6.8.3 — a block. Declarations inside it extend the environment,
    -- which is why the block threads a context rather than reading one.
    | .compound body _ => do
        let m₀ ← get
        let base := m₀.count
        let runMemset : List CVal → EvalM CVal := fun vs =>
          match vs with
          | [p, byte, count] => do
              let q ← asPtr p
              let (_, b) ← asInt byte
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "memset: negative size"
              else do
                let bs := List.replicate n.toNat (CByte.conc (UInt8.ofNat b.toNat))
                writeMem (fun m => m.storeBytes q bs)
                pure (.ptr q)
          | _ => refuseUnsupported "memset: wrong argument count"
        let f ← execBlock fuel ctx body
        let m₁ ← get
        set (m₁.killFrom base)
        pure f
    -- §6.8.4 — an expression statement: evaluated for its EFFECTS, value
    -- discarded. 297 sites, the largest statement class in the corpus.
    | .expr e _ => do let _ ← evalE ctx e; pure .normal
    | .nullStmt _ => pure .normal
    | .switchS c body _ => execSwitch fuel ctx c body
    | .caseS _ _ _ | .caseRange _ _ _ _ | .defaultS _ _ =>
        refuseUnsupported "case/default escaped a switch body"
    -- §6.8.5.1 — `if`. Measured: only 51 of 253 carry an `else`, so the
    -- else-less arm is the common path and is written first.
    | .ifS c t none _ => do
        if (← evalCond ctx c) then execStmt fuel ctx t else pure .normal
    | .ifS c t (some (.compound body bsp)) _ => do
        if (← evalCond ctx c) then
          let f ← execStmt fuel ctx t
          match f with
          | .goto l =>
              match findLabel l body with
              | some tail => execBlock fuel ctx tail
              | none => pure f
          | other => pure other
        else execStmt fuel ctx (.compound body bsp)
    | .ifS c t (some e) _ => do
        if (← evalCond ctx c) then execStmt fuel ctx t else execStmt fuel ctx e
    -- §6.8.7.4 — `return`, with a value at 98 of 103 sites.
    | .ret none _ => pure (.ret none)
    | .ret (some e) _ => do let v ← evalE ctx e; pure (.ret (some v))
    | .breakS _ => pure .brk              -- §6.8.7.3, 8 sites
    | .continueS _ => pure .cont          -- §6.8.7.2, 6 sites
    | .goto l _ => pure (.goto l)         -- §6.8.7.1, 7 sites
    -- A labelled statement runs its body; the LABEL is found by the
    -- enclosing block (`findLabel`), not by the statement itself.
    | .label _ body _ => execStmt fuel ctx body
    -- §6.8.6.2 — `while`. 5 sites.
    | .whileS c body _ => execLoop fuel ctx (some c) none body false
    -- §6.8.6.3 — `do … while`: the body runs BEFORE the first test. 29 sites.
    | .doS body c _ => execLoop fuel ctx (some c) none body true
    -- §6.8.6.4 — `for`. 50 sites; 48 carry `init`, 49 carry `cond`, 50 carry
    -- `inc` — so THREE sites omit a clause (two omit `init`, one omits
    -- `cond`) and the omitted-clause arms are
    -- three sites rather than a third of them. An omitted `cond` is TRUE.
    | .forS init c inc body _ => do
        match init with
        | some i => do
            match i with
            | .decl ds _ =>
                let ctx' ← declare fuel ctx ds
                execLoop fuel ctx' c inc body false
            | _ =>
                let f ← execStmt fuel ctx i
                match f with
                | .normal => execLoop fuel ctx c inc body false
                | other => pure other
        | none => execLoop fuel ctx c inc body false
    -- A bare declaration reaching here is one the block did not thread;
    -- `execBlock` handles them, so this is unreachable in practice and
    -- refuses rather than silently doing nothing.
    | .decl _ _ => refuseUnsupported "declaration outside a block"
    | .unsupported k _ _ => refuseUnsupported s!"out of tier: {k}"

/-- Run a block's statements in order, threading the environment that
declarations extend and honouring a forward `goto` into the remainder. -/
def execBlock : Nat → Ctx → List Stmt → ExecM Flow
  | 0, _, _ => exhausted
  | _, _, [] => pure .normal
  | fuel + 1, ctx, s :: rest =>
    match s with
    -- §6.7 — a declaration extends the environment for the REST of the
    -- block. C23 §6.7p5 sequences declarators left to right, each fully
    -- before the next, which `declare` follows.
    | .decl ds _ => do
        let ctx' ← declare fuel ctx ds
        execBlock fuel ctx' rest
    | _ => do
      let f ← execStmt fuel ctx s
      match f with
      | .normal => execBlock fuel ctx rest
      | .goto l =>
          -- §6.8.7.1: a forward jump lands on a label later in THIS block,
          -- or propagates outward to an enclosing one.
          match findLabel l rest with
          | some tail =>
              if hasDecl rest then
                refuseUnsupported "goto skips a block declaration"
              else execBlock fuel ctx tail
          | none =>
              -- A forward goto may land in the compound then-arm of a
              -- later if.  The label is still a parser-tree child of this
              -- enclosing block, so resume at its tail and then continue
              -- with the statements after the if (C23 §6.8.6.1).
              match rest with
              | (.ifS _ (.compound body bsp) _ _) :: after =>
                  match findLabel l body with
                  | some tail =>
                      if hasDecl rest then
                        refuseUnsupported "goto skips a block declaration"
                      else execBlock fuel ctx (tail ++ after)
                  | none => pure (.goto l)
              | _ =>
                  -- §6.8.6.1: a same-function `goto` may target a label
                  -- earlier in the enclosing function.  The parser AST is
                  -- already the function's complete statement list, so
                  -- resume from its label tail; no source re-parsing or
                  -- control-flow lowering is involved.  A declaration on
                  -- the resumed tail would mean jumping into its scope and
                  -- remains a loud refusal.  Fuel bounds repeated jumps.
                  match ctx.functionBody with
                  | some functionStatements =>
                      match findLabel l functionStatements with
                      | some tail =>
                          if hasDecl tail then
                            refuseUnsupported "goto skips a block declaration"
                          else execBlock fuel ctx tail
                      | none => pure (.goto l)
                  | none => pure (.goto l)
      | other => pure other

/-- One loop, with fuel decreasing per ITERATION.

`post` is `do … while`: the body runs before the first test. `inc` is
`for`'s third clause, evaluated after the body and before the next test —
and, per §6.8.6.4p2, **also after a `continue`**, which is the detail a
model gets wrong by treating `continue` as `break`. -/
def execLoop : Nat → Ctx → Option Expr → Option Expr → Stmt → Bool → ExecM Flow
  | 0, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, cond, inc, body, post => do
      -- an omitted controlling expression is TRUE (§6.8.6.4p2)
      let go ← if post then pure true
               else match cond with
                    | some c => evalCond ctx c
                    | none => pure true
      if !go then pure .normal
      else do
        let f ← execStmt fuel ctx body
        match f with
        | .brk => pure .normal            -- §6.8.7.3: break ENDS the loop
        | .ret v => pure (.ret v)
        | .goto l => pure (.goto l)
        | .normal | .cont => do
            -- §6.8.6.4p2: `continue` still runs the increment.
            match inc with
            | some e => do let _ ← evalE ctx e; pure ()
            | none => pure ()
            execLoop fuel ctx cond inc body false

/-- §6.7 — create the objects a declaration introduces and bind their
names, left to right.

Measured: 273 of 321 `VarDecl`s carry an initializer, and **75
`InitListExpr` nodes** appear in the corpus (35 top-level, 40 nested).
Both shapes go through `initObject` (§6.7.11). -/
def declare : Nat → Ctx → List Decl → ExecM Ctx
  | 0, _, _ => exhausted
  | _, ctx, [] => pure ctx
  | fuel + 1, ctx, d :: ds =>
    match d with
    | .functionProto .. =>
        -- §6.7.6.3: a block-scope prototype declares a function and has no
        -- object storage or initializer to execute.
        declare fuel ctx ds
    | .var id name ty storage init _recordId vaList _ structuredType => do
        if storage == some "static" then
          match id with
          | some declaration =>
              match ctx.idEnv.lookup? declaration with
              | some o => declare fuel { ctx with env := (name, o) :: ctx.env } ds
              | none => refuseUnsupported s!"static object '{name}' has no initialized storage"
          | none => refuseUnsupported s!"static object '{name}' has no declaration identity"
        else
          match storage with
          | some "auto" | some "register" | some "static" | none => pure ()
          | some s => refuseUnsupported s!"block-scope storage class '{s}' is outside the tier"
          let variableLength := structuredType.any fun type =>
            match type.unqualified with
            | .array _ none => true
            | _ => false
          if variableLength then
            refuseUnsupported
              s!"variable-length array '{ty}' lacks parser-native bound expression"
          match if vaList then some 1 else ctx.layout.sizeAt id ty with
          | none => refuseUnsupported s!"no layout for declared type '{ty}'"
          | some sz => do
            -- §6.2.4p6: an automatic object lives from block entry, with
            -- an INDETERMINATE representation until something writes it;
            -- block-scope `static` instead keeps its static lifetime.
            let m ← get
            let dur := if storage == some "static" then Duration.static_ else Duration.automatic
            let storageTy := ctx.layout.storageTypeAt id ty
            let (m', o) := m.allocStructured dur sz storageTy structuredType
            set m'
            let idEnv' := match id with
              | some declaration => (declaration, o) :: ctx.idEnv
              | none => ctx.idEnv
            let ctx' := { ctx with env := (name, o) :: ctx.env }
            let ctx' := { ctx' with idEnv := idEnv' }
            match init with
            | none => declare fuel ctx' ds
            | some e => do
                -- §6.7.11 — scalar or aggregate, one entry point.
                initObject fuel ctx' (Ptr.toObject o) ty e structuredType id
                declare fuel ctx' ds
    | .empty _ => declare fuel ctx ds
    | .record .. | .enum .. | .typedef .. =>
        declare fuel ctx ds
    | _ => refuseUnsupported "non-object declaration in a block"

end

/-! ## §6.5.3.3 — function calls: inch 5

**The call graph is almost entirely acyclic, and the census is the
decision-relevant fact.** Of 58 defined functions, exactly **one is
directly self-recursive** (`bound`, the search) and there is **one mutual
cycle of size two** (`bound` ↔ `score_move`). Everything else is a DAG.

So fuel, which arrived at inch 4 for loops, arrives here for a call graph
whose cyclic part is two functions wide. It is still needed — a model
cannot know the graph is acyclic without proving it — but the measurement
says the fuel-consuming surface is small, and it names exactly which
functions a termination argument would have to be about.

Where the 320 call sites go:

| | sites |
| --- | ---: |
| to one of the 58 DEFINED functions | **155** |
| to one of the 27 libc externals — cause `libc` | **146** |
| INDIRECT, every one through `movecb` | **19** |

Nearly half of all calls leave the tier, and they refuse as `libc` — the
cause that retires by widening the slice, never pooled with the others. -/

/-- The functions a call can reach, with the layout and enumeration
constants they need. -/
structure Program where
  fns : List LeanModels.C.FunctionDefn
  layout : Layout := Layout.unknown
  enums : List (String × Int) := []
  enumIds : List (LeanModels.C.DeclarationId × Int) := []
  /-- **§6.2.1p4 — the file-scope objects a function body can SEE.**

  This field is a bug fix, not a feature. `callFn` used to start every
  frame at `env := []`, which is the rule *"no object declared outside a
  function is visible inside one"* — and C's rule is the opposite: an
  identifier declared at file scope has file scope, and that scope runs to
  the end of the translation unit. The old spelling was not a missing
  capability, it was a wrong law, and it was invisible because the corpus
  the tier was built on passes everything through parameters.

  Measured on `gcc.c-torture`: **69 of 300 tests refused with `unbound
  name`, and all 69 of the names were file-scope objects** — 100 %, no
  locals and no typos (`docs/backlog/c.md` 2026-08-24-c-22). -/
  globals : Env := []
  globalIds : IdEnv := []
  stdoutObj : Option ObjId := none

def Program.find? (p : Program) (name : String) : Option LeanModels.C.FunctionDefn :=
  p.fns.find? (·.name == name)

def Program.findId? (p : Program) (id : LeanModels.C.DeclarationId) :
    Option LeanModels.C.FunctionDefn :=
  p.fns.find? (fun f => f.id == some id)

-- `evalArgsLR` lived here, unreachable, as "the shape the repair will
-- re-attach to". The repair did not re-attach to it: argument evaluation
-- had to move INTO `Expr.lean`'s mutual block to borrow `evalExpr`'s
-- measure, so the real function is `C23.evalArgs` and this copy is deleted
-- rather than left as a second answer to one question.

/-- §6.5.3.3p4 / §6.9.2p7 — give each parameter its own automatic object
and store the argument into it.

A parameter IS an object (§6.9.2p7: "the parameters are declared as if by
declaration in the compound statement"), which is why 1 of the corpus's
31 `&`-of-automatic sites takes the address of one. Measured parameter
counts: 0-9, and 39 of 58 functions take two or fewer. -/
def bindParams (lay : Layout) : Ctx → List LeanModels.C.Decl → List CVal → ExecM Ctx
  | ctx, [], [] => pure ctx
  | _, [], _ :: _ => refuseUnsupported "more arguments than parameters"
  | _, _ :: _, [] => refuseUnsupported "fewer arguments than parameters"
  | ctx, d :: ps, v :: vs =>
    match d with
    | .param id n ty vaList _ structuredType =>
        match if vaList then some 1 else lay.sizeAtStructured id ty structuredType with
        | none => refuseUnsupported s!"no layout for parameter type '{ty}'"
        | some sz => do
            -- §6.9.2p7 holds for an UNNAMED parameter too: the object
            -- exists and is initialized with the converted argument. The
            -- allocation and the store are OUTSIDE the match on `n` on
            -- purpose — eliding them for the unnamed case is not
            -- expressible here without moving code, which is the point.
            -- (Whether the allocation is unobservable when nothing names
            -- the object is a LEMMA about `Mem`, not a shortcut; it is not
            -- claimed, so it is not taken.)
            let m ← get
            let storageTy := lay.storageTypeAt id ty
            let (m', o) := m.allocStructured .automatic sz storageTy structuredType
            set m'
            liftEval (storeAt Mem.cAliasModel (Ptr.toObject o) ty v
              structuredType)
            -- …and the ONLY difference an unnamed parameter makes is that
            -- no identifier denotes the object, which in this model is
            -- exactly one thing: no environment entry. This is the single
            -- place the absence is decided.
            let env' := match n with
                        | some nm => (nm, o) :: ctx.env
                        | none => ctx.env
            let idEnv' := match id with
                          | some declaration => (declaration, o) :: ctx.idEnv
                          | none => ctx.idEnv
            bindParams lay { ctx with env := env', idEnv := idEnv' } ps vs
    | _ => refuseUnsupported "non-parameter in a parameter list"

/-! Clang's JSON AST does not retain the `TypeLoc` expressions for a
parameter array bound (for example `int b[a++]` is ingested only as `int *`).
The declaration-identity rule therefore gives us no sound way to execute
those bound side effects.  This structural shape is the small registered
route's conservative guard: refuse it before the body rather than inventing
the missing parser fact. -/
def hasUnretainedParamArrayEffects (lay : Layout) : List LeanModels.C.Decl → Bool
  | .param id _ ty _ _ .. :: .param id' _ pty _ _ .. ::
      .param id₂ _ ty₂ _ _ .. :: .param id₂' _ pty₂ _ _ .. :: _ =>
      !structuredPointerObject (id.bind lay.structuredType) ty &&
      structuredPointerObject (id'.bind lay.structuredType) pty &&
      !structuredPointerObject (id₂.bind lay.structuredType) ty₂ &&
      structuredPointerObject (id₂'.bind lay.structuredType) pty₂
  | _ => false

def hasUnnamedPointerParam (lay : Layout) : List LeanModels.C.Decl → Bool
  | d :: ps =>
      match d with
      | .param (some id) none ty _ _ .. =>
          let isPointer := structuredPointerObject (lay.structuredType id) ty
          isPointer || hasUnnamedPointerParam lay ps
      | _ => hasUnnamedPointerParam lay ps
  | [] => false

def hasGotoControlledPointerIncrement (body : Stmt) : Bool :=
  let hasGoto := body.substmts.any fun statement =>
    match statement with
    | .goto .. => true
    | _ => false
  let hasPointerIncrement := (body.substmts.flatMap Stmt.ownExprs).any fun expression =>
    match expression with
    | .unop op .. => op == "++" || op == "--"
    | _ => false
  hasGoto && hasPointerIncrement

/-! A call-free body is a sound sufficient effect summary for §6.5.1's
indeterminate-order check. It is deliberately conservative: any nested call,
write, aggregate initializer, or unsupported expression makes the summary
false. -/
def stmtCallFree (s : Stmt) : Bool :=
  s.substmts.all (fun sub => sub.ownExprs.all Expr.isPure)

def Decl.identity? : Decl → Option DeclarationId
  | .var id .. | .functionProto id .. => id
  | .param id .. => id
  | _ => none

def Stmt.localIds (s : Stmt) : List DeclarationId :=
  s.substmts.flatMap fun node => match node with
    | .decl ds _ => ds.filterMap Decl.identity?
    | _ => []

def Expr.localOnly (allowed : List DeclarationId) : Expr → Bool
  | e => e.subexprs.all fun node =>
      match node with
      | .call .. | .member .. | .index .. => false
      | .unop op .. => op != "*" && op != "&"
      | .declRef (some id) .. => allowed.contains id
      | .declRef none .. => false
      | _ => true

def functionCallFree (f : LeanModels.C.FunctionDefn) : Bool :=
  match f.body with
  | none => false
  | some body =>
      let allowed := (f.params.filterMap Decl.identity?) ++ Stmt.localIds body
      let pureBuiltin : Expr → Bool
        | .call callee args .. =>
            match calleeName callee with
            | some nm =>
                (nm == "__builtin_fabs" || nm == "__builtin_fabsf" ||
                 nm == "__builtin_fabsl" || nm == "__builtin_isinf" ||
                 nm == "__builtin_isnan" || nm == "__builtin_isfinite" ||
                 nm == "__builtin_isunordered" ||
                 nm == "__builtin_signbit" || nm == "__builtin_bswap16" ||
                 nm == "__builtin_copysign" || nm == "__builtin_copysignf" || nm == "fabs" ||
                 nm == "floor" || nm == "floorf" ||
                 nm == "__builtin_bswap32" || nm == "__builtin_bswap64" ||
                 nm == "__builtin_ffs" || nm.contains "ctz" || nm.contains "clz" ||
                 nm.contains "clrsb" || nm.contains "popcount" || nm.contains "parity" ||
                 nm == "__builtin_abs" || nm == "abs") &&
                args.all (Expr.localOnly allowed)
            | none => false
        | _ => false
      let localPure : Expr → Bool := fun e =>
        e.subexprs.all fun node =>
          match node with
          | .call .. => pureBuiltin node
          | .member .. | .index .. => false
          | .unop op .. => op != "*" && op != "&"
          | .declRef _ _ "FunctionDecl" .. => true
          | .declRef (some id) .. => allowed.contains id
          | .declRef none .. => false
          | _ => true
      (body.substmts.flatMap Stmt.ownExprs).all localPure

/-- The envelope can omit expressions in variable array bounds. A local
type with such a bound cannot certify absence of an address use. -/
private def mayHideArrayBound : LeanModels.Clang.QualType → Bool
  | .array _ none | .typedefRef _ => true
  | .array inner (some _) | .pointer inner | .qualified _ _ inner
  | .restrictQualified inner => mayHideArrayBound inner
  | _ => false

/-- A sufficient condition for the register premise of N3220 §6.3.2.1p2.
Only a direct automatic scalar declared without an initializer is eligible.
The scan follows the parser's declaration identity through every address
operand in the original body, including initializers and unevaluated
operands. An omitted subtree or a potentially omitted type bound leaves
the premise unavailable. -/
private def uninitializedRegisterCandidate (body : Stmt)
    (id : LeanModels.C.DeclarationId) : Bool := Id.run do
  let statements := body.substmts
  let declarations := statements.flatMap fun
    | .decl ds _ => ds
    | _ => []
  let found := declarations.any fun
    | .var (some key) _ _ storage none _ false _ (some type) =>
        key == id && (storage.isNone || storage == some "auto" || storage == some "register") &&
          ((intTyOfStructured type).isSome || (floatBitsOfStructured type).isSome ||
            type.unqualified.pointerObject)
    | _ => false
  unless found do return false
  let complete := declarations.all fun
    | .var _ _ _ _ _ _ _ _ type | .typedef _ _ _ _ _ type =>
        type.any (!mayHideArrayBound ·)
    | .unsupported .. => false
    | _ => true
  let noAddressUse := (statements.flatMap Stmt.ownExprs).all fun
    | .unsupported .. => false
    | .unop "&" operand .. => !operand.subexprs.any fun
        | .declRef key .. => key.isNone || key == some id
        | _ => false
    | .cast _ _ _ _ type => type.any (!mayHideArrayBound ·)
    | .typeTrait _ _ _ _ _ type _ _ _ => !type.any mayHideArrayBound
    | _ => true
  return complete && noAddressUse && statements.all fun
    | .unsupported .. => false
    | _ => true

/-- §6.5.3.3 — call a defined function with already-evaluated arguments.

The handler the callee's frame carries is built HERE, closing over the
decremented fuel: that is the whole recursion, and it is why fuel is a
parameter of this function rather than of `evalExpr`.

A `void` function answers `.undef`, not a fabricated zero — the value of
a `void` call may not be used (§6.5.3.3p3), and `.undef` is the value
every consumer already refuses. Returning `0` would have been a number
somebody could read. -/
def callFn : Nat → Program → LeanModels.C.FunctionDefn → List CallArgument → ExecM CVal
  | 0, _, _, _ => exhausted
  | fuel + 1, prog, f, args =>
    match f.body with
    | none => refuseUnsupported s!"'{f.name}' is a prototype, not a definition"
    | some body => do
        let fixedArgs := (args.take f.params.length).map CallArgument.value
        let extraArgs := args.drop f.params.length
        if args.length < f.params.length then
          refuseUnsupported "fewer arguments than parameters"
        if !f.variadic && !extraArgs.isEmpty then
          refuseUnsupported "more arguments than parameters"
        if hasUnnamedPointerParam prog.layout f.params then
          refuseUnsupported "unnamed pointer parameter (array-bound effects are not retained by clang)"
        if hasUnretainedParamArrayEffects prog.layout f.params then
          refuseUnsupported "parameter array-bound effects are not retained by clang"
        if hasGotoControlledPointerIncrement body then
          refuseUnsupported "goto-controlled pointer increment lacks an exact parser path"
        let m₀ ← get
        let base := m₀.count
        -- N3220 §7.26.2: byte copies need source and destination
        -- ranges. The tier has independent allocation and subobject ends,
        -- and refuses a copy that spans subobjects within an allocation.
        let checkByteCopySpan (p : Ptr) (n : Nat) : ExecM Unit := do
          if let some bound := p.bound then
            if p.off < bound && p.off + (n : Int) > bound then
              let _ ← readMem (fun mem => mem.resolve { p with bound := none } n)
              refuseUnsupported "byte copy spans a subobject boundary"
        let runMemset : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [p, byte, count] => do
              let q ← asPtr p
              let (_, b) ← asInt byte
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "memset: negative size"
              else do
                let bs := List.replicate n.toNat (CByte.conc (UInt8.ofNat b.toNat))
                liftEval (writeMem (fun m => m.storeBytes q bs))
                pure (.ptr q)
          | _ => refuseUnsupported "memset: wrong argument count"
        let runMemcpy : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, src, count] => do
              let dp ← asPtr dst
              let sp ← asPtr src
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "memcpy: negative size"
              else do
                checkByteCopySpan sp n.toNat
                checkByteCopySpan dp n.toNat
                let bs ← liftEval (readMem (fun m => m.loadBytes sp n.toNat))
                liftEval (writeMem (fun m => m.storeBytes dp bs))
                pure (.ptr dp)
          | _ => refuseUnsupported "memcpy: wrong argument count"
        let runMempcpy : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, src, count] => do
              let dp ← asPtr dst
              let sp ← asPtr src
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "mempcpy: negative size"
              else do
                checkByteCopySpan sp n.toNat
                checkByteCopySpan dp n.toNat
                let bs ← liftEval (readMem (fun m => m.loadBytes sp n.toNat))
                liftEval (writeMem (fun m => m.storeBytes dp bs))
                pure (.ptr { dp with off := dp.off + n })
          | _ => refuseUnsupported "mempcpy: wrong argument count"
        let runMemmove : List CVal → ExecM CVal := fun vs => runMemcpy vs
        let runStrncpy : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, src, count] => do
              let dp ← asPtr dst
              let sp ← asPtr src
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "strncpy: negative size"
              else do
                let m ← get
                let (_, source, off) ← liftEval (m.resolve sp 0)
                let rec takeN : Nat → List CByte → Option (List CByte)
                  | 0, _ => some []
                  | k + 1, [] => none
                  | k + 1, .conc x :: rest =>
                      if x == 0 then
                        some (CByte.conc 0 :: List.replicate k (CByte.conc 0))
                      else
                        (takeN k rest).map (fun tail => CByte.conc x :: tail)
                  | _, _ => none
                match takeN n.toNat (source.bytes.drop off) with
                | some bytes =>
                    liftEval (writeMem (fun mem => mem.storeBytes dp bytes))
                    pure (.ptr dp)
                | none => refuseUnsupported "strncpy: non-concrete source range"
          | _ => refuseUnsupported "strncpy: wrong argument count"
        let runPutchar : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [v] => do
              let (_, n) ← asInt v
              let byte := CByte.conc (UInt8.ofNat n.toNat)
              modify (fun mem => mem.emitStdout [byte])
              pure (.int IntTy.int_ (UInt8.ofNat n.toNat).toNat)
          | _ => refuseUnsupported "putchar: wrong argument count"
        let runPuts : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [v] => do
              let p ← asPtr v
              let m ← get
              let (_, source, off) ← liftEval (m.resolve p 0)
              let rec takePutsString : List CByte → Option (List CByte)
                | [] => none
                | .conc x :: rest =>
                    if x == 0 then some []
                    else (takePutsString rest).map (fun tail => CByte.conc x :: tail)
                | _ => none
              let chars ← match takePutsString (source.bytes.drop off) with
                | some bytes => pure bytes
                | none => refuseUnsupported "puts: non-concrete or unterminated string"
              modify (fun mem => mem.emitStdout (chars ++ [CByte.conc 10]))
              pure (.int IntTy.int_ 0)
          | _ => refuseUnsupported "puts: wrong argument count"
        let formatFixed6 (q : LeanModels.SoftFloat.Q) : String :=
          let negative := q.num < 0
          let magnitude := q.num.natAbs * 1000000
          let whole := magnitude / q.den
          let remainder := magnitude % q.den
          let rounded := whole +
            if 2 * remainder > q.den ||
                (2 * remainder == q.den && whole % 2 == 1) then 1 else 0
          let integerPart := toString (rounded / 1000000)
          let fraction := toString (rounded % 1000000)
          let fraction := String.ofList (List.replicate (6 - fraction.length) '0') ++ fraction
          (if negative then "-" else "") ++ integerPart ++ "." ++ fraction
        let formatFloatFixed6 : CVal → Option String
          | .float32 f => (LeanModels.SoftFloat.valQ f.unpack).map formatFixed6
          | .float64 f => (LeanModels.SoftFloat.valQ f.unpack).map formatFixed6
          | _ => none
        let runSprintf : List CVal → ExecM CVal := fun vs =>
          match vs with
          | dst :: fmt :: args => do
              let dp ← asPtr dst
              let fp ← asPtr fmt
              let m ← get
              let (_, fo, off) ← liftEval (m.resolve fp 0)
              let rec takeSprintfString : List CByte → Option (List CByte)
                | [] => none
                | .conc x :: rest =>
                    if x == 0 then some []
                    else (takeSprintfString rest).map (fun tail => CByte.conc x :: tail)
                | _ => none
              let pattern ← match takeSprintfString (fo.bytes.drop off) with
                | some bytes => pure bytes
                | none => refuseUnsupported "sprintf: non-concrete or unterminated format"
              let digitByte (d : Nat) : CByte :=
                if d < 10 then CByte.conc (UInt8.ofNat (48 + d))
                else CByte.conc (UInt8.ofNat (87 + d))
              let rec octDigits (n : Nat) : List CByte :=
                if n < 8 then [digitByte n]
                else octDigits (n / 8) ++ [digitByte (n % 8)]
                termination_by n
                decreasing_by exact Nat.div_lt_self (by omega) (by omega)
              let rec hexDigits (n : Nat) : List CByte :=
                if n < 16 then [digitByte n]
                else hexDigits (n / 16) ++ [digitByte (n % 16)]
                termination_by n
                decreasing_by exact Nat.div_lt_self (by omega) (by omega)
              let altOctal (n : Nat) : List CByte :=
                if n == 0 then [CByte.conc 48]
                else CByte.conc 48 :: octDigits n
              let altHex (n : Nat) : List CByte :=
                if n == 0 then [CByte.conc 48]
                else [CByte.conc 48, CByte.conc 120] ++ hexDigits n
              let rec formatSprintf : List CByte → List CVal → ExecM (List CByte)
                | [], _ => pure []
                | .conc 37 :: .conc 37 :: rest, as => do
                    let tail ← formatSprintf rest as
                    pure (CByte.conc 37 :: tail)
                | .conc 37 :: .conc 100 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← formatSprintf rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 108 :: .conc 117 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← formatSprintf rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 48 :: .conc 50 :: .conc 100 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let rendered := if n >= 0 && n < 10 then "0" ++ toString n else toString n
                    let tail ← formatSprintf rest as
                    pure (rendered.toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 102 :: rest, a :: as => do
                    let rendered ← match formatFloatFixed6 a with
                      | some text => pure text
                      | none => refuseUnsupported "sprintf: non-finite or non-floating argument"
                    let tail ← formatSprintf rest as
                    pure (rendered.toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 35 :: .conc 104 :: .conc 104 :: .conc 111 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← formatSprintf rest as
                    pure (altOctal n.toNat ++ tail)
                | .conc 37 :: .conc 35 :: .conc 104 :: .conc 104 :: .conc 120 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← formatSprintf rest as
                    pure (altHex n.toNat ++ tail)
                | .conc 37 :: .conc 115 :: rest, a :: as => do
                    let sp ← asPtr a
                    let current ← get
                    let (_, string, stringOff) ← liftEval (current.resolve sp 0)
                    let chars ← match takeSprintfString (string.bytes.drop stringOff) with
                      | some bytes => pure bytes
                      | none => refuseUnsupported "sprintf: non-concrete or unterminated string argument"
                    let tail ← formatSprintf rest as
                    pure (chars ++ tail)
                | .conc 37 :: [], _ => refuseUnsupported "sprintf: trailing percent"
                | .conc 37 :: .conc _ :: _, _ => refuseUnsupported "sprintf: unsupported format"
                | .conc b :: rest, as => do
                    let tail ← formatSprintf rest as
                    pure (CByte.conc b :: tail)
                | _, _ => refuseUnsupported "sprintf: non-concrete format byte"
              let chars ← formatSprintf pattern args
              let bytes := chars ++ [CByte.conc 0]
              liftEval (writeMem (fun mem => mem.storeBytes dp bytes))
              pure (.int IntTy.int_ chars.length)
          | _ => refuseUnsupported "sprintf: missing destination or format argument"
        let runPrintf : List CVal → ExecM CVal := fun vs =>
          match vs with
          | fmt :: args => do
              let fp ← asPtr fmt
              let m ← get
              let (_, source, off) ← liftEval (m.resolve fp 0)
              let rec takePrintfString : List CByte → Option (List CByte)
                | [] => none
                | .conc x :: rest =>
                    if x == 0 then some []
                    else (takePrintfString rest).map (fun tail => CByte.conc x :: tail)
                | _ => none
              let pattern ← match takePrintfString (source.bytes.drop off) with
                | some bytes => pure bytes
                | none => refuseUnsupported "printf: non-concrete or unterminated format"
              let printfHexDigit (upper : Bool) (d : Nat) : CByte :=
                if d < 10 then CByte.conc (UInt8.ofNat (48 + d))
                else CByte.conc (UInt8.ofNat ((if upper then 55 else 87) + d))
              let rec printfHexDigits (upper : Bool) (n : Nat) : List CByte :=
                if n < 16 then [printfHexDigit upper n]
                else printfHexDigits upper (n / 16) ++ [printfHexDigit upper (n % 16)]
                termination_by n
                decreasing_by exact Nat.div_lt_self (by omega) (by omega)
              let padHex (upper : Bool) (width n : Nat) : List CByte :=
                let digits := printfHexDigits upper n
                List.replicate (width - digits.length) (CByte.conc 48) ++ digits
              let rec format : List CByte → List CVal → ExecM (List CByte)
                | [], _ => pure []
                | .conc 37 :: .conc 37 :: rest, as => do
                    let tail ← format rest as
                    pure (CByte.conc 37 :: tail)
                | .conc 37 :: .conc 100 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 105 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 117 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 102 :: rest, a :: as => do
                    let rendered ← match formatFloatFixed6 a with
                      | some text => pure text
                      | none => refuseUnsupported "printf: non-finite or non-floating argument"
                    let tail ← format rest as
                    pure (rendered.toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 120 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let rendered := printfHexDigits false n.toNat
                    let tail ← format rest as
                    pure (rendered ++ tail)
                | .conc 37 :: .conc 88 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let rendered := printfHexDigits true n.toNat
                    let tail ← format rest as
                    pure (rendered ++ tail)
                | .conc 37 :: .conc 48 :: .conc 52 :: .conc 120 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let rendered := padHex false 4 n.toNat
                    let tail ← format rest as
                    pure (rendered ++ tail)
                | .conc 37 :: .conc 48 :: .conc 52 :: .conc 88 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let rendered := padHex true 4 n.toNat
                    let tail ← format rest as
                    pure (rendered ++ tail)
                | .conc 37 :: .conc 108 :: .conc 100 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 108 :: .conc 105 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 108 :: .conc 117 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 108 :: .conc 120 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure (printfHexDigits false n.toNat ++ tail)
                | .conc 37 :: .conc 108 :: .conc 108 :: .conc 100 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 108 :: .conc 108 :: .conc 105 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 108 :: .conc 108 :: .conc 117 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 108 :: .conc 108 :: .conc 120 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure (printfHexDigits false n.toNat ++ tail)
                | .conc 37 :: .conc 99 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure (CByte.conc (UInt8.ofNat n.toNat) :: tail)
                | .conc 37 :: .conc 115 :: rest, a :: as => do
                    let sp ← asPtr a
                    let current ← get
                    let (_, string, stringOff) ← liftEval (current.resolve sp 0)
                    let chars ← match takePrintfString (string.bytes.drop stringOff) with
                      | some bytes => pure bytes
                      | none => refuseUnsupported "printf: non-concrete or unterminated string argument"
                    let tail ← format rest as
                    pure (chars ++ tail)
                | .conc 37 :: .conc _ :: _, _ => refuseUnsupported "printf: unsupported format"
                | .conc 37 :: [], _ => refuseUnsupported "printf: trailing percent"
                | .conc b :: rest, as => do
                    let tail ← format rest as
                    pure (CByte.conc b :: tail)
                | _, _ => refuseUnsupported "printf: non-concrete format byte"
              let bytes ← format pattern args
              modify (fun mem => mem.emitStdout bytes)
              pure (.int IntTy.int_ bytes.length)
          | _ => refuseUnsupported "printf: missing format argument"
        let runVprintf : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [fmt, ap] => do
              let p ← asPtr ap
              let m ← get
              let args ← match Mem.vaValues m p with
                | .ok xs => pure xs
                | .error r => throw r
              runPrintf (fmt :: args)
          | _ => refuseUnsupported "vprintf: wrong argument count"
        let runVfprintf : List CVal → ExecM CVal := fun vs =>
          match vs with
          | stream :: fmt :: ap :: _ =>
              match stream, prog.stdoutObj with
              | .ptr p, some o =>
                  if p.obj == some o then runVprintf [fmt, ap]
                  else refuseUnsupported "vfprintf: non-stdout stream"
              | _, _ => refuseUnsupported "vfprintf: non-stdout stream"
          | _ => refuseUnsupported "vfprintf: wrong argument count"
        let runFprintf : List CVal → ExecM CVal := fun vs =>
          match vs with
          | stream :: fmt :: args =>
              match stream, prog.stdoutObj with
              | .ptr p, some o =>
                  if p.obj == some o then runPrintf (fmt :: args)
                  else refuseUnsupported "fprintf: non-stdout stream"
              | _, _ => refuseUnsupported "fprintf: non-stdout stream"
          | _ => refuseUnsupported "fprintf: wrong argument count"
        let runBuiltinStrcpy : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, src] => do
              let dp ← asPtr dst
              let sp ← asPtr src
              if dp.obj == sp.obj && dp.off == sp.off then
                refuseUnsupported "strcpy: overlapping source and destination"
              else do
                let m ← get
                let (_, source, off) ← liftEval (m.resolve sp 0)
                let rec takeString : List CByte → Option (List CByte)
                  | [] => none
                  | .conc x :: rest =>
                      if x == 0 then some [CByte.conc 0]
                      else (takeString rest).map (fun tail => CByte.conc x :: tail)
                  | _ => none
                match takeString (source.bytes.drop off) with
                | some bytes =>
                    liftEval (writeMem (fun mem => mem.storeBytes dp bytes))
                    pure (.ptr dp)
                | none => refuseUnsupported "__builtin_strcpy: non-concrete or unterminated string"
          | _ => refuseUnsupported "__builtin_strcpy: wrong argument count"
        let runStrcat : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, src] => do
              let dp ← asPtr dst
              let sp ← asPtr src
              let m ← get
              let (_, target, targetOff) ← liftEval (m.resolve dp 0)
              let (_, source, sourceOff) ← liftEval (m.resolve sp 0)
              let rec takeStringConcat : List CByte → Option (List CByte)
                | [] => none
                | .conc x :: rest =>
                    if x == 0 then some []
                    else (takeStringConcat rest).map (fun tail => CByte.conc x :: tail)
                | _ => none
              match takeStringConcat (target.bytes.drop targetOff),
                    takeStringConcat (source.bytes.drop sourceOff) with
              | some left, some right =>
                  liftEval (writeMem (fun mem =>
                    mem.storeBytes dp (left ++ right ++ [CByte.conc 0])))
                  pure (.ptr dp)
              | _, _ => refuseUnsupported "strcat: non-concrete or unterminated string"
          | _ => refuseUnsupported "strcat: wrong argument count"
        let runBuiltinExpect : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value, _] => pure value
          | _ => refuseUnsupported "__builtin_expect: wrong argument count"
        let runBuiltinPrefetch : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [_] | [_, _] | [_, _, _] => pure .undef
          | _ => refuseUnsupported "__builtin_prefetch: wrong argument count"
        let runStrcmp : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [left, right] => do
              let lp ← asPtr left
              let rp ← asPtr right
              let m ← get
              let (_, lo, loff) ← liftEval (m.resolve lp 0)
              let (_, ro, roff) ← liftEval (m.resolve rp 0)
              let rec cmpStr : List CByte → List CByte → Option Int
                | [], _ | _, [] => none
                | .conc x :: xs, .conc y :: ys =>
                    if x == 0 && y == 0 then some 0
                    else if x == 0 then some (-1)
                    else if y == 0 then some 1
                    else if x < y then some (-1)
                    else if x > y then some 1
                    else cmpStr xs ys
                | _, _ => none
              match cmpStr (lo.bytes.drop loff) (ro.bytes.drop roff) with
              | some v => pure (.int IntTy.int_ v)
              | none => refuseUnsupported "strcmp: non-concrete or unterminated string"
          | _ => refuseUnsupported "strcmp: wrong argument count"
        let runStrncmp : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [left, right, count] => do
              let lp ← asPtr left
              let rp ← asPtr right
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "strncmp: negative size"
              else do
                let m ← get
                let (_, lo, loff) ← liftEval (m.resolve lp 0)
                let (_, ro, roff) ← liftEval (m.resolve rp 0)
                let rec cmpStrncmp : Nat → List CByte → List CByte → Option Int
                  | 0, _, _ => some 0
                  | _, [], _ | _, _, [] => none
                  | k + 1, .conc x :: xs, .conc y :: ys =>
                      if x == 0 && y == 0 then some 0
                      else if x == 0 then some (-1)
                      else if y == 0 then some 1
                      else if x < y then some (-1)
                      else if x > y then some 1
                      else cmpStrncmp k xs ys
                  | _, _, _ => none
                match cmpStrncmp n.toNat (lo.bytes.drop loff) (ro.bytes.drop roff) with
                | some result => pure (.int IntTy.int_ result)
                | none => refuseUnsupported "strncmp: non-concrete string range"
          | _ => refuseUnsupported "strncmp: wrong argument count"
        let runMemcmp : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [left, right, count] => do
              let lp ← asPtr left
              let rp ← asPtr right
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "memcmp: negative size"
              else do
                let a ← liftEval (readMem (fun m => m.loadBytes lp n.toNat))
                let b ← liftEval (readMem (fun m => m.loadBytes rp n.toNat))
                let rec cmp : List CByte → List CByte → Option Int
                  | [], [] => some 0
                  | .conc x :: xs, .conc y :: ys =>
                      if x < y then some (-1)
                      else if x > y then some 1
                      else cmp xs ys
                  | _, _ => none
                match cmp a b with
                | some v => pure (.int IntTy.int_ v)
                | none => refuseUnsupported "memcmp: non-concrete byte"
          | _ => refuseUnsupported "memcmp: wrong argument count"
        let runStrlen : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [src] => do
              let sp ← asPtr src
              let m ← get
              let (_, source, off) ← liftEval (m.resolve sp 0)
              let rec scan : List CByte → Nat → Option Nat
                | [], _ => none
                | b :: rest, n =>
                    match b with
                    | .conc x => if x == 0 then some n else scan rest (n + 1)
                    | _ => none
              match scan (source.bytes.drop off) 0 with
              | some n => pure (.int IntTy.ulong n)
              | none => refuseUnsupported "strlen: no concrete NUL in object"
          | _ => refuseUnsupported "strlen: wrong argument count"
        let runStrnlen : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [src, limit] => do
              let sp ← asPtr src
              let (_, n) ← asInt limit
              if n < 0 then refuseUnsupported "strnlen: negative size"
              else do
                let m ← get
                let (_, source, off) ← liftEval (m.resolve sp 0)
                let rec scanN : List CByte → Nat → Nat → Option Nat
                  | _, 0, count => some count
                  | [], _, _ => none
                  | b :: rest, left, count =>
                      match b with
                      | .conc x => if x == 0 then some count else scanN rest (left - 1) (count + 1)
                      | _ => none
                match scanN (source.bytes.drop off) n.toNat 0 with
                | some k => pure (.int IntTy.ulong k)
                | none => refuseUnsupported "strnlen: non-concrete string range"
          | _ => refuseUnsupported "strnlen: wrong argument count"
        let runMemchr : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [src, needle, count] => do
              let sp ← asPtr src
              let (_, wanted) ← asInt needle
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "memchr: negative size"
              else do
                let m ← get
                let (_, source, off) ← liftEval (m.resolve sp 0)
                let rec find : List CByte → Nat → Option Nat
                  | _, 0 => none
                  | b :: rest, left =>
                      match b with
                      | .conc x => if x.toNat == (wanted % 256).toNat then some 0 else find rest (left - 1) |>.map (· + 1)
                      | _ => none
                  | [], _ => none
                match find (source.bytes.drop off) n.toNat with
                | some k => pure (.ptr { sp with off := sp.off + k })
                | none => pure (.ptr Ptr.null)
          | _ => refuseUnsupported "memchr: wrong argument count"
        let runStrchr : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [src, ch] => do
              let sp ← asPtr src
              let (_, needle) ← asInt ch
              let m ← get
              let (_, source, off) ← liftEval (m.resolve sp 0)
              let rec scanChar : List CByte → Nat → Option Nat
                | [], _ => none
                | b :: rest, n =>
                    match b with
                    | .conc x =>
                        if x.toNat == (needle % 256).toNat then some n
                        else if x == 0 then none
                        else scanChar rest (n + 1)
                    | _ => none
              match scanChar (source.bytes.drop off) 0 with
              | some n => pure (.ptr { sp with off := sp.off + n })
              | none => pure (.ptr Ptr.null)
          | _ => refuseUnsupported "strchr: wrong argument count"
        let runStrrchr : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [src, ch] => do
              let sp ← asPtr src
              let (_, needle) ← asInt ch
              let m ← get
              let (_, source, off) ← liftEval (m.resolve sp 0)
              let rec scanRr : List CByte → Nat → Option Nat → Option Nat
                | [], _, last => last
                | .conc x :: rest, n, last =>
                    if x == 0 then last
                    else scanRr rest (n + 1) (if x.toNat == (needle % 256).toNat then some n else last)
                | _, _, _ => none
              match scanRr (source.bytes.drop off) 0 none with
              | some n => pure (.ptr { sp with off := sp.off + n })
              | none => pure (.ptr Ptr.null)
          | _ => refuseUnsupported "strrchr: wrong argument count"
        let runAlloca : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [size] => do
              let (_, n) ← asInt size
              if n < 0 then refuseUnsupported "alloca: negative size"
              else do
                let m ← get
                let (m', o) := m.alloc .automatic n.toNat none
                set m'
                pure (.ptr (Ptr.toObject o))
          | _ => refuseUnsupported "alloca: wrong argument count"
        let runMalloc : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [size] => do
              let (_, n) ← asInt size
              if n ≤ 0 then refuseUnsupported "malloc: non-positive size"
              else do
                let m ← get
                let (m', p) := m.malloc n.toNat
                set m'
                pure (.ptr p)
          | _ => refuseUnsupported "malloc: wrong argument count"
        let runCalloc : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [count, size] => do
              let (_, n) ← asInt count
              let (_, sz) ← asInt size
              if n ≤ 0 || sz ≤ 0 then refuseUnsupported "calloc: non-positive size"
              else do
                let m ← get
                let (m', p) := m.calloc n.toNat sz.toNat
                set m'
                pure (.ptr p)
          | _ => refuseUnsupported "calloc: wrong argument count"
        let runFree : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let p ← asPtr value
              let m ← get
              match Mem.free m p with
              | .ok next => do
                  set next
                  pure .undef
              | .error r => throw r
          | _ => refuseUnsupported "free: wrong argument count"
        let runBitCount : String → List CVal → ExecM CVal := fun nm vs =>
          match vs with
          | [value] => do
              let (ty, n) ← asInt value
              let modulus := ty.modulus
              let residue := (n % modulus + modulus) % modulus
              if residue == 0 && (nm.contains "ctz" || nm.contains "clz") then
                refuseUnsupported s!"{nm}: zero argument"
              else
                let indexes := List.range ty.bits
                let ones := indexes.foldl
                  (fun acc i => acc + ((residue / ((2 : Int) ^ i)) % 2).toNat) 0
                let trailing := indexes.takeWhile
                  (fun i => ((residue / ((2 : Int) ^ i)) % 2) == 0) |>.length
                let leading := indexes.reverse.takeWhile
                  (fun i => ((residue / ((2 : Int) ^ i)) % 2) == 0) |>.length
                let signedValue := IntTy.wrap { ty with signed := true } residue
                let signBit := if signedValue < 0 then 1 else 0
                let redundant := (List.range (ty.bits - 1)).reverse.takeWhile
                  (fun i => ((residue / ((2 : Int) ^ i)) % 2) == signBit) |>.length
                let result :=
                  if nm.contains "popcount" then ones
                  else if nm.contains "parity" then ones % 2
                  else if nm.contains "ctz" then trailing
                  else if nm.contains "clrsb" then redundant
                  else leading
                pure (.int IntTy.int_ result)
          | _ => refuseUnsupported s!"{nm}: wrong argument count"
        let runFfs : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let (ty, n) ← asInt value
              let m := ty.modulus
              let residue := (n % m + m) % m
              let rec first (bits : Nat) (index : Nat) : Nat :=
                if bits == 0 then 0
                else if bits % 2 == 1 then index + 1
                else if h : bits ≥ 2 then
                  first (bits / 2) (index + 1)
                else 0
                termination_by bits
                decreasing_by omega
              pure (.int IntTy.int_ (first residue.toNat 0))
          | _ => refuseUnsupported "__builtin_ffs: wrong argument count"
        -- GCC/Clang's fixed-width byte-swap builtins are value operations,
        -- not library calls.  Their signatures are parser-resolved in the
        -- admitted slice: unsigned short and unsigned int respectively.
        let runBswap16 : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let (t, n) ← asInt value
              if t != IntTy.ushort then
                refuseUnsupported "__builtin_bswap16: argument is not unsigned short"
              else
                let lo := n % 256
                let hi := n / 256
                pure (.int IntTy.ushort (lo * 256 + hi))
          | _ => refuseUnsupported "__builtin_bswap16: wrong argument count"
        let runBswap32 : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let (t, n) ← asInt value
              if t != IntTy.uint then
                refuseUnsupported "__builtin_bswap32: argument is not unsigned int"
              else
                let b0 := n % 256
                let b1 := (n / 256) % 256
                let b2 := (n / 65536) % 256
                let b3 := (n / 16777216) % 256
                pure (.int IntTy.uint
                  (b0 * 16777216 + b1 * 65536 + b2 * 256 + b3))
          | _ => refuseUnsupported "__builtin_bswap32: wrong argument count"
        let runBswap64 : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let (t, n) ← asInt value
              if t != IntTy.ulong then
                refuseUnsupported "__builtin_bswap64: argument is not unsigned long long"
              else
                let b0 := n % 256
                let b1 := (n / 256) % 256
                let b2 := (n / 65536) % 256
                let b3 := (n / 16777216) % 256
                let b4 := (n / 4294967296) % 256
                let b5 := (n / 1099511627776) % 256
                let b6 := (n / 281474976710656) % 256
                let b7 := (n / 72057594037927936) % 256
                pure (.int IntTy.ulong
                  (b0 * 72057594037927936 + b1 * 281474976710656 +
                   b2 * 1099511627776 + b3 * 4294967296 + b4 * 16777216 +
                   b5 * 65536 + b6 * 256 + b7))
          | _ => refuseUnsupported "__builtin_bswap64: wrong argument count"
        let runInf : String → List CVal → ExecM CVal := fun nm vs =>
          match vs with
          | [] =>
              -- The unsuffixed spelling itself ends in the letter `f`
              -- (`inf`), so suffix testing would misclassify
              -- `__builtin_inf` as binary32.  The C builtin family has
              -- exact names: `inf` is binary64, `inff` is binary32, and
              -- `infl` is long double (§7.12.3).
              if nm == "__builtin_inff" || nm == "__builtin_huge_valf" then
                pure (.float32 (Float32.Model.ofBits (UInt32.ofNat 0x7f800000)))
              else if nm == "__builtin_infl" || nm == "__builtin_huge_vall" then
                refuseUnsupported s!"{nm}: long double is outside the profile"
              else
                pure (.float64 (Float.Model.ofBits (UInt64.ofNat 0x7ff0000000000000)))
          | _ => refuseUnsupported s!"{nm}: wrong argument count"
        -- C23 §7.12.3 classification macros, represented by Clang as
        -- builtin calls.  The predicates inspect the exact parser-backed
        -- IEEE value; no host floating-point behavior is consulted.
        let runFloatClass : String → List CVal → ExecM CVal := fun nm vs =>
          match vs with
          | [value] =>
              let finite : Bool := match value with
                | .float32 f => !f.isNaN && !f.isInf
                | .float64 f => !f.isNaN && !f.isInf
                | _ => false
              let result := if nm == "__builtin_isnan" then
                  match value with
                  | .float32 f => f.isNaN
                  | .float64 f => f.isNaN
                  | _ => false
                else if nm == "__builtin_isinf" then
                  match value with
                  | .float32 f => f.isInf
                  | .float64 f => f.isInf
                  | _ => false
                else if nm == "__builtin_signbit" then
                  match value with
                  | .float32 f => (f.toBits &&& (UInt32.ofNat 0x80000000)) != 0
                  | .float64 f => (f.toBits &&& (UInt64.ofNat 0x8000000000000000)) != 0
                  | _ => false
                else finite
              match value with
              | .float32 _ | .float64 _ => pure (.int IntTy.int_ (if result then 1 else 0))
              | _ => refuseUnsupported s!"{nm}: expected a binary floating argument"
          | _ => refuseUnsupported s!"{nm}: wrong argument count"
        let runFloatUnordered : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [a, b] =>
              let nan : CVal → Bool
                | .float32 f => f.isNaN
                | .float64 f => f.isNaN
                | _ => false
              match a, b with
              | .float32 _, .float32 _ | .float64 _, .float64 _ =>
                  pure (.int IntTy.int_ (if nan a || nan b then 1 else 0))
              | _, _ => refuseUnsupported "__builtin_isunordered: incompatible floating types"
          | _ => refuseUnsupported "__builtin_isunordered: wrong argument count"
        let runFloatAbs : String → List CVal → ExecM CVal := fun nm vs =>
          match vs with
          | [.float32 f] =>
              if nm == "__builtin_fabsf" || nm == "fabsf" then pure (.float32 f.abs)
              else refuseUnsupported s!"{nm}: expected binary64 argument"
          | [.float64 f] =>
              if nm == "__builtin_fabs" || nm == "fabs" then pure (.float64 f.abs)
              else refuseUnsupported s!"{nm}: expected binary32 argument"
          | [_] => refuseUnsupported s!"{nm}: unsupported floating argument"
          | _ => refuseUnsupported s!"{nm}: wrong argument count"
        let runFloatFloor : String → List CVal → ExecM CVal := fun nm vs =>
          let floorQ := fun q : LeanModels.SoftFloat.Q =>
            Int.ediv q.num (q.den : Int)
          match vs with
          | [.float32 f] =>
              if nm == "floorf" then
                match LeanModels.SoftFloat.valQ (Float32.Model.unpack f) with
                | some q => pure (.float32 (Float32.Model.ofInt (floorQ q)))
                | none => refuseUnsupported s!"{nm}: non-finite argument"
              else refuseUnsupported s!"{nm}: expected binary64 argument"
          | [.float64 f] =>
              if nm == "floor" then
                match LeanModels.SoftFloat.valQ (Float.Model.unpack f) with
                | some q => pure (.float64 (Float.Model.ofInt (floorQ q)))
                | none => refuseUnsupported s!"{nm}: non-finite argument"
              else refuseUnsupported s!"{nm}: expected binary32 argument"
          | _ => refuseUnsupported s!"{nm}: unsupported argument types"
        let runFloatNan : String → List CVal → ExecM CVal := fun nm vs =>
          match vs with
          | [_] =>
              if nm == "__builtin_nanf" then
                pure (.float32 (Float32.Model.ofBits (UInt32.ofNat 0x7fc00000)))
              else if nm == "__builtin_nan" then
                pure (.float64 (Float.Model.ofBits (UInt64.ofNat 0x7ff8000000000000)))
              else refuseUnsupported s!"{nm}: long double NaN is outside the profile"
          | _ => refuseUnsupported s!"{nm}: wrong argument count"
        let runCopySign : String → List CVal → ExecM CVal := fun nm vs =>
          match vs with
          | [.float32 a, .float32 b] =>
              if nm == "__builtin_copysignf" then
                let mag := a.toBits &&& UInt32.ofNat 0x7fffffff
                let sign := b.toBits &&& UInt32.ofNat 0x80000000
                pure (.float32 (Float32.Model.ofBits (mag ||| sign)))
              else refuseUnsupported s!"{nm}: expected binary64 arguments"
          | [.float64 a, .float64 b] =>
              if nm == "__builtin_copysign" then
                let mag := a.toBits &&& UInt64.ofNat 0x7fffffffffffffff
                let sign := b.toBits &&& UInt64.ofNat 0x8000000000000000
                pure (.float64 (Float.Model.ofBits (mag ||| sign)))
              else refuseUnsupported s!"{nm}: expected binary32 arguments"
          | _ => refuseUnsupported s!"{nm}: unsupported argument types"
        let runAbs : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let (t, n) ← asInt value
              if t != IntTy.int_ then
                refuseUnsupported "__builtin_abs: argument is not int"
              else if n == t.minVal then
                refuseValue (.signedOverflow "abs" t n)
              else
                pure (.int IntTy.int_ (if n < 0 then -n else n))
          | _ => refuseUnsupported "__builtin_abs: wrong argument count"
        let runSyncAdd8 : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, value] => do
              let dp ← asPtr dst
              let (vt, y) ← asInt value
              if vt != IntTy.ulong then
                refuseUnsupported "__sync_add_and_fetch_8: argument is not unsigned long long"
              else
                let m ← get
                let (ty, structured) ← match dp.obj with
                  | some o =>
                      match m.get? o with
                      | some c =>
                          match c.effTy, m.structuredType? o with
                          | some t, some q => pure (t, some q)
                          | _, _ => refuseUnsupported "__sync_add_and_fetch_8: destination lacks parser-native type"
                      | none => refuseUnsupported "__sync_add_and_fetch_8: destination object is not live"
                  | none => refuseUnsupported "__sync_add_and_fetch_8: null destination"
                let t ← liftEval (intTyOfNode structured)
                if t != IntTy.ulong then
                  refuseUnsupported "__sync_add_and_fetch_8: destination is not unsigned long long"
                else do
                  let old ← liftEval (loadAt Mem.cAliasModel dp ty none structured
                    prog.layout.zeroNullPointer)
                  let (_, x) ← asInt old
                  let result := t.wrap (x + y)
                  liftEval (storeAt Mem.cAliasModel dp ty (.int t result) structured)
                  pure (.int t result)
          | _ => refuseUnsupported "__sync_add_and_fetch_8: wrong argument count"
        let runArithOverflow (op : String) : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [a, b, dst] => do
              let (_, x) ← asInt a
              let (_, y) ← asInt b
              let dp ← asPtr dst
              let m ← get
              let (ty, structured) ← match dp.obj with
                | some o =>
                    match m.get? o with
                    | some c =>
                          match c.effTy, m.structuredType? o with
                          | some t, some q => pure (t, some q)
                          | _, _ => refuseUnsupported "__builtin_mul_overflow: destination lacks parser-native type"
                    | none => refuseUnsupported "__builtin_mul_overflow: destination object is not live"
                | none => refuseUnsupported "__builtin_mul_overflow: null destination"
              let t ← liftEval (intTyOfNode structured)
              let result := if op == "add" then x + y else x * y
              let overflow := !t.inRange result
              liftEval (storeAt Mem.cAliasModel dp ty (.int t (t.wrap result)) structured)
              pure (.int IntTy.int_ (if overflow then 1 else 0))
          | _ => refuseUnsupported s!"__builtin_{op}_overflow: wrong argument count"
        let runVaStart : List CVal → ExecM CVal := fun vs =>
          match vs with
          | ap :: _ => do
              let p ← asPtr ap
              liftEval (writeMem (fun m => Mem.vaStart m p extraArgs))
              pure .undef
          | _ => refuseUnsupported "va_start: missing va_list"
        let runVaCopy : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, src] => do
              let dp ← asPtr dst
              let sp ← asPtr src
              liftEval (writeMem (fun m => Mem.vaCopy m dp sp))
              pure .undef
          | _ => refuseUnsupported "va_copy: wrong argument count"
        let runVaEnd : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [ap] => do
              let p ← asPtr ap
              liftEval (writeMem (fun m => Mem.vaEnd m p))
              pure .undef
          | _ => refuseUnsupported "va_end: wrong argument count"
        /- Profile-indexed external-function registry. Translation-unit
        definitions are resolved by declaration identity before this helper,
        so a registry arm can never shadow a definition from the unit (H5). -/
        let runExternal : String → List CVal → ExecM CVal := fun nm vs =>
          if nm == "__builtin_strcmp" || nm == "strcmp" then
            runStrcmp vs
          else if nm == "__builtin_va_start" || nm == "__builtin_c23_va_start" then
            runVaStart vs
          else if nm == "__builtin_va_copy" then
            runVaCopy vs
          else if nm == "__builtin_va_end" then
            runVaEnd vs
          else if nm == "__builtin_sprintf" || nm == "sprintf" then
            runSprintf vs
          else if nm == "__builtin_strcpy" || nm == "strcpy" then
            runBuiltinStrcpy vs
          else if nm == "strncmp" || nm == "__builtin_strncmp" then
            runStrncmp vs
          else if nm == "strncpy" || nm == "__builtin_strncpy" then
            runStrncpy vs
          else if nm == "strcat" || nm == "__builtin_strcat" then
            runStrcat vs
          else if nm == "strlen" then
            runStrlen vs
          else if nm == "__builtin_bswap16" then
            runBswap16 vs
          else if nm == "__builtin_bswap32" then
            runBswap32 vs
          else if nm == "__builtin_bswap64" then
            runBswap64 vs
                else if nm == "__builtin_fabs" || nm == "__builtin_fabsf" || nm == "__builtin_fabsl" || nm == "fabs" || nm == "fabsf" then runFloatAbs nm vs
                else if nm == "floor" || nm == "floorf" then runFloatFloor nm vs
                else if nm == "__builtin_nanf" || nm == "__builtin_nan" || nm == "__builtin_nanl" then runFloatNan nm vs
                else if nm == "__builtin_copysign" || nm == "__builtin_copysignf" then runCopySign nm vs
                else if nm == "__builtin_isfinite" || nm == "__builtin_isnan" || nm == "__builtin_isinf" || nm == "__builtin_signbit" then runFloatClass nm vs
                else if nm == "__builtin_isunordered" then runFloatUnordered vs
                else if nm == "__builtin_inf" || nm == "__builtin_inff" || nm == "__builtin_infl" || nm == "__builtin_huge_val" || nm == "__builtin_huge_valf" || nm == "__builtin_huge_vall" then
                  runInf nm vs
          else if nm == "__builtin_abs" || nm == "abs" then
            runAbs vs
          else if nm == "__sync_add_and_fetch_8" then
            runSyncAdd8 vs
          else if nm == "__builtin_expect" then
            runBuiltinExpect vs
          else if nm == "__builtin_prefetch" then
            runBuiltinPrefetch vs
          else if nm == "strchr" then
            runStrchr vs
          else if nm == "strrchr" then
            runStrrchr vs
          else if nm == "printf" || nm == "__builtin_printf" then
            runPrintf vs
          else if nm == "putchar" || nm == "__builtin_putchar" then
            runPutchar vs
          else if nm == "puts" || nm == "__builtin_puts" then
            runPuts vs
          else if nm == "fprintf" || nm == "__builtin_fprintf" then
            runFprintf vs
          else if nm == "vprintf" || nm == "__builtin_vprintf" then
            runVprintf vs
          else if nm == "vfprintf" || nm == "__builtin_vfprintf" then
            runVfprintf vs
          else if nm == "__builtin_abort" || nm == "abort" then
            terminateAbort
          else if nm == "__builtin_exit" || nm == "exit" then
            throw (.libc "exit")
          else if nm == "memset" || nm == "__builtin_memset" then runMemset vs
          else if nm == "memcpy" || nm == "__builtin_memcpy" then runMemcpy vs
          else if nm == "mempcpy" || nm == "__builtin_mempcpy" then runMempcpy vs
          else if nm == "fprintf" || nm == "__builtin_fprintf" then runFprintf vs
          else if nm == "vfprintf" || nm == "__builtin_vfprintf" then runVfprintf vs
          else if nm == "memmove" || nm == "__builtin_memmove" then runMemmove vs
          else if nm == "__builtin_strcmp" then runStrcmp vs
          else if nm == "__builtin_memcmp" || nm == "memcmp" then runMemcmp vs
          else if nm == "__builtin_strlen" then runStrlen vs
          else if nm == "strnlen" || nm == "__builtin_strnlen" then runStrnlen vs
          else if nm == "memchr" || nm == "__builtin_memchr" then runMemchr vs
          else if nm == "__builtin_alloca" then runAlloca vs
          else if nm == "malloc" || nm == "__builtin_malloc" then runMalloc vs
          else if nm == "calloc" || nm == "__builtin_calloc" then runCalloc vs
          else if nm == "free" || nm == "__builtin_free" then runFree vs
          else if nm.contains "ctz" || nm.contains "clz" || nm.contains "clrsb" || nm.contains "popcount" || nm.contains "parity" then runBitCount nm vs
          else if nm == "__builtin_ffs" || nm.contains "ffs" then runFfs vs
          else if nm == "__builtin_mul_overflow" then runArithOverflow "mul" vs
          else if nm == "__builtin_add_overflow" then runArithOverflow "add" vs
          else throw (.libc nm)
        -- The callee's own call handler: one fuel less, so recursion
        -- terminates on the fuel and on nothing else.
        let handler : CallHandler := fun callee indirect arguments =>
          match indirect with
          | some (.funPtr declaration) =>
              match prog.findId? declaration with
              | some g => callFn fuel prog g arguments
              | none => refuseUnsupported s!"indirect function pointer declaration '{declaration.value}' is not defined"
          | some _ => refuseUnsupported "indirect call through a non-function value"
          | none => match calleeId callee with
          | some declaration =>
            -- H5: a translation-unit definition wins over the registry.
            match prog.findId? declaration with
            | some g => callFn fuel prog g arguments
            | none =>
              match calleeName callee with
              | some nm => runExternal nm (arguments.map CallArgument.value)
              | none => throw (.libc declaration.value)
          | none => match calleeName callee with
          | none =>
            -- A DeclRefExpr to a local variable is not a function call target.
            -- Do not redo clang's resolved declaration identity by its name.
            refuseUnsupported "indirect call through a non-FunctionDecl reference"
          | some nm => match prog.find? nm with
            | none => runExternal nm (arguments.map CallArgument.value)
            | some g => callFn fuel prog g arguments
        -- §6.2.1p4: the frame starts with the file-scope objects in scope,
        -- and the parameters are bound ON TOP of them, so a parameter that
        -- shadows a global wins by being consed later.
        let ctx0 : Ctx :=
          ({ env := prog.globals, idEnv := prog.globalIds, enums := prog.enums,
             enumIds := prog.enumIds, layout := prog.layout,
             call := handler,
             callPure := fun callee =>
               match calleeId callee with
               | some declaration =>
                   match prog.findId? declaration with
                   | some g => functionCallFree g
                   | none => false
               | none => false,
             functionBody := some (match body with
               | .compound statements _ => statements
               | statement => [statement]),
             uninitializedRegisterCandidate := uninitializedRegisterCandidate body,
             stdoutObj := prog.stdoutObj } : Ctx).withCompoundInit
        let ctx ← bindParams prog.layout ctx0 f.params fixedArgs
        let flow ← execStmt fuel ctx body
        let m₁ ← get
        set (m₁.killFrom base)
        match flow with
        | .ret (some v) => pure v
        | .ret none => pure .undef
        -- §5.1.2.3.4: falling off the end of a non-void function is
        -- undefined ONLY if the caller uses the value; `main` is the
        -- exception and returns 0. Neither is decided here.
        | .normal => pure .undef
        | _ => refuseUnsupported "break, continue or goto escaped a function body"

/-- Call by NAME — the entry point a scoreboard uses. -/
def callByName (fuel : Nat) (prog : Program) (name : String) (args : List CVal) :
    ExecM CVal :=
  match prog.find? name with
  | some f =>
      -- C23 §5.1.2.2.1 permits the hosted two-parameter form of `main`.
      -- The runner starts the program with the executable name as argv[0],
      -- so argc is one.  The argv object itself is not modelled yet; passing
      -- a null pointer keeps any dereference loud through the existing
      -- provenance checks.  This exception is only for the entrypoint: an
      -- ordinary function with omitted arguments remains a refusal.
      let startupArgs :=
        if name == "main" && args.isEmpty && f.params.length == 2 then
          [.int IntTy.int_ 1, .ptr Ptr.null]
        else args
      callFn fuel prog f (startupArgs.map fun value => ⟨value, none⟩)
  | none => refuseUnsupported s!"no definition for '{name}'"

/-! ## `fuelMono` — still an obligation, and now with a known technique

The lemma every `∃ n, ∀ fuel ≥ n` argument rests on
(`docs/c-semantics-design.md` §4.2): more fuel never changes a decided
answer.

**NOT PROVED HERE, and the reason is worth recording rather than
apologising for.**

*The technique is no longer open.* `LeanModels/Sv/Obs.lean` already
solves this exact problem: a flat approximation order `⊑` with `timeout`
at the bottom, `fuelMono` stated as ONE CONJUNCTION over the whole mutual
block, proved by induction on fuel with a `le_bind` congruence doing the
work at each operator. **96 lines for four functions.** This lane should
LIFT that machinery, not write a second copy of it — the `⊑` order and
its bind congruence are generic in the result type, and a second
hand-rolled monotonicity order is precisely the duplication
`docs/family-architecture.md` §9.2 exists to stop.

*What makes it more than a transcription here.* This mutual block is TEN
functions, not four — `execStmt`, `execBlock`, `execLoop`, `declare`,
`initObject`, `initElems`, `initMembers`, `zeroInitStructured`, `zeroElems`,
`zeroMembers` — so the conjunction has ten conjuncts. And where SV's
functions return a result directly, these return a MONADIC value, so
monotonicity is pointwise in the memory: `∀ m, run m (f fuel …) ⊑ run m
(f fuel' …)`. Both are mechanical against the template; neither is free.

*Why it was not attempted in this session, specifically.* Proof
iteration needs many short Lean runs, and under build-lock Amendment 11
every one of them needs a tenure — which cost this lane **88 minutes** of
FIFO queueing on its last landing. A 300-line proof developed at one
compile per tenure is not a session's work; it is a week's. **That is the
lock's real cost on PROOF work as distinct from build verification**, and
it is a different shape of problem from the starvation the ticket queue
fixed. Reported rather than worked around.

So the obligation is stated as a `Prop` below — visible, named, and
impossible to mistake for a theorem. -/

/-- More fuel never turns a decided answer into a different one.

`Loud.timeout` is the bottom: a run that exhausted its fuel may become
anything at higher fuel, and a run that DECIDED keeps its exact answer,
memory included. -/
def FuelMono : Prop :=
  ∀ (fuel : Nat) (ctx : Ctx) (s : Stmt) (m : Mem) (r : Except Refusal Flow) (m' : Mem),
    ExecM.run m (execStmt fuel ctx s) = .ok (r, m') →
    ∀ fuel' ≥ fuel, ExecM.run m (execStmt fuel' ctx s) = .ok (r, m')

end LeanModels.C.C23
