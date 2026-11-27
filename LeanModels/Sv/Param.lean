import LeanModels.Sv.Obs
import LeanModels.Sv.Sem2

/-!
# SV parametric design layer (`LeanModels.Sv` — schema sv-0.2, phase 2)

The Lean side of the CV32E40P phase-1 symbolic envelopes
(`docs/sv-envelope-schema.md`, "Symbolic mode — schema sv-0.2"): a
**parametric** design AST (`PDesign`) whose parameters stay symbolic and
whose generate constructs stay structural, plus the proof-relevant
elaboration function

```
PDesign.instantiate : PDesign → List Int → (iterFuel : Nat) → Res Design
```

that substitutes concrete parameter values and expands `GenerateFor`
families into the **existing M0 `Design`** — so instantiated designs run
under the untouched M0 cycle semantics (`Semantics.lean`), and everything
outside the M0 tier arrives there as loud `.unsupported` nodes exactly as
before. This file deliberately imports no `Lean.Json`: JSON ingestion of
sv-0.2 envelopes lives in `Ingest2.lean`; theorems only ever mention the
types and functions here.

Design laws implemented (the point of the program):

* **Parameters stay symbolic.** A parameterized module is data
  (`PDesign`); a Design-valued *function* of its parameters is
  `fun args => d.instantiateD args` (the `load_design_sv2` command in
  `Ingest2.lean` binds it with named `Nat` binders in declaration order).
  ∀-parameter theorems quantify over the arguments of `instantiate`.
* **Generate stays structural.** `GenItem.genFor` is ONE constructor
  (genvar, symbolic init/bound/step, body template). Expansion is
  recursion over the genvar value sequence (`genvarSeq`), so proofs about
  generate families go by induction on that sequence — the
  `expandIters_*` and `genvarSeq_*` lemmas below are the induction
  handles (the analog lane's `chain : Nat → Netlist` precedent,
  `LeanModels/Spice/RippleNetlist.lean`, generalized to source-extracted
  families).

`LVec.ofInt w v`, the vector an integer becomes at a `w`-bit context, is the
known vector `LVec.ofBitVec (BitVec.ofInt w v)` (`LVec.ofInt_eq_ofBitVec`, not
`@[simp]`: instantiation proofs keep the literals folded).

Representation deviations from the M0 `Ast.lean` conventions, both
deliberate: (1) the parametric layer uses **`List`** (not `Array`) for
every recursive field — nested-inductive structural recursion and the
expansion lemmas are far cleaner over `List`, and `instantiate` converts
to `Array` at the M0 boundary; (2) `SysCall` carries exactly **one**
argument (all four supported system functions are unary; the parser
enforces arity).

## Semantic decisions (the honest ledger)

* **Constant tier** (`evalInt`): parameter defaults, localparams,
  generate headers/conditions, dimension bounds, select labels. Two
  regimes, chosen per node by the syntactic INT class (`PExpr.isInt`):
  - **INT class** — unsized integers, genvars, system-call results, and
    parameters bound in `IEnv.vals` (untyped, or typed `int`/`integer`:
    32-bit signed), closed under `+ - * / % ** << >> <<< >>> & | ^`,
    unary `- +` and `?:`. Evaluated over **mathematical `Int`** (no
    32-bit wrap: no CV32E40P parameter comes near it — recorded
    restriction). `/` `%` truncate toward zero (`Int.tdiv`/`Int.tmod`,
    the SV rule), `**` requires a nonnegative exponent, `>>` requires a
    nonnegative operand (logical shift of a negative constant is
    width-dependent — loud error instead), `>>>` is arithmetic
    (`Int.fdiv`). Comparisons over two INT operands compare the
    mathematical values (32-bit signed on both sides).
  - **Everything else** — any operand that is a sized literal (unsigned
    at its own width), a parameter typed narrower than 32 bits or
    unsigned (bound in `IEnv.nvals` with its width and signedness), a
    `Resize`, a cast, a comparison result (1-bit unsigned), a constant
    select — goes to `evalSized`, the IEEE 1800-2023 §11.6/§11.8 rules
    verbatim: self-determined type bottom-up (`ctype`), the type
    propagated to context-determined operands, operands extended
    (sign-extended only under a signed propagated type), every result
    wrapped to the propagated width (`canonInt`). This is what makes
    `K + 3'd4` with `K = 3'd5` evaluate to `1`, as in every simulator,
    not `9` (verifier finding 2026-10-28). slang's elaborated tree
    carries context propagation as `Resize` nodes (and, in a parametric
    family, resized literals), but their widths are the DEFAULT point's
    (round 3 repair): `ctype` reads a conversion as its operand's own
    type (a 4-state → 2-state `Squash2` too, round 5, and the context
    reaches through one, round 6: `PExpr.ctxPropagates`), `evalAt` converts
    to the context it is given, and the context
    of a root is supplied — the declared width of a typed localparam or
    parameter default at THESE parameters (`evalAssign`), 32 bits for an
    `integer`/`int` one (`evalIntTarget`, round 4), the root's own width
    for a self-determined root (`evalSized`), and, where the tree records
    an outside assignment-like target (a conversion at the root — a genvar
    initializer, an INT-class override into a typed parameter wider than
    32 bits), the own-width value where the target's reading agrees and a loud refusal
    where it differs (`PExpr.pushedTarget`, round 4: the oracles split).
    An untyped parameter default or localparam whose own-type value wraps
    is loud (`evalUntyped`, round 5: Icarus 12.0 evaluates it losslessly),
    and so, since round 6, is every one built with `+ - * **` on its
    context chain, whatever its value (`PExpr.icarusWidens`: Icarus 12.0
    gives it a lossless WIDTH — `N + 1` is 33 bits there, 32 in slang and
    Yosys 0.53 — which shows wherever the width does).
    Division/modulo by zero, x/z operands and out-of-range constant
    selects read x — loud in this tier.
  `parameter int unsigned`, `logic [31:0]` and other typed parameters
  are NOT `int` — the envelope's `signed` field (absent = signed exactly
  when the declared width is 32, a rule only a type of literal bounds may
  rely on, round 5) decides the class (`declConstType`); a
  ranged parameter without a type (`parameter [3:0] V`) is typed.
* **Untyped parameters** take the type of their final value (§6.20.2):
  `instantiate`/`instantiate2` read every argument as an integer OVERRIDE
  (an `int`); `PDesign.atPoint` models a point where some are NOT
  overridden by retyping those to their default's type, and a
  value-position read of one that IS overridden while its default was not
  `int`-typed is loud (`PParam.overrideRetypes`, `IEnv.stale`) — the
  envelope's value tree was typed at the default.
* **32-bit `int` overflow** is not modelled on the fast path;
  `IEnv.int32` evaluates INT parameters width-exactly instead, and
  `Param2.lean`'s `PDesign.int32Agrees` compares the two instantiations
  (the differential runner and `load_design_sv2` refuse a mismatch).
* **`$clog2`** is `Sv.clog2` (ceiling log2, `clog2 0 = clog2 1 = 0` —
  the LRM's `$clog2`); **`$bits`/`$size`** of a *declared signal* is its
  instantiated width; **`$high`** of a declared signal is `width - 1`
  (the tier's packed ranges are `[W-1:0]`). Anything else (type
  arguments, expression arguments) is a loud error.
* **Widths.** Declared widths come from the symbolic `PackedType` bounds
  (`|msb - lsb| + 1` per dimension, multi-dim = product — a packed array
  is one bit vector). Declarations elaborate **in order**: a
  `$bits`/`$high` in a bound may reference earlier declarations only.
* **Value positions** instantiate context-width-directed: `Int`/`Fill`/
  `ParamRef`/`GenvarRef` literals materialize at the context width
  (assignment target's declared width; operands of arithmetic inherit
  it; comparison operands take the max of the operand self-widths — the
  LRM §11.6 rules restricted to this vocabulary; a fill with no
  determinable width is loud). Symbolic-only operators (`* / % ** <<
  …`), in a value position, constant-fold when closed over
  parameters and are loud otherwise (T-ops tier).
* **`Resize`** (width-changing implicit conversion, unsigned): its
  envelope width is **default-elaborated** (slang folds the target
  type), so it is honored only when it matches the context width at the
  *current* parameters — zero-extension becomes an M0 `concat` with a
  zero literal; truncation and any width mismatch are loud
  (`Resize:truncate` / `Resize:context`). This is a recorded envelope
  limitation, not paper-over: at non-default parameters the affected
  expression is `.unsupported`, never silently mis-sized.
* **`Squash2`** (4-state → 2-state) is outside the M0 value core — loud.
* **Enums** bind as literal values at the enum's base width (`EnumRef` →
  `Expr.lit`); the member table is data, never folded away at parse
  time.
* **Generate-local declarations** are outside this slice (they need
  per-instance name scoping) — they arrive as loud items. Neither smoke
  envelope contains one.
* **Package constants** (`PDesign.packageParams`) are bound before the
  module parameters, in dependency order, each at its declared width and
  signedness with its x/z bits (`bindPackageParams`, "Constant functions and
  package constants" below).  A constant that cannot be evaluated is left
  unbound with its reason, and a `ParamRef` to it is loud at use
  (`ParamRef:package`).
* **Constant functions** (IEEE 1800-2023 §13.4.3) are executed as written
  (`PFunction.stmts`, `execFnStmt`), in package constants, parameter defaults,
  localparams and generate-local parameters.
* `instantiate` is **fueled only where unbounded**: the genvar iteration
  (`genvarSeq`, fuel exhausted = `.timeout`); everything else is
  structural recursion. Bad parameters (arity, failing localparam/width/
  bound evaluation) are `.unsupported` with a message — loud `Res`, the
  M0 discipline.
-/

namespace LeanModels.Sv

/-! ## `$clog2` and integer-valued vector embedding -/

/-- Ceiling log2 — the LRM's `$clog2`: least `k` with `n ≤ 2^k`
(`clog2 0 = clog2 1 = 0`). -/
def clog2 (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

#guard clog2 0 == 0
#guard clog2 1 == 0
#guard clog2 2 == 1
#guard clog2 3 == 2
#guard clog2 8 == 3
#guard clog2 9 == 4
#guard clog2 32 == 5
#guard clog2 33 == 6

/-- Two's-complement embedding of an `Int` at width `w` (negative values
wrap mod `2^w`, the SV rule for sized contexts). -/
def LVec.ofInt (w : Nat) (v : Int) : LVec := .ofNat w (v.emod ((2 : Int) ^ w)).toNat

/-- `LVec.ofInt w v` is the known vector of `BitVec.ofInt w v`. Not `@[simp]`: instantiation proofs keep
`LVec.ofInt` literals folded. -/
theorem LVec.ofInt_eq_ofBitVec (w : Nat) (v : Int) : LVec.ofInt w v = LVec.ofBitVec (BitVec.ofInt w v) := by
  rw [LVec.ofInt, LVec.ofBitVec, BitVec.toNat_ofInt, Int.natCast_pow, Int.cast_ofNat_Int]
  rfl

#guard (LVec.ofInt 4 5).toBinString == "0101"
#guard (LVec.ofInt 4 (-1)).toBinString == "1111"
#guard (LVec.ofInt 4 (-8)).toBinString == "1000"
#guard (LVec.ofInt 8 256).toBinString == "00000000"

/-! ## The symbolic vocabulary -/

/-- Binary operators of the sv-0.2 envelope: the M0 set (`.m0`), integer
and runtime multiplication (`*`), constant-position extras (`/ % ** << >> <<< >>>`), signed order
comparisons (spelled `s<` … by the extractor), and the legacy spellings of
case equality and logical operators. Wildcard comparisons use `.m0`. -/
inductive SymBinOp where
  | m0 (op : BinOp)
  | mul   -- `*`
  | div   -- `/`
  | mod   -- `%`
  | pow   -- `**`
  | shl   -- `<<`
  | shr   -- `>>`
  | ashl  -- `<<<`
  | ashr  -- `>>>`
  | slt   -- `s<`  (signed `<`)
  | sle   -- `s<=`
  | sgt   -- `s>`
  | sge   -- `s>=`
  | ceq   -- `===`
  | cne   -- `!==`
  | land  -- `&&`
  | lor   -- `||`
deriving Repr, BEq, DecidableEq, Inhabited

/-- Envelope spelling of a `SymBinOp` (error messages / parser table). -/
def SymBinOp.sym : SymBinOp → String
  | .m0 .add => "+" | .m0 .sub => "-" | .m0 .mul => "*"
  | .m0 .div => "u/" | .m0 .sdiv => "s/"
  | .m0 .rem => "u%" | .m0 .srem => "s%"
  | .m0 (.pow signedBase signedExponent) =>
      (if signedBase then "s" else "u") ++ "**" ++ (if signedExponent then "s" else "u")
  | .m0 (.shl signedLeft) => (if signedLeft then "s" else "u") ++ "<<"
  | .m0 (.shr signedLeft) => (if signedLeft then "s" else "u") ++ ">>"
  | .m0 (.ashl signedLeft) => (if signedLeft then "s" else "u") ++ "<<<"
  | .m0 (.ashr signedLeft) => (if signedLeft then "s" else "u") ++ ">>>"
  | .m0 .and => "&" | .m0 .or => "|"
  | .m0 .xor => "^" | .m0 .eq => "==" | .m0 .ne => "!="
  | .m0 .caseEq => "===" | .m0 .caseNe => "!=="
  | .m0 .wildEq => "==?" | .m0 .wildNe => "!=?"
  | .m0 .casez => "casez" | .m0 .casex => "casex"
  | .m0 .land => "&&" | .m0 .lor => "||" | .m0 .lt => "<"
  | .m0 .le => "<=" | .m0 .gt => ">" | .m0 .ge => ">="
  | .m0 .slt => "s<" | .m0 .sle => "s<="
  | .m0 .sgt => "s>" | .m0 .sge => "s>="
  | .mul => "*" | .div => "/" | .mod => "%" | .pow => "**"
  | .shl => "<<" | .shr => ">>" | .ashl => "<<<" | .ashr => ">>>"
  | .slt => "s<" | .sle => "s<=" | .sgt => "s>" | .sge => "s>="
  | .ceq => "===" | .cne => "!==" | .land => "&&" | .lor => "||"

/-- Unary operators: the M0 set plus unary `+` and the generate-step
`++`/`--` (which are legal only in `GenerateFor.step` position). -/
inductive SymUnaryOp where
  | m0 (op : UnaryOp)
  | plus  -- unary `+` (arithmetic x/z collapse at runtime)
  | inc   -- `++` (generate step only)
  | dec   -- `--` (generate step only)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The sv-0.2 system functions (expression position, one argument). -/
inductive SysFn where
  | clog2 | bits | high | size
  /-- `$test$plusargs` reads the simulator's plus-argument environment
  (IEEE 1800-2023 §20.2.2).  The source node is retained, while the current
  value tier keeps this external environment-dependent result loud. -/
  | testPlusargs
deriving Repr, BEq, DecidableEq, Inhabited

def SysFn.sym : SysFn → String
  | .clog2 => "$clog2" | .bits => "$bits" | .high => "$high" | .size => "$size"
  | .testPlusargs => "$test$plusargs"

/-- Trailing part-select form of a packed-array select path
(`PExpr.arrayPart` / `PLhs.arrayPart`): `[a:b]` (`range` — `a`/`b` the msb/
lsb LABELS as written), `[a +: b]` (`up`) and `[a -: b]` (`down` — `a` the
base label, `b` the width), IEEE 1800-2023 §11.5.1. -/
inductive PartMode where
  | range | up | down
deriving Repr, BEq, DecidableEq, Inhabited

/-- Symbolic expressions — the sv-0.2 expression vocabulary. One type for
every expression position (process values, parameter defaults, generate
headers, dimension bounds); the two evaluation modes are `evalInt`
(constant tier, `Int`-valued) and `instExpr` (value tier, → M0 `Expr`). -/
inductive PExpr where
  /-- Sized 4-state literal (already width-resolved by the extractor). -/
  | lit (value : LVec)
  /-- Signal reference. -/
  | ident (name : String)
  /-- Parameter/localparam reference; `pkg` is set only for package-scoped
  parameters (whose values the envelope does not carry — loud at use). -/
  | paramRef (name : String) (pkg : Option String)
  /-- Enclosing generate-for loop variable reference. -/
  | genvarRef (name : String)
  /-- Enum member used as a value (`type` is the `PEnumType` name). -/
  | enumRef (type member : String) (pkg : Option String)
  /-- Unsized integer literal (32-bit signed int; materializes at context
  width). -/
  | int (value : Int)
  /-- Unbased-unsized literal `'0`/`'1`/`'x`/`'z` — width is context-
  determined, potentially parameter-dependent. -/
  | fill (bit : Logic)
  | unary (op : SymUnaryOp) (arg : PExpr)
  | binary (op : SymBinOp) (left right : PExpr)
  | ternary (cond thenE elseE : PExpr)
  /-- Source order, `parts[0]` most significant (M0 convention). -/
  | concat (parts : List PExpr)
  /-- Width-changing implicit conversion of an **unsigned** operand.
  `width` is the default-elaborated target width (envelope limitation —
  see module docstring). -/
  | resize (width : Nat) (arg : PExpr)
  | signedResize (width : Nat) (arg : PExpr)
  /-- 4-state → 2-state squash (self-check-tier node; outside M0). -/
  | squash2 (width : Nat) (arg : PExpr)
  | sysCall (fn : SysFn) (arg : PExpr)
  /-- `$bits(type)` type inspection.  The width is parser-resolved and
  fixed for the admitted type, while the query remains source-shaped. -/
  | typeBits (name : String) (width : Nat)
  /-- Semantic tier (phase 2): bit/element select `base[index]` — over a
  multi-dim packed base this reads one `elemW`-bit chunk (the element
  width comes from the declaration's dims at instantiation). -/
  | bitSel (base index : PExpr)
  /-- Semantic tier: constant-bound part select `base[msb:lsb]`. -/
  | partSel (base msb lsb : PExpr)
  /-- Semantic tier: replication `{count{arg}}` (count constant). -/
  | repl (count arg : PExpr)
  /-- Semantic tier: reduction `| & ^ ~| ~& ~^`. -/
  | reduce (op : RedOp) (arg : PExpr)
  /-- Semantic tier: `$signed`/`$unsigned` — width-preserving, bit
  identity; signedness acts through the consuming operator (the extractor
  spells signed comparisons `s<` …), so instantiation passes through. -/
  | cast (signed : Bool) (arg : PExpr)
  /-- Semantic tier: a packed-array select PATH over the declared signal
  `name` — `name[i₁]…[iₖ]`, element selects outermost first, each index the
  RAW declared label (an elaboration-time constant). Lowered against the
  declaration's packed dimensions (`IEnv.dims`, evaluated in the
  declaration scope) at instantiation:
  per-dimension label→offset normalization (ascending, descending,
  non-zero-based ranges) and range checks, flat `slice` result
  (`Param2.lean`, `arrayElemWindow`/`arrayPartGeom`). The envelope's `ArraySel` node. -/
  | arrayElem (name : String) (indices : List PExpr)
  /-- `arrayElem`'s path followed by a part select on the NEXT dimension:
  `[a:b]`, `[a +: b]`, `[a -: b]` (`PartMode`). -/
  | arrayPart (name : String) (indices : List PExpr) (mode : PartMode) (a b : PExpr)
  /-- Source-shaped unpacked aggregate member path.  Each step is either a
  field name or a runtime index expression.  The path is retained until the
  aggregate E relation consumes it. -/
  | aggregateMember (base : String) (path : List (Option String × Option PExpr))
  /-- Source-shaped read of one element of a package aggregate parameter. -/
  | packageAggElem (package name : String) (index : PExpr)
  /-- Source-shaped automatic function call. -/
  | functionCall (name : String) (args : List PExpr)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-- One packed dimension `[msb:lsb]` with symbolic bounds. -/
structure PDim where
  msb : PExpr
  lsb : PExpr
deriving Repr, BEq, Inhabited

/-- A declared type: symbolic packed dimensions, an (enum) type
reference, or an unrecoverable dimension list. `resolved?` fields are
defaults-elaborated **metadata** (cross-checks only, never the
contract). -/
inductive PType where
  /-- `[]` = scalar; multi-dim outermost first; total width = product. -/
  | packed (dims : List PDim) (resolved? : Option Nat)
  | typeRef (name : String) (pkg : Option String) (resolved? : Option Nat)
  | unrecoverable (resolved? : Option Nat)
deriving Repr, BEq, Inhabited

/-! Source-shaped aggregate declaration metadata. -/
inductive PAggType where
  | scalar (type : PType) (isSigned : Bool := false) (twoState : Bool := false)
  | struct (fields : List (String × PAggType))
  | array (msb lsb : PExpr) (elem : PAggType)
deriving Repr, BEq, Inhabited

/-- A `parameter` declaration (the design family's binder). `resolved?`
is the defaults-elaborated value — metadata. `type?` is the declared
parameter type when the source gives one (`parameter bit FALL_THROUGH`,
`parameter int unsigned DEPTH`): its width is the parameter's
self-determined width in value positions (untyped parameters are 32-bit
ints, §6.20.2). -/
structure PParam where
  name : String
  default? : Option PExpr := none
  resolved? : Option Int := none
  type? : Option PType := none
  /-- Signedness of the declared type (envelope `signed`); `none` = the
  envelope default: signed exactly when the declared width is 32 (`int`,
  `integer`), unsigned otherwise (`logic [..]`, `bit`) — the extractor
  emits the field for types that depart from it (`int unsigned`,
  `logic [31:0]`, `byte`, …) and, since round 5, for every type whose
  width depends on a parameter (`declConstType` refuses one without it).
  Meaningless without `type?`. -/
  signed? : Option Bool := none
  /-- An UNTYPED parameter whose type at the DEFAULT point (where slang
  elaborated the envelope: its default's type, §6.20.2) is not the type an
  integer override gives it (`int`). At an overridden point the envelope's
  value-tier tree — operator signedness, conversions — was typed for the
  default's type, so value-position reads of it are loud there (`IEnv.stale`,
  `bindParams`). Set at load by `PDesign.markOverrideRetypes`. -/
  overrideRetypes : Bool := false
  /-- Source-shaped aggregate type for a package parameter. -/
  aggregate? : Option PAggType := none
  /-- Keyed packed-struct elements of a fixed unpacked package parameter. -/
  aggregateDefault? : Option (List (List (String × PExpr))) := none
  /-- A parser-retained `string` parameter.  Its value is source metadata and
  does not enter the integer elaboration environment. -/
  isString : Bool := false
  /-- A package member outside the extractor's constant tier.  It remains in
      the package table while references to it fail through the usual loud
      unknown-package-constant path. -/
  unsupported? : Option String := none
  /-- The parser's own value of a package constant, bit for bit (MSB first,
  over 0 1 x z; its length is the parser's width).  Metadata, like
  `resolved?`: the loader's differential compares it. -/
  resolvedBits? : Option String := none
  /-- The parser's signedness of a package constant. -/
  resolvedSigned? : Option Bool := none
deriving Repr, BEq, Inhabited

structure PackageAggValue where
  msb : Int
  lsb : Int
  elements : List LVec
  /-- Signedness of a scalar array element.  Struct and nested aggregate
  elements are unsigned packed values at this tier. -/
  signed : Bool := false
deriving Repr, BEq, Inhabited

/-- A `localparam` (evaluated from the bound parameters at
instantiation, in declaration order). `type?`/`signed?` as on `PParam`. -/
structure PLocalParam where
  name : String
  expr : PExpr
  resolved? : Option Int := none
  type? : Option PType := none
  signed? : Option Bool := none
deriving Repr, BEq, Inhabited

/-- An enum member value: an integer, or an x/z bits string (metadata
fidelity — x/z members cannot be used as constants). -/
inductive EnumVal where
  | int (v : Int)
  | bits (s : String)
deriving Repr, BEq, DecidableEq, Inhabited

structure PEnumMember where
  name : String
  value : EnumVal
deriving Repr, BEq, Inhabited

/-- A named enum type: base width (a `PType`, usually packed) and the
ordered member list (data, never folded away). -/
structure PEnumType where
  name : String
  pkg : Option String := none
  base : PType
  members : List PEnumMember
deriving Repr, BEq, Inhabited

/- The symbolic frontend may flatten a fixed unpacked cell into a scalar
declaration for a legacy store.  Keep the source cell identity as metadata so
the memory route never has to recover it by parsing the display name. -/
/-- A port / variable / net declaration with a symbolic type. Ports come
first (port-list order), then module-body declarations — the M0 decl
order. -/
structure PDecl where
  name : String
  type : PType
  /-- Source-shaped unpacked dimensions.  The current flat E store does not
  yet allocate array-valued state, so nonempty dimensions remain a loud
  memory boundary at instantiation rather than being flattened at the
  default parameter point. -/
  unpackedDims : List PDim := []
  /-- Declared signedness, retained for symbolic scalar/vector declarations. -/
  isSigned : Bool := false
  twoState : Bool := false
  isInput : Bool := false
  isOutput : Bool := false
  /-- Parser-native bidirectional net port (`inout`, IEEE 1800-2023 §23.2.2).
  The ordinary scalar store does not resolve multiple net drivers yet, so
  this flag is retained source-shaped and remains loud at that boundary. -/
  isInout : Bool := false
  isNet : Bool := false
  init : Option PExpr := none
  /-- Base array name when this declaration is one flattened cell. -/
  flatBase : Option String := none
  /-- Constant unpacked index of a flattened one-rank cell. -/
  flatIndex : Option Int := none
  /-- Parser-native aggregate shape.  Aggregate declarations remain loud in
  the scalar E store, but their fields and fixed ranges are retained here so
  the source-shaped relation can admit them without flattening. -/
  aggregate? : Option PAggType := none
deriving Repr, BEq, Inhabited

/-- A literal-file `$readmemh` task retained as module metadata.  The
statement surface stays frozen; the memory adapter consumes this typed record
instead of reparsing an Unsupported message. -/
structure PReadmemh where
  file : String
  target : String
  words : List String
deriving Repr, BEq, Inhabited

structure PCellRef where
  name : String
  base : String
  index : Int
deriving Repr, BEq, Inhabited

/-- Assignment targets of the semantic tier: whole signal, bit/element
select, constant part select, or a concatenation of those direct leaves.
Concatenation targets are used by continuous assignments; their leaves stay
over declared signal names so the comb driver can update each existing
vector window without introducing aggregate storage. -/
inductive PLhs where
  | ident (name : String)
  | bitSel (name : String) (index : PExpr)
  | partSel (name : String) (msb lsb : PExpr)
  | concat (parts : List PLhs)
  /-- A packed-array select path target (`PExpr.arrayElem`'s shape —
  `pp[i][j] = …`): lowered to ONE flat window of the declared vector. -/
  | arrayElem (name : String) (indices : List PExpr)
  /-- A packed bit select of one unpacked array element, retained as one
      parser-shaped memory target (`mem[0][i]`, IEEE 1800-2023 §§7.4.6, 11.5.1). -/
  | arrayBitSel (name : String) (indices : List PExpr) (bit : PExpr)
  /-- … with a trailing part select (`PExpr.arrayPart`'s shape). -/
  | arrayPart (name : String) (indices : List PExpr) (mode : PartMode) (a b : PExpr)
  /-- Source-shaped aggregate member path target. -/
  | aggregateMember (base : String) (path : List (Option String × Option PExpr))
deriving Repr, BEq, Inhabited

/-- The targeted signal's name. -/
def PLhs.name : PLhs → String
  | .ident n | .bitSel n _ | .partSel n _ _ | .arrayElem n _ | .arrayBitSel n _ _ | .arrayPart n ..
  | .aggregateMember n _ => n
  | .concat (part :: _) => part.name
  | .concat [] => ""

/-- A statement of a function body, as the source writes it (IEEE 1800-2023
§13.4, §12).  It is a separate type from `PStmt` because a function body has
`return` and typed local declarations, which the process statements do not
have; the constant evaluator (`execFnStmt`) gives each node its meaning. -/
inductive PFnStmt where
  /-- A local variable declaration with its declared type. -/
  | decl (name : String) (type : PType) (isSigned : Bool) (twoState : Bool) (init : Option PExpr)
  /-- A blocking assignment. -/
  | assign (target : PLhs) (value : PExpr)
  /-- `x++` / `x--` as a statement (§11.4.2). -/
  | incDec (target : String) (inc : Bool)
  | ifStmt (cond : PExpr) (thenS : PFnStmt) (elseS : Option PFnStmt)
  /-- A plain `case` (§12.5): items in source order, each with its expressions. -/
  | caseStmt (subject : PExpr) (items : List (List PExpr × PFnStmt)) (default? : Option PFnStmt)
  /-- `for (init; cond; step) body` (§12.7.1). -/
  | forLoop (init : List PFnStmt) (cond : PExpr) (step : List PFnStmt) (body : PFnStmt)
  | block (body : List PFnStmt)
  /-- `return e;` or `return;` (§13.4.1). -/
  | ret (value : Option PExpr)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-! A source-shaped function declaration.  `body` is the one return
expression of the E function rung (automatic input-only functions; a body the
extractor cannot give as one expression is an `unsupported` node there).
`stmts` is the body as written; the constant evaluator executes it. -/
structure PFunction where
  name : String
  formals : List PDecl
  returnType : PType
  body : PExpr
  /-- Signedness of the function's integral return type. -/
  isSigned : Bool := false
  automatic : Bool := true
  /-- The body as written (absent in an envelope older than this field: the
  body is then `return body;`). -/
  stmts : Option (List PFnStmt) := none
  /-- The return type is 2-state (the result variable starts at 0, §6.8). -/
  returnTwoState : Bool := false
  /-- Declared in a package: its types have one point, so the widths the
  frontend recorded in its body are exact (`evalVec`'s `exact`). -/
  fromPackage : Bool := false
deriving Repr, BEq, Inhabited

/-- Statements: the M0 shapes over `PExpr` (identifier targets), plus the
semantic tier's select-target assignments (`…L`) and `case` (plain /
`unique` / `inside` — §12.5.4). `caseStmt.items` are `(patterns, body)`
pairs in source order; a comma list is ONE item with several patterns. -/
inductive PStmt where
  | blockingAssign (target : String) (value : PExpr)
  | nbaAssign (target : String) (value : PExpr)
  | ifStmt (cond : PExpr) (thenBranch : PStmt) (elseBranch : Option PStmt)
  | block (body : List PStmt)
  /-- A fixed-width static procedural declaration. -/
  | localDecl (name : String) (width : Nat) (init : Option PExpr)
  /-- A procedural declaration with automatic lifetime.  Its storage is
      allocated per activation by the source-shaped executor. -/
  | automaticDecl (name : String) (width : Nat) (init : Option PExpr)
  /-- A symbolic procedural `for` retained until parameter-point
  instantiation.  The iterator is represented as a temporary genvar-style
  constant while the body is lowered at each concrete point. -/
  | forLoop (iterator : String) (init condition step : PExpr) (body : PStmt)
  | blockingAssignL (target : PLhs) (value : PExpr)
  | nbaAssignL (target : PLhs) (value : PExpr)
  | caseStmt (subject : PExpr) (items : List (List PExpr × PStmt))
      (default? : Option PStmt) (mode : CaseMode) (check : CaseCheck)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/- Edge polarity retained on a plain event-controlled `always` list. -/
inductive PEventEdge where
  | any
  | posedge
  | negedge
deriving Repr, BEq, Inhabited

/-! A parser-shaped scalar event-list member. Expression events, guards, and
aggregate selectors stay outside this first E admission slice. -/
structure PEvent where
  signal : String
  edge : PEventEdge := .any
deriving Repr, BEq, Inhabited

/-- Processes: M0 shapes plus select-target continuous assigns and the
async active-low reset event list (`@(posedge clock or negedge rstn)`). -/
inductive PProcess where
  | alwaysFF (clock : String) (body : PStmt)
  /-- Negative-edge `always_ff`; retained for canonical E (§9.4.2). -/
  | alwaysFFNegedge (clock : String) (body : PStmt)
  | alwaysPlain (clock : String) (body : PStmt)
  | alwaysComb (body : PStmt)
  /-- Source-shaped `always_latch`; its implicit level sensitivity and
      time-zero activation are retained for canonical E (§9.2.2.3). -/
  | alwaysLatch (body : PStmt)
  /-- Plain `always @*`: the parser's implicit event control and original
  body, retained for E. It first waits, unlike `always_comb` (§9.4.2.2).
  The frozen cycle views have no corresponding process and stay loud. -/
  | alwaysImplicit (body : PStmt)
  /-- A plain `always` with a retained scalar event list (§9.4.2). -/
  | alwaysEvent (events : List PEvent) (body : PStmt)
  | assign (target : String) (value : PExpr)
  | assignL (target : PLhs) (value : PExpr)
  | alwaysFFR (clock rstn : String) (body : PStmt) (resetHigh : Bool)
  /-- A source-shaped `initial` process.  It runs once at time zero in
  memory-cycle semantics; other semantic routes keep it loud until their
  scheduler has an explicit time-zero phase. -/
  | initial (body : PStmt)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-- One segment of a module instance's lexical generate path (F3): the
generate block's name (`genblk<n>` for an unnamed block, IEEE 1800-2023
§27.6) and, for a generate-for block, its genvar — whose value at expansion
time is the block's index (`g_bit[3]`). -/
structure PPathSeg where
  label : String
  genvar : Option String := none
deriving Repr, BEq, Inhabited

/-- One port connection of a module instance, in the CHILD's port order
(the extractor resolves named, ordered, `.name` and `.*` connections).
`input`: the actual is a value expression of the instantiating scope
(`none` = unconnected; `net` = the port is a net, so an unconnected one
reads z — a variable port reads its initial x; on a CONNECTED input `net`
marks the one shape Xcelium binds bit for bit — a net formal fed by a bare
net actual — so a narrower actual there is `PortConn:net-width`,
`Hier2.lean`). `output`: the actual is an assignment target of the
instantiating scope (`none` = unconnected).
`unsupported`: a loud connection (inout, interface port, port default, …). -/
inductive PConn where
  | input (port : String) (actual : Option PExpr) (net : Bool)
  | output (port : String) (actual : Option PLhs)
  /-- Bidirectional net connection, retained as a source-shaped relation.
  Resolution is handled only by a future net-driver route, so the current
  scalar hierarchy route refuses it explicitly. -/
  | inout (port : String) (actual : Option PExpr)
  | unsupported (port : String) (svKind text : String)
deriving Repr, BEq, Inhabited

/-- The connected port's name (`""` for a loud connection without one). -/
def PConn.port : PConn → String
  | .input p _ _ | .output p _ | .inout p _ | .unsupported p _ _ => p

/-- A module instance (F3): instance name, definition name (looked up in
the envelope's module library at instantiation), lexical generate path,
the OVERRIDDEN parameters as `(child parameter, symbolic constant
expression of the instantiating scope)`, and the port connections. The
hierarchical instantiation (`Hier2.lean`, `PDesign.instantiateH`) flattens
it; the flat instantiations (`instantiate`, `instantiate2`) keep it as a
loud unsupported process. -/
structure PInst where
  name : String
  module : String
  path : List PPathSeg := []
  params : List (String × PExpr) := []
  conns : List PConn := []
deriving Repr, BEq, Inhabited

/-- Source-shaped built-in gate primitive instance (IEEE 1800-2023 §28).
The first port is the primitive output target, followed by input expressions.
The node remains distinct from continuous assignment semantics. -/
structure PPrimitive where
  name : String
  op : String
  target : PLhs
  inputs : List PExpr
deriving Repr, BEq, Inhabited

/-- Generate items. `genFor` is ONE structural node — genvar, symbolic
`init`/`bound`/`step`, body **template** (never unrolled in the data);
`genIf` keeps its symbolic condition (`elseB = []` when there is no else
branch; else-if chains are an `elseB` containing one `genIf`).
`resolvedCount?` is defaults-elaborated metadata. `inst` is a module
instance (F3) — at module level or inside a generate body. -/
inductive GenItem where
  | process (p : PProcess)
  /-- A declaration retained in its generate scope.  Its source-shaped type
  and unpacked dimensions are elaborated at the active generate instance;
  the canonical memory route collects it alongside the enclosing module
  declarations (IEEE 1800-2023 §27. generate blocks). -/
  | decl (d : PDecl)
  /-- A generate-local `localparam` retained in its lexical generate scope.
  It is evaluated at the active concrete generate instance and remains a
  constant binding for the source-shaped items that follow it (IEEE
  1800-2023 §27.4). -/
  | localParam (p : PLocalParam)
  | genFor (label : Option String) (genvar : String) (init bound step : PExpr)
      (resolvedCount? : Option Nat) (body : List GenItem)
  | genIf (cond : PExpr) (thenB elseB : List GenItem)
  | unsupported (svKind : String) (text : String)
  | inst (i : PInst)
deriving Repr, BEq, Inhabited

/-! Value expressions keep `$past` inside an equality instead of erasing it
from the ordinary `PExpr` tree.  This is the finite safety fragment's
source-shaped temporal value route; unsupported value operators remain loud
at ingestion. -/
inductive PSvaValue where
  | current (value : PExpr)
  | past (cycles : Nat) (value : PExpr)
  | countOnes (value : PExpr)
  /-- A parameter-sized integral cast retained inside a sampled value.  The
      width is evaluated at the concrete parameter point by the SVA contract;
      keeping the parameter name here avoids folding it at the extractor's
      default point. -/
  | paramCast (parameter : String) (value : PSvaValue)
  | binary (op : BinOp) (left right : PSvaValue)
deriving Repr, BEq, Inhabited

/-! Structured SVA syntax retained from Slang.  Ordinary boolean leaves are
`PExpr`; the property layer adds only sampling, delays, implications and
`disable iff`.  Source text remains provenance, never a second parser input. -/
inductive PSvaBool where
  | expr (value : PExpr)
  | valueEq (left right : PSvaValue)
  | not (arg : PSvaBool)
  | and (left right : PSvaBool)
  | or (left right : PSvaBool)
  | isUnknown (value : PExpr)
  | oneHot0 (value : PExpr)
  | valueCmp (op : BinOp) (left right : PSvaValue)
  | past (cycles : Nat) (value : PExpr)
  | rose (value : PExpr)
  | fell (value : PExpr)
  | stable (value : PExpr)
deriving Repr, BEq, Inhabited

inductive PSvaSeq where
  | atom (test : PSvaBool)
  | delay (cycles : Nat) (body : PSvaSeq)
  | range (lo hi : Nat) (body : PSvaSeq)
  | concat (left right : PSvaSeq)
deriving Repr, BEq, Inhabited

inductive PSvaProp where
  | always (body : PSvaSeq)
  | implies (antecedent consequent : PSvaSeq)
  | nonoverlap (antecedent consequent : PSvaSeq)
  | disable (guard : PSvaBool) (body : PSvaProp)
deriving Repr, BEq, Inhabited

inductive PSvaKind where
  | assert | assume | cover
deriving Repr, BEq, Inhabited

inductive PSvaEdge where
  | posedge | negedge | any
deriving Repr, BEq, Inhabited

structure PSvaCheck where
  kind : PSvaKind
  edge : PSvaEdge
  clock : String
  property : PSvaProp
deriving Repr, BEq, Inhabited

structure PProperty where
  name : String
  kind : String
  clock : Option String := none
  text : String := ""
  ast : Option PSvaCheck := none
  /-- Lexical generate labels enclosing this property.  Generated instance
  indices are left to the hierarchy contract; they are not flattened here. -/
  path : List String := []
deriving Repr, BEq, Inhabited

/-- Parser-native metadata retained for a refused net declaration.  This is
not a resolution rule: it records the evidence needed to decide one later
without recovering fields from an error string (IEEE 1800-2023 §6.6/§28.12). -/
structure PNetDriver where
  bounds : Int × Int
  ownerKind : String
  ownerName : String
  generated : Bool
  source : String
deriving Repr, BEq, Inhabited

structure PNetMetadata where
  name : String
  width : Nat
  netKind : String
  signed : Bool
  fourState : Bool
  isNet : Bool
  /-- True when this marker came from a declaration scoped by a generate
  block (IEEE 1800-2023 §27.4), rather than a module member. -/
  generated : Bool := false
  driverReason : Option String := none
  driverRecords : List PNetDriver := []
deriving Repr, BEq, Inhabited

/-- A parametric design — the sv-0.2 module payload. `params` order is
the **binder order** of the design family. `others` are out-of-tier
module members (kept as loud unsupported processes at instantiation). -/
structure PDesign where
  name : String
  params : List PParam
  localParams : List PLocalParam
  /-- Scalar package parameters visible to this module.  The package name is
  retained beside the parameter so qualified `ParamRef`s remain source-shaped. -/
  packageParams : List (String × PParam) := []
  enums : List PEnumType
  decls : List PDecl
  functions : List PFunction := []
  primitives : List PPrimitive := []
  processes : List PProcess
  generates : List GenItem
  others : List (String × String) := []
  netMetadata : List PNetMetadata := []
  /-- Concurrent assertions retained from the source envelope. -/
  properties : List PProperty := []
  /-- Structured literal-file memory tasks (the process marker remains in
  `processes` for the ordinary route's loud refusal). -/
  readmemh : List PReadmemh := []
  cellRefs : List PCellRef := []
deriving Repr, BEq, Inhabited

/-! ## The instantiation environment -/

/-- Instantiation environment: bound integer constants (parameters,
localparams, in-scope genvars — first match wins, so genvar bindings
shadow), instantiated declaration widths, and the enum tables. -/
structure IEnv where
  vals : List (String × Int) := []
  /-- Packed values of parser-retained string parameters.  Strings are
  source metadata for the integer constant tier, but hierarchy forwarding
  still needs their exact bits (IEEE 1800-2023 §6.20.2). -/
  stringVals : List (String × LVec) := []
  /-- INT-class package constants, keyed by `(package, name)`. -/
  packageVals : List ((String × String) × Int) := []
  /-- Fixed-width non-INT package constants, keyed by `(package, name)`,
  with their canonical value, width, and signedness.  Parameter-dependent
  package widths are not retained by the symbolic extractor. -/
  packageNvals : List ((String × String) × (Int × Nat × Bool)) := []
  /-- Four-state package constants, keyed by `(package, name)`.  The vector
  retains the declared width, signedness, and every x/z bit for ordinary
  value positions. -/
  packageFvals : List ((String × String) × (LVec × Nat × Bool)) := []
  packageAggs : List ((String × String) × PackageAggValue) := []
  widths : List (String × Nat) := []
  enums : List (String × Nat) := []
  members : List ((String × String) × LVec) := []
  functions : List PFunction := []
  /-- Declared widths of TYPED parameters/localparams (semantic tier;
  untyped parameters are 32-bit ints and are absent here). -/
  pwidths : List (String × Nat) := []
  /-- The packed dimensions of every declaration with an explicit
  dimension list (`PType.packed`), outermost first, as `(msb, lsb)` LABELS
  evaluated ONCE in the declaration's own scope (the module parameters and
  localparams — `Param2.lean`'s `dimTable`, run by `instantiate2` before
  generate expansion): the geometry of packed-array select paths
  (`PExpr.arrayElem`/`arrayPart`, semantic tier). Evaluated rather than
  symbolic so that no genvar bound later by `bindVal` (which may legally
  reuse a parameter's name) can reach a declared range. -/
  dims : List (String × List (Int × Int)) := []
  /-- Parameters/localparams whose type is NOT the INT class (32-bit
  signed): `(name, value, width, signed)`, the value canonical for the
  type (`canonInt`). `vals` is consulted first, so a genvar reusing such a
  name shadows it. Membership in `vals` is what makes a `ParamRef` INT
  (`PExpr.isInt`) — a proof holding `env.vals.lookup n = some v` needs no
  separate typing fact. -/
  nvals : List (String × (Int × Nat × Bool)) := []
  /-- Constants whose type HERE differs from the type the envelope's tree
  was elaborated at (`PParam.overrideRetypes` parameters at an override,
  and untyped localparams defined from them): bound in `nvals` (their
  constant-tier value and type are exact), but a value-position read of one
  is loud (`instExpr2`) — the tree's operator signedness around it is the
  default point's. -/
  stale : List String := []
  /-- **Exact 32-bit `int` mode** (`PDesign.int32Agrees`): INT-class
  parameters and typed-`int` localparams bind in `nvals` at `(32, signed)`
  instead of `vals`, so every constant expression over them is evaluated
  width-exactly (`evalSized`: two's-complement wrap at 32 bits, as in every
  simulator) rather than on the unbounded fast path. Off in `instantiate2`
  (the proof-facing family); the differential runner and the load gate
  compare the two instantiations. -/
  int32 : Bool := false
  /-- The packed range of every TYPED parameter/localparam whose declared
  bounds are not all literals (`localparam logic [N-1:0] P`), evaluated at
  THIS point (`bindParams`/`bindLocal`, round 3 folds). The extractor keeps
  a select of such a parameter's value (`P[1]`, `P[0 +: 2]`) in the legacy
  encoding — its labels read as offsets from bit 0 — only where the range is
  canonical `[m:0]` at the default point (`_sym_param_root_select`); the
  constant tier (`evalAt`, `paramSelectOk`) refuses the select at a point
  where the range is anything else (`[-1:0]` at `N = 0`). Parameters with
  literal bounds (offsets folded by the extractor, exact everywhere) and
  INT-class ones (`[31:0]`) are absent. -/
  pdims : List (String × List (Int × Int)) := []
  /-- How many LEADING entries of `vals` were bound by generate scopes
  (generate-local parameters and genvars of the canonical E route,
  `coreMemScopeEnv`).  A module function is declared in the module scope
  (IEEE 1800-2023 §13.4.3, §23.9): its body is evaluated in `IEnv.declEnv`,
  the environment without those entries. -/
  scopedVals : Nat := 0
  /-- The same count for `nvals`. -/
  scopedNVals : Nat := 0
deriving Repr, Inhabited

/-- The environment of the module scope: `env` without the generate-scope
bindings its counts record. -/
def IEnv.declEnv (env : IEnv) : IEnv :=
  { env with vals := env.vals.drop env.scopedVals, nvals := env.nvals.drop env.scopedNVals,
             scopedVals := 0, scopedNVals := 0 }

/-- Bind a constant (prepend — shadows outer bindings of the name). -/
def IEnv.bindVal (env : IEnv) (n : String) (v : Int) : IEnv :=
  { env with vals := (n, v) :: env.vals }

def IEnv.bindStringVal (env : IEnv) (n : String) (v : LVec) : IEnv :=
  { env with stringVals := (n, v) :: env.stringVals }

def IEnv.stringVal? (env : IEnv) (n : String) : Option LVec :=
  env.stringVals.lookup n

def IEnv.bindPackageVal (env : IEnv) (pkg n : String) (v : Int) : IEnv :=
  { env with packageVals := ((pkg, n), v) :: env.packageVals }

def IEnv.packageVal (env : IEnv) (pkg n : String) : Option Int :=
  env.packageVals.lookup (pkg, n)

def IEnv.bindPackageNVal (env : IEnv) (pkg n : String) (v : Int) (w : Nat) (s : Bool) : IEnv :=
  { env with packageNvals := ((pkg, n), (v, w, s)) :: env.packageNvals }

def IEnv.packageNVal (env : IEnv) (pkg n : String) : Option (Int × Nat × Bool) :=
  env.packageNvals.lookup (pkg, n)

def IEnv.bindPackageFVal (env : IEnv) (pkg n : String) (v : LVec) (w : Nat) (s : Bool) : IEnv :=
  { env with packageFvals := ((pkg, n), (v, w, s)) :: env.packageFvals }

def IEnv.packageFVal (env : IEnv) (pkg n : String) : Option (LVec × Nat × Bool) :=
  env.packageFvals.lookup (pkg, n)

def IEnv.bindPackageAgg (env : IEnv) (pkg n : String) (v : PackageAggValue) : IEnv :=
  { env with packageAggs := ((pkg, n), v) :: env.packageAggs }

def IEnv.packageAgg? (env : IEnv) (pkg n : String) : Option PackageAggValue :=
  env.packageAggs.lookup (pkg, n)

private def packageAggLabels (msb lsb : Int) : List Int :=
  if msb ≤ lsb then
    (List.range ((lsb - msb + 1).toNat)).map (fun n => msb + Int.ofNat n)
  else
    (List.range ((msb - lsb + 1).toNat)).map (fun n => msb - Int.ofNat n)

/-- A module parameter whose default is a parser-retained package aggregate.
The integer parameter binder cannot carry this value.  Keep the source-shaped
parameter unbound so hierarchy forwarding can preserve it, and let any direct
constant or value use refuse at its own expression node until the aggregate
value store is threaded through the module environment (IEEE 1800-2023
§6.20.2). -/
@[simp] def PParam.hasAggregateDefault (env : IEnv) (p : PParam) : Bool :=
  match p.default? with
  | some (.paramRef n (some pkg)) => (env.packageAgg? pkg n).isSome
  | _ => false

/-- Self-determined type of a retained package parameter. -/
def IEnv.packageConstType (env : IEnv) (pkg n : String) : Option (Nat × Bool) :=
  match env.packageFVal pkg n with
  | some (_, w, s) => some (w, s)
  | none =>
      match env.packageVal pkg n with
      | some _ => some (32, true)
      | none =>
          (env.packageNVal pkg n).map fun (_, w, s) => (w, s)

/-- Canonical key for an enum type in the retained environment.  Package
enums stay qualified, while a frontend that already puts `pkg::` in the
type name is accepted without doubling the qualifier. -/
def enumKey (name : String) (pkg : Option String) : String :=
  match pkg with
  | none => name
  | some p =>
      let q := p ++ "::"
      if name.startsWith q then name else q ++ name

def IEnv.enumWidth (env : IEnv) (name : String) (pkg : Option String) : Option Nat :=
  env.enums.lookup (enumKey name pkg)

def IEnv.enumMember (env : IEnv) (name member : String) (pkg : Option String) : Option LVec :=
  env.members.lookup (enumKey name pkg, member)

/-- Bind a non-INT typed constant (`IEnv.nvals`). -/
def IEnv.bindNVal (env : IEnv) (n : String) (v : Int) (w : Nat) (s : Bool) : IEnv :=
  { env with nvals := (n, (v, w, s)) :: env.nvals }

/-- Integer-class lookup for proof-facing views: a loop binding in `vals`
shadows the exact signed-32 parameter/localparam slice in `nvals`. -/
def IEnv.intVal? (env : IEnv) (n : String) : Option Int :=
  match env.vals.lookup n with
  | some v => some v
  | none =>
      if n ∈ env.stale then none
      else
        match env.nvals.lookup n with
        | some (v, 32, true) => some v
        | _ => none

@[simp] theorem IEnv.intVal?_bindVal_self (env : IEnv) (n : String) (v : Int) :
    IEnv.intVal? (env.bindVal n v) n = some v := by
  simp [IEnv.intVal?, IEnv.bindVal]

theorem IEnv.intVal?_bindVal_ne {env : IEnv} {g n : String} (v : Int) (h : n ≠ g) :
    IEnv.intVal? (env.bindVal g v) n = IEnv.intVal? env n := by
  have hlookup : List.lookup n ((g, v) :: env.vals) = List.lookup n env.vals := by
    simp [List.lookup, beq_false_of_ne h]
  unfold IEnv.intVal?
  change (match List.lookup n ((g, v) :: env.vals) with
    | some x => some x
    | none => if n ∈ env.stale then none else
      match List.lookup n env.nvals with
      | some (x, 32, true) => some x
      | _ => none) = _
  rw [hlookup]

theorem IEnv.intVal?_cases {env : IEnv} {n : String} {v : Int}
    (h : IEnv.intVal? env n = some v) :
    env.vals.lookup n = some v ∨
      ∃ w s, env.nvals.lookup n = some (v, w, s) ∧ w = 32 ∧ s = true := by
  unfold IEnv.intVal? at h
  cases hv : env.vals.lookup n with
  | some x =>
      left
      have hx : x = v := by simpa [hv] using h
      rw [← hx]
  | none =>
      right
      cases hn : env.nvals.lookup n with
      | none => simp [hv, hn] at h
      | some q =>
          obtain ⟨x, w, s⟩ := q
          by_cases hw : w = 32
          · subst w
            by_cases hs : s = true
            · subst s
              have hstale : n ∉ env.stale := by
                by_cases hbad : n ∈ env.stale
                · simp [hv, hbad] at h
                · exact hbad
              have hx : x = v := by simpa [hv, hn, hstale] using h
              subst x
              refine ⟨32, true, ?_, rfl, rfl⟩
              rfl
            · simp [hv, hn, hs] at h
          · simp [hv, hn, hw] at h

#guard IEnv.intVal? ({ nvals := [("N", (16, 32, true))] } : IEnv) "N" == some 16
#guard IEnv.intVal? (({ nvals := [("N", (16, 32, true))] } : IEnv).bindVal "i" 3) "N" == some 16
#guard IEnv.intVal? (({ nvals := [("N", (16, 32, true))] } : IEnv).bindVal "N" 3) "N" == some 3

/-! ## Constant tier: `evalInt` -/

private def b2i (b : Bool) : Int := if b then 1 else 0

/-! A known constant replication, computed from the operand's own width. -/
def repeatConst : Nat → Nat → Int → Int
  | 0, _, _ => 0
  | n + 1, w, v =>
      v.emod ((2 : Int) ^ w) * ((2 : Int) ^ (n * w)) + repeatConst n w v

/-- `v` at the constant type `(w, s)`: two's complement modulo `2^w`, read
signed when `s` (IEEE 1800-2023 §11.8.2: every operation is carried out at
the propagated width; `canonInt w s` is the value that width holds). -/
def canonInt (w : Nat) (s : Bool) (v : Int) : Int :=
  let m := v.emod ((2 : Int) ^ w)
  if s && decide (0 < w) && decide ((2 : Int) ^ (w - 1) ≤ m) then m - (2 : Int) ^ w else m

/-- The integer view used only at constant-required sites.  A known
four-state package value has the same canonical integer view as the legacy
package table, while an x/z bit remains unavailable to that view. -/
def IEnv.packageIntView? (env : IEnv) (pkg n : String) : Option Int :=
  match env.packageFVal pkg n with
  | some (v, w, s) => v.toNat?.map (fun k => canonInt w s k)
  | none => env.packageVal pkg n

theorem IEnv.packageIntView_bindPackageFVal (env : IEnv) (pkg n : String)
    (v : LVec) (w : Nat) (s : Bool) :
    (env.bindPackageFVal pkg n v w s).packageIntView? pkg n =
      v.toNat?.map (fun k => canonInt w s k) := by
  simp [IEnv.packageIntView?, IEnv.bindPackageFVal, IEnv.packageFVal]

/-- Conservativity for known package values: the four-state table's integer
view agrees with the legacy integer binding at the same width and signedness. -/
theorem IEnv.packageIntView_known (env : IEnv) (pkg n : String)
    (v : LVec) (w : Nat) (s : Bool) (k : Nat)
    (hknown : v.toNat? = some k) :
    (env.bindPackageFVal pkg n v w s).packageIntView? pkg n =
      some (canonInt w s k) := by
  simp [IEnv.packageIntView?, IEnv.bindPackageFVal, IEnv.packageFVal, hknown]

/-- A value of type `(lw, ls)` at the propagated type `(w, s)` (§11.8.2:
the operand's bits extended — sign-extended ONLY when the propagated type
is signed — or truncated, then read at the new type). -/
def convertConst (lw : Nat) (w : Nat) (s : Bool) (v : Int) : Int :=
  let bits := v.emod ((2 : Int) ^ lw)
  canonInt w s (if s then canonInt lw true bits else bits)

/-- How a binary operator treats its operands in a constant expression
(IEEE 1800-2023 §11.6.1 Table 11-21). -/
inductive ConstOpClass where
  /-- `+ - * / % & | ^`: context-determined operands (the max width, signed
  iff both are). -/
  | arith
  /-- `<< >> <<< >>> **`: the left operand context-determined, the right
  self-determined. -/
  | shift
  /-- Equality/relational: operands sized to each other, 1-bit unsigned
  result. -/
  | compare
  /-- `&& ||`: self-determined operands, 1-bit unsigned result. -/
  | logical
  /-- The run-time vector spellings (`u/`, `s%`, `u**s`, `s>>` …): loud in a
  constant context. -/
  | vector
deriving Repr, BEq, DecidableEq, Inhabited

/-- `ConstOpClass` of an envelope operator. -/
def SymBinOp.constClass : SymBinOp → ConstOpClass
  | .m0 .add | .m0 .sub | .m0 .mul | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem
  | .m0 .and | .m0 .or | .m0 .xor
  | .mul | .div | .mod => .arith
  | .pow | .shl | .shr | .ashl | .ashr => .shift
  | .m0 .eq | .m0 .ne | .m0 .caseEq | .m0 .caseNe | .m0 .wildEq | .m0 .wildNe
  | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
  | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge
  | .slt | .sle | .sgt | .sge | .ceq | .cne => .compare
  | .m0 .land | .m0 .lor | .land | .lor => .logical
  | _ => .vector

/-- The operators that keep the INT class (32-bit signed operands in,
32-bit signed result out). -/
def SymBinOp.intArith : SymBinOp → Bool
  | .m0 .add | .m0 .sub | .m0 .mul | .m0 .and | .m0 .or | .m0 .xor
  | .m0 (.shl _) | .m0 (.shr _) | .m0 (.ashl _) | .m0 (.ashr _)
  | .mul | .div | .mod | .pow | .shl | .shr | .ashl | .ashr => true
  | _ => false

/-- **The INT class** of a constant expression: built from unsized integers,
genvars, system-call results and `vals`-bound (32-bit signed) parameters by
the `intArith` operators, unary `-`/`+`, and `?:` (whose condition is
self-determined and may be anything). Its value is the mathematical one
(`evalInt`'s fast path, the ledger's unbounded-`Int` regime); every other
expression is evaluated width-exactly by `evalSized`. A `ParamRef` is INT
exactly when the name is bound in `IEnv.vals` (non-INT typed parameters
live in `IEnv.nvals`). -/
def PExpr.isInt (env : IEnv) : PExpr → Bool
  | .int _ | .genvarRef _ | .sysCall .. | .typeBits .. => true
  | .paramRef n none =>
      (env.vals.lookup n).isSome ||
        match env.nvals.lookup n with
        | some (_, 32, true) => true
        | _ => false
  | .paramRef n (some p) => (env.packageVal p n).isSome
  | .unary (.m0 .neg) a | .unary (.m0 .pos) a | .unary .plus a => a.isInt env
  | .binary op l r => op.intArith && l.isInt env && r.isInt env
  | .ternary _ t e => t.isInt env && e.isInt env
  | .functionCall n _ =>
      match env.functions.find? (fun f => f.name == n) with
      | some f =>
          f.isSigned && match f.returnType with
            | .packed _ (some 32) | .typeRef _ _ (some 32) => true
            | _ => false
      | none => false
  | .aggregateMember .. | .packageAggElem .. | _ => false

-- The INT-class test computes on syntax (and `vals` lookups): a `simp` that
-- unfolds `evalInt` decides it by itself.
attribute [simp] PExpr.isInt SymBinOp.intArith

mutual
/-- Whether a `ParamRef` to one of `names` occurs anywhere in the
expression (`IEnv.stale` propagation and value-tier checks). -/
def PExpr.mentionsAny (names : List String) : PExpr → Bool
  | .paramRef n _ => names.contains n
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a | .sysCall _ a
  | .reduce _ a | .cast _ a => a.mentionsAny names
  | .binary _ l r | .bitSel l r | .repl l r => l.mentionsAny names || r.mentionsAny names
  | .partSel b m l | .ternary b m l =>
      b.mentionsAny names || m.mentionsAny names || l.mentionsAny names
  | .concat ps | .arrayElem _ ps => PExpr.mentionsAnyList names ps
  | .arrayPart _ ps _ a b =>
      PExpr.mentionsAnyList names ps || a.mentionsAny names || b.mentionsAny names
  | .aggregateMember .. | .packageAggElem .. => false
  | .functionCall _ args => PExpr.mentionsAnyList names args
  | .lit _ | .ident _ | .genvarRef _ | .enumRef .. | .int _ | .fill _
  | .typeBits .. | .unsupported .. => false

/-- `PExpr.mentionsAny` over a list. -/
def PExpr.mentionsAnyList (names : List String) : List PExpr → Bool
  | [] => false
  | p :: ps => p.mentionsAny names || PExpr.mentionsAnyList names ps
end


/-! Exact-mode INT classification is separate from the historical proof-path
predicate.  `instantiate2` stores signed 32-bit INT values in `nvals`; this
view exposes that class without changing the unbounded `evalInt` API. -/
def PExpr.isIntExact (env : IEnv) : PExpr → Bool
  | .int _ | .genvarRef _ | .sysCall .. | .typeBits .. => true
  | .paramRef n none =>
      (env.vals.lookup n).isSome ||
        match env.nvals.lookup n with
        | some (_, 32, true) => true
        | _ => false
  | .paramRef n (some p) => (env.packageVal p n).isSome
  | .unary (.m0 .neg) a | .unary (.m0 .pos) a | .unary .plus a => a.isIntExact env
  | .binary op l r => op.intArith && l.isIntExact env && r.isIntExact env
  | .ternary _ t e => t.isIntExact env && e.isIntExact env
  | _ => false

attribute [simp] PExpr.isIntExact

/-! A constant-context replication must reject a signal operand before it
evaluates the repetition count.  In particular, a select has a structural
width, so `ctype` alone would otherwise accept it and get stuck on a symbolic
count.  Keep this test local to `Param.lean`: `Param2` has a similar walker,
but importing it here would create a cycle. -/
mutual
def PExpr.readsSignalConst : PExpr → Bool
  | .ident _ | .arrayElem .. | .arrayPart .. => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => a.readsSignalConst
  | .binary _ l r | .bitSel l r | .repl l r =>
      l.readsSignalConst || r.readsSignalConst
  | .partSel b m l | .ternary b m l =>
      b.readsSignalConst || m.readsSignalConst || l.readsSignalConst
  | .concat ps => PExpr.readsSignalConstList ps
  | .lit _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _ | .typeBits ..
  | .fill _ | .functionCall .. | .aggregateMember .. | .packageAggElem .. | .unsupported .. => false

def PExpr.readsSignalConstList : List PExpr → Bool
  | [] => false
  | p :: ps => p.readsSignalConst || PExpr.readsSignalConstList ps
end

/-- The signal name for the select forms whose refusal can name their root. -/
def PExpr.signalRoot? : PExpr → Option String
  | .ident n => some n
  | .bitSel b _ | .partSel b _ _ => b.signalRoot?
  | .arrayElem n _ | .arrayPart n .. => some n
  | .aggregateMember n _ => some n
  | .packageAggElem pkg n _ => some (pkg ++ "::" ++ n)
  | _ => none

/-- An order comparison spelled signed by the frontend (`s<` …). -/
private def SymBinOp.signedOrder : SymBinOp → Bool
  | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge | .slt | .sle | .sgt | .sge => true
  | _ => false

/-- An order comparison spelled UNSIGNED by the frontend (plain `<` …:
slang spells every signed comparison `s<`). -/
private def SymBinOp.unsignedOrder : SymBinOp → Bool
  | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge => true
  | _ => false

/-- `+ - * / % & | ^` at `(w, s)` on operands already at that type. -/
private def constArith (op : SymBinOp) (w : Nat) (s : Bool) (a b : Int) : Except String Int :=
  match op with
  | .m0 .add => .ok (canonInt w s (a + b))
  | .m0 .sub => .ok (canonInt w s (a - b))
  | .m0 .mul | .mul => .ok (canonInt w s (a * b))
  | .m0 .div | .m0 .sdiv =>
      if b == 0 then .error "division by zero in a constant context (reads x)"
      else .ok (canonInt w s (a.tdiv b))
  | .m0 .rem | .m0 .srem =>
      if b == 0 then .error "modulo by zero in a constant context (reads x)"
      else .ok (canonInt w s (a.tmod b))
  | .div => if b == 0 then .error "division by zero in a constant context (reads x)"
            else .ok (canonInt w s (a.tdiv b))
  | .mod => if b == 0 then .error "modulo by zero in a constant context (reads x)"
            else .ok (canonInt w s (a.tmod b))
  | .m0 .and | .m0 .or | .m0 .xor =>
      let x := (a.emod ((2 : Int) ^ w)).toNat
      let y := (b.emod ((2 : Int) ^ w)).toNat
      .ok (canonInt w s (Int.ofNat (match op with
        | .m0 .and => x &&& y
        | .m0 .or => x ||| y
        | _ => x ^^^ y)))
  | _ => .error s!"operator '{op.sym}' outside the constant tier"

/-- `<< <<< >> >>> **` at `(w, s)`: `a` at that type, `b` the
self-determined right operand (a shift amount is unsigned in SV; a
negative constant one is loud here, as is a negative exponent). -/
private def constShift (op : SymBinOp) (w : Nat) (s : Bool) (a b : Int) : Except String Int :=
  if b < 0 then .error s!"negative right operand of '{op.sym}' in a constant context"
  else
    match op with
    | .shl | .ashl =>
        if (w : Int) ≤ b then .ok 0 else .ok (canonInt w s (a * (2 : Int) ^ b.toNat))
    | .shr =>
        if (w : Int) ≤ b then .ok 0
        else .ok (canonInt w s (a.emod ((2 : Int) ^ w) / (2 : Int) ^ b.toNat))
    | .ashr =>
        if s then
          if (w : Int) ≤ b then .ok (if a < 0 then -1 else 0)
          else .ok (a.fdiv ((2 : Int) ^ b.toNat))
        else if (w : Int) ≤ b then .ok 0
        else .ok (canonInt w s (a.emod ((2 : Int) ^ w) / (2 : Int) ^ b.toNat))
    | .pow =>
        if 4096 < b then .error "'**' exponent above 4096 in a constant context"
        else .ok (canonInt w s (a ^ b.toNat))
    | _ => .error s!"operator '{op.sym}' outside the constant tier"

/-- Equality/relational result on operands at their common type. -/
private def constCompare (op : SymBinOp) (a b : Int) : Int :=
  match op with
  | .m0 .ne | .m0 .caseNe | .m0 .wildNe | .cne => b2i (a != b)
  | .m0 .lt | .m0 .slt | .slt => b2i (decide (a < b))
  | .m0 .le | .m0 .sle | .sle => b2i (decide (a ≤ b))
  | .m0 .gt | .m0 .sgt | .sgt => b2i (decide (a > b))
  | .m0 .ge | .m0 .sge | .sge => b2i (decide (a ≥ b))
  | _ => b2i (a == b)

/-- **A constant select of a parameter's value reads labels as offsets
exactly** (round 3 folds, `IEnv.pdims`): a parameter whose declared range
is parameter-dependent must be ONE dimension `[m:0]` with `m ≥ 0` at this
point. The extractor emits such a select only where the range is canonical
at the default point (`_sym_param_root_select`), with its labels raw; at a
point where the range is `[-1:0]` (`[N-1:0]` at `N = 0`), label 1 is out of
range — Icarus 12.0 and Yosys 0.53 read x, the offset reading a bit of the
value — so the select is refused here, loudly. Every other base passes. -/
def paramSelectOk (env : IEnv) : PExpr → Except String Unit
  | .paramRef n none =>
      match env.pdims.lookup n with
      | none => .ok ()
      | some [(l, r)] =>
          if r == 0 && decide (0 ≤ l) then .ok ()
          else .error s!"select of parameter '{n}', whose packed range is [{l}:{r}] at these parameters: the envelope reads its labels as offsets from bit 0, exact only on a range [m:0] with m ≥ 0"
      | some ds =>
          .error s!"select of parameter '{n}', which has {ds.length} packed dimensions at these parameters (the constant tier selects bits of one dimension)"
  | _ => .ok ()

/-- **`$size`/`$high` of a declared signal at this point** (round 3 folds,
IEEE 1800-2023 §20.7): its FIRST (outermost) packed dimension as evaluated
in `IEnv.dims` — `$high` the larger label, `$size` the element count
`|msb - lsb| + 1`. They used to be read as `width - 1` and `width`, i.e.
for a 1-D `[W-1:0]` range: `$high` of `logic [7:4] u` is 7, not 3; of
`logic [N-1:0] v` at `N = 0` (the ascending `[-1:0]`) 0, not 1; `$size` of
`logic [3:0][7:0] m` is 4, not 32. A signal without a dimension entry here
(an enum- or struct-typed declaration, a scalar, a range that does not
evaluate, or a dimension bound read before the table exists) is loud. -/
def dimQuery (env : IEnv) (fn : String) (n : String) (high : Bool) : Except String Int :=
  match env.dims.lookup n with
  | some ((l, r) :: _) => .ok (if high then max l r else ((l - r).natAbs + 1 : Nat))
  | _ => .error s!"{fn} of '{n}': its packed range is not known here (only a declared signal with an explicit packed dimension list, after the declaration scope is built)"

/-- **Context-propagating operators** (IEEE 1800-2023 §11.6.1, §11.8.2):
the nodes whose operands take the width of the expression's context —
unary `- ~ +`, binary `+ - * / % & | ^`, the left operand of a shift or
power, and the arms of `?:`. A `Resize` the envelope wraps around one of
them (an assignment-like truncation at the DEFAULT point: `c = a + b` with
a 2-bit `c` and 4-bit operands) is no truncation at a point where the
context is wider: there the operands are extended BEFORE the operation and
its carry survives (`instExpr2`'s `resize` arm and `evalAt`'s, round 3
folds, repros `sx` and `vp_lp2`). Every other node — a leaf, a select, a
comparison, a reduction, a concatenation, a cast — is self-determined
under the conversion.

Round 6 folds (round 5 FOLDS verifier blocker 1, repro `vs_sqn`): a
`Squash2` is transparent here exactly as it is to `ctype` (round 5). A
2-state target NARROWER than its initializer at the default point is
`Resize(target, Squash2(default width, op))` in slang's tree; with the
`Squash2` opaque, the `resize` arm evaluated `op` at its OWN width at a
point where the target is the wider context: `localparam shortint H1 =
(U + 1'b1) >> 1` with a 4-bit `U = 15` was 0 where Icarus 12.0, the
Yosys 0.53 netlist and slang's elaboration give 8 (also `byte`, `bit
[7:0]`, `bit signed [7:0]`, a `byte` parameter default, and an `int` over
an operand wider than 32 bits at the default point). The value tier
refuses every `Squash2` (`instExpr2`), so only the constant tier reads
this. -/
def PExpr.ctxPropagates : PExpr → Bool
  | .unary (.m0 .lnot) _ => false
  | .unary (.m0 _) _ | .unary .plus _ => true
  | .binary op _ _ =>
      match op with
      | .m0 .add | .m0 .sub | .m0 .mul | .m0 .and | .m0 .or | .m0 .xor
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem | .m0 (.pow ..)
      | .m0 (.shl _) | .m0 (.shr _) | .m0 (.ashl _) | .m0 (.ashr _)
      | .mul | .div | .mod | .pow | .shl | .shr | .ashl | .ashr => true
      | _ => false
  | .ternary .. => true
  | .squash2 _ a => a.ctxPropagates
  | _ => false

/-- Whether an operand is a `Squash2` node (round 7 folds): the operand whose
context reading round 6 introduced (`PExpr.ctxPropagates`), and whose
own-width reading `evalAt`'s `resize`, `signedResize` and `squash2` arms
still require to be DEFINED (the round 7 gate there). -/
def PExpr.isSquash2 : PExpr → Bool
  | .squash2 .. => true
  | _ => false

/-- The refusal of a NEGATIVE genvar zero-extended past its 32 bits
(`PExpr.negGenvarAt`, and `PExpr.negGenvarWidened` in the value tier). -/
def negGenvarMsg (g : String) (w : Nat) : String :=
  s!"genvar '{g}' is negative here and is extended into an unsigned {w}-bit context: Icarus 12.0 sign-extends it, Yosys 0.53, Verilator 5.042 and the LRM (§27.4, §11.8.2) zero-extend it"

/-- **Where the oracles split**, constant tier (round 3 folds): the
operand of an unsigned conversion that is a NEGATIVE genvar, at a context
wider than its 32 bits — Icarus 12.0 sign-extends it, Yosys 0.53,
Verilator 5.042 and the LRM zero-extend it (`negGenvarMsg`). -/
def PExpr.negGenvarAt (env : IEnv) (w : Nat) : PExpr → Option String
  | .genvarRef g =>
      match env.vals.lookup g with
      | some v => if v < 0 && 32 < w then some g else none
      | none => none
  | _ => none

/-- A literal, possibly under casts and conversions: its own width is the
same at every parameter point. -/
def PExpr.isFixedLiteral : PExpr → Bool
  | .lit _ | .int _ | .fill _ => true
  | .cast _ a | .resize _ a | .signedResize _ a | .squash2 _ a => a.isFixedLiteral
  | _ => false

/-- The width a conversion node writes over an operand whose own width can
depend on the parameter point.  A literal operand has the same width at every
point, so the conversion the frontend recorded at the default point is the
conversion at this one. -/
def PExpr.convWidth? : PExpr → Option Nat
  | .resize w a | .signedResize w a | .squash2 w a => if a.isFixedLiteral then none else some w
  | _ => none

/-- The refusal of a converted concatenation operand whose written width is
not its operand's own width at this point. -/
def convPartMsg : String :=
  "Concat:converted-operand — a concatenation operand converted to a width other than its own at these parameters (an assignment-pattern member, or a cast): the recorded width is the default point's, and the constant tier does not model the member assignment outside a package"

/-- A converted concatenation operand is admitted where its written width is
its operand's own width `wa`. -/
def convPartOk (p : PExpr) (wa : Nat) : Except String Unit :=
  match p.convWidth? with
  | some w => if w != wa then .error convPartMsg else .ok ()
  | none => .ok ()

mutual

/-- Structural list worker for concatenation typing.  This is kept in the
same mutual block as `ctype` so the kernel sees the recursion through the
`PExpr.concat` constructor rather than through `List.mapM`'s closure. -/
def ctypeList (env : IEnv) : List PExpr → Except String (List (Nat × Bool))
  | [] => .ok []
  | p :: ps => do
      -- IEEE 1800-2023 §5.7.1 gives an unbased unsized literal one bit
      -- when it is an operand of a concatenation.  Keep that exception
      -- local to this list worker.  A fill outside a concatenation still
      -- needs its assignment context and remains loud in `ctype`.
      let ty ← match p with
        | .fill _ => .ok (1, false)
        | _ => ctype env p
      let rest ← ctypeList env ps
      .ok (ty :: rest)

/-- Structural list worker for concatenation evaluation. -/
def evalAtList (env : IEnv) : List PExpr → Except String (List (Nat × Int))
  | [] => .ok []
  | p :: ps => do
      let pty ← match p with
        | .fill _ => .ok (1, false)
        | _ => ctype env p
      -- A concatenation operand is self-determined, so a conversion on one
      -- is a real conversion to the width it writes (a member of an
      -- assignment pattern, §10.9.2).  `ctype` reads conversions as
      -- transparent; where the written width is not the operand's own at
      -- THIS point the two readings differ, and the operand is refused.
      convPartOk p pty.1
      let v ← match p with
        | .fill b =>
            match b with
            | .l0 => .ok 0
            | .l1 => .ok 1
            | .lx | .lz => .error "x/z literal in a constant context"
        | _ => evalAt env pty p
      let rest ← evalAtList env ps
      .ok ((pty.1, v) :: rest)

/-- **Self-determined type** `(width, signed)` of a constant expression
(IEEE 1800-2023 §11.6.1 Table 11-21, §11.8.1): unsized integers, genvars,
system calls and INT parameters are `(32, signed)`; a sized literal its own
width, unsigned (a signed literal arrives as `cast true` — `Ingest2`); a
typed parameter its declared type; context-determined operators the max of
their operands, signed iff both are; comparisons/logical/`!`/selects
unsigned; shifts and `**` the left operand's type. -/
def ctype (env : IEnv) : PExpr → Except String (Nat × Bool)
  | .int _ | .genvarRef _ | .sysCall .. => .ok (32, true)
  | .typeBits _ _ => .ok (32, true)
  | .lit v => .ok (v.width, false)
  | .ident n => .error s!"signal '{n}' in a constant context"
  | .paramRef n none =>
      match env.vals.lookup n with
      | some _ => .ok (32, true)
      | none =>
          match env.nvals.lookup n with
          | some (_, w, s) => .ok (w, s)
          | none => .error s!"unbound parameter '{n}'"
  | .paramRef n (some p) =>
      match env.packageConstType p n with
      | some ty => .ok ty
      | none => .error s!"package-scoped parameter '{p}::{n}'"
  | .functionCall n _ => .error s!"function '{n}' in a constant context"
  | .enumRef ty _ pkg =>
      match env.enumWidth ty pkg with
      | some w => .ok (w, false)
      | none => .error s!"unknown enum type '{ty}'"
  | .unary op a =>
      match op with
      | .m0 .lnot => .ok (1, false)
      | .m0 .neg | .m0 .pos | .m0 .bnot | .plus => ctype env a
      | .inc | .dec => .error "'++'/'--' outside a generate step"
  | .binary op l r =>
      match op.constClass with
      | .arith => do
          let (wl, sl) ← ctype env l
          let (wr, sr) ← ctype env r
          .ok (max wl wr, sl && sr)
      | .shift => ctype env l
      | .compare | .logical => .ok (1, false)
      | .vector => .error s!"vector operator '{op.sym}' in a constant context"
  | .ternary _ t e => do
      let (wt, st) ← ctype env t
      let (we, se) ← ctype env e
      .ok (max wt we, st && se)
  -- Round 3 folds (verifier finding, `vp_lp2`/`c_intlp`): an implicit
  -- conversion's envelope width is the DEFAULT point's context, so it is
  -- transparent here — what a conversion contributes to the max-of-operands
  -- width at THESE parameters is its operand's own width (`selfWidth2`'s
  -- reading in the value tier); the context it converts to is supplied
  -- from above (`evalAt`'s `ty`, an assignment target through
  -- `evalAssign`/`evalIntTarget`; round 4: never a width read off a
  -- conversion, which `evalSized` uses only to REFUSE a root whose outside
  -- target's reading differs, `PExpr.pushedTarget`). A `Squash2` is
  -- transparent too (round 5 folds, verifier repro `vq_sq2`): its width is
  -- the 2-state TARGET's at the default point (`bit [N-1:0] B = …` at
  -- `N = 32`) or its operand's there, and keeping it as a floor evaluated
  -- `(U + 1'b1) >> 1` at 32 bits at `N = 4` (8 where every tool gives 0);
  -- the target is supplied from above (`evalAssign` at the declared width,
  -- `evalIntTarget` for an `int`).
  | .resize _ a => do
      let (wa, _) ← ctype env a
      .ok (wa, false)
  | .signedResize _ a => do
      let (wa, _) ← ctype env a
      .ok (wa, true)
  | .squash2 _ a => ctype env a
  | .cast s a => do
      let (w, _) ← ctype env a
      .ok (w, s)
  | .bitSel .. => .ok (1, false)
  | .partSel b m l => do
      let _ ← ctype env b  -- a signal base is loud before its bounds are read
      let mv ← evalAt env (← ctype env m) m
      let lv ← evalAt env (← ctype env l) l
      if lv ≤ mv then .ok ((mv - lv).toNat + 1, false) else .error "bad part-select bounds"
  | .arrayElem n _ | .arrayPart n .. => .error s!"signal '{n}' in a constant context"
  | .aggregateMember n _ => .error s!"signal '{n}' in a constant context"
  | .packageAggElem pkg n _ =>
      match env.packageAgg? pkg n with
      | some agg =>
          match agg.elements.head? with
          | some v => .ok (v.width, agg.signed)
          | none => .error s!"package aggregate '{pkg}::{n}' has no elements"
      | none => .error s!"package aggregate '{pkg}::{n}' in a constant context"
  | .fill _ => .error "unbased-unsized literal in a constant context (no context width)"
  | .concat ps => do
      let tys ← ctypeList env ps
      let w := tys.foldl (fun total ty => total + ty.1) 0
      if w == 0 then .error "empty concatenation in a constant context"
      else .ok (w, false)
  | .repl count arg =>
      if arg.readsSignalConst then
        match arg.signalRoot? with
        | some n => .error s!"signal '{n}' in a constant context"
        | none => .error "signal operand in a constant context"
      else do
        let (wa, _) ← ctype env arg
        let n ← evalAt env (← ctype env count) count
        if n < 0 then .error "negative replication count"
        else if n == 0 then .error "empty replication in a constant context"
        else .ok (n.toNat * wa, false)
  | .reduce _ _ => .error "reduction in a constant context (width-dependent)"
  | .unsupported k _ => .error s!"unsupported node '{k}' in a constant context"

/-- **Value at a propagated type** `ty = (w, s)` (IEEE 1800-2023 §11.8.2):
context-determined operands are evaluated at `ty` itself, self-determined
ones (shift amounts, exponents, conditions, select labels, comparison and
logical operands, cast/resize operands) at their own `ctype`; leaves are
converted with `convertConst`; every result is `canonInt w s`. Loud on x/z,
division by zero, out-of-range constant selects, and a frontend
signed/unsigned comparison spelling the operand types contradict (the
envelope's typing and ours must agree — a missing `signed` field shows up
here, never as a silently different answer). -/
def evalAt (env : IEnv) (ty : Nat × Bool) : PExpr → Except String Int
  | .int v => .ok (convertConst 32 ty.1 ty.2 v)
  | .typeBits _ width => .ok (convertConst 32 ty.1 ty.2 width)
  | .lit v =>
      match v.toNat? with
      | some n => .ok (convertConst v.width ty.1 ty.2 n)
      | none => .error "x/z literal in a constant context"
  | .ident n => .error s!"signal '{n}' in a constant context"
  | .paramRef n none =>
      match env.vals.lookup n with
      | some v => .ok (convertConst 32 ty.1 ty.2 v)
      | none =>
          match env.nvals.lookup n with
          | some (v, w, _) => .ok (convertConst w ty.1 ty.2 v)
          | none => .error s!"unbound parameter '{n}'"
  | .paramRef n (some p) =>
      match env.packageFVal p n with
      | some (v, _, _) =>
          match v.toNat? with
          | some k => .ok (convertConst v.width ty.1 ty.2 k)
          | none => .error s!"package parameter '{p}::{n}' contains x/z bits in an integer-required constant context"
      | none =>
          match env.packageVal p n with
          | some v => .ok (convertConst 32 ty.1 ty.2 v)
          | none =>
              match env.packageNVal p n with
              | some (v, w, _) => .ok (convertConst w ty.1 ty.2 v)
              | none => .error s!"package-scoped parameter '{p}::{n}'"
  | .genvarRef n =>
      match env.vals.lookup n with
      | some v => .ok (convertConst 32 ty.1 ty.2 v)
      | none => .error s!"genvar '{n}' outside its loop"
  | .enumRef tn mem pkg =>
      match env.enumMember tn mem pkg with
      | some v =>
          match v.toNat? with
          | some k => .ok (convertConst v.width ty.1 ty.2 k)
          | none => .error s!"enum member {tn}::{mem} has x/z bits"
      | none => .error s!"unknown enum member {tn}::{mem}"
  | .sysCall fn a =>
      match fn, a with
      | .clog2, e => do
          -- IEEE 1800-2023 §20.8.1 reads the argument as unsigned.  The
          -- argument's self-determined width supplies the modulo domain, so
          -- `$clog2(-1)` on an unsized 32-bit integer is 32, not a refusal.
          let ety ← ctype env e
          let v ← evalAt env ety e
          let u := v.emod ((2 : Int) ^ ety.1)
          .ok (convertConst 32 ty.1 ty.2 (clog2 u.toNat : Int))
      | .bits, .ident n =>
          match env.widths.lookup n with
          | some w => .ok (convertConst 32 ty.1 ty.2 (w : Int))
          | none => .error s!"$bits/$size of undeclared signal '{n}'"
      | .bits, .paramRef n none =>
          match env.vals.lookup n with
          | some _ => .ok (convertConst 32 ty.1 ty.2 32)
          | none =>
              match env.nvals.lookup n with
              | some (_, w, _) => .ok (convertConst 32 ty.1 ty.2 (w : Int))
              | none => .error s!"$bits/$size of undeclared parameter '{n}'"
      | .bits, .paramRef n (some p) =>
          match env.packageFVal p n with
          | some (_, w, _) => .ok (convertConst 32 ty.1 ty.2 (w : Int))
          | none =>
              match env.packageVal p n with
              | some _ => .ok (convertConst 32 ty.1 ty.2 32)
              | none =>
                  match env.packageNVal p n with
                  | some (_, w, _) => .ok (convertConst 32 ty.1 ty.2 (w : Int))
                  | none => .error s!"$bits/$size of undeclared parameter '{p}::{n}'"
      | .bits, .int v => .ok (convertConst 32 ty.1 ty.2 v)
      | .bits, .typeBits _ w => .ok (convertConst 32 ty.1 ty.2 (w : Int))
      | .size, .ident n => do
          let v ← dimQuery env "$size" n false
          .ok (convertConst 32 ty.1 ty.2 v)
      | .high, .ident n => do
          let v ← dimQuery env "$high" n true
          .ok (convertConst 32 ty.1 ty.2 v)
      | f, _ => .error s!"{f.sym} argument outside the declared-signal tier"
  | .unary op a =>
      match op with
      | .m0 .lnot => do
          let x ← evalAt env (← ctype env a) a
          .ok (convertConst 1 ty.1 ty.2 (b2i (x == 0)))
      | .m0 .neg => do
          let x ← evalAt env ty a
          .ok (canonInt ty.1 ty.2 (-x))
      | .m0 .bnot => do
          let x ← evalAt env ty a
          .ok (canonInt ty.1 ty.2 (-x - 1))
      | .m0 .pos | .plus => evalAt env ty a
      | .inc | .dec => .error "'++'/'--' outside a generate step"
  | .binary op l r =>
      match op.constClass with
      | .arith => do
          let a ← evalAt env ty l
          let b ← evalAt env ty r
          constArith op ty.1 ty.2 a b
      | .shift => do
          let a ← evalAt env ty l
          let b ← evalAt env (← ctype env r) r
          constShift op ty.1 ty.2 a b
      | .compare => do
          let (wl, sl) ← ctype env l
          let (wr, sr) ← ctype env r
          let ct := (max wl wr, sl && sr)
          if (op.signedOrder && !ct.2) || (op.unsignedOrder && ct.2) then
            .error s!"'{op.sym}' contradicts the operand signedness (constant tier)"
          else do
            let a ← evalAt env ct l
            let b ← evalAt env ct r
            .ok (convertConst 1 ty.1 ty.2 (constCompare op a b))
      | .logical => do
          let a ← evalAt env (← ctype env l) l
          let b ← evalAt env (← ctype env r) r
          let v := match op with
            | .m0 .land | .land => a != 0 && b != 0
            | _ => a != 0 || b != 0
          .ok (convertConst 1 ty.1 ty.2 (b2i v))
      | .vector => .error s!"vector operator '{op.sym}' in a constant context"
  | .ternary c t e => do
      let cv ← evalAt env (← ctype env c) c
      if cv != 0 then evalAt env ty t else evalAt env ty e
  | .resize _ a => do
      -- An UNSIGNED conversion to the CONTEXT `ty` (the envelope's width
      -- is the default point's — round 3 folds, `vp_lp2`): a
      -- context-propagating operand (`PExpr.ctxPropagates` — at a root,
      -- the default point's assignment truncation) is evaluated AT the
      -- context, so its carry survives where the context is wider; any
      -- other operand is its own bits (a signed one — the extractor's
      -- `_sym_unsigned_simple_operand` marker — taken modulo its own
      -- width) zero-extended. A NEGATIVE genvar extended past 32 bits is
      -- where the oracles split (`negGenvarMsg`): loud.
      let (wa, sa) ← ctype env a
      if a.ctxPropagates && decide (wa < ty.1) then do
        -- Round 7 folds (round 6 FOLDS verifier major 4): through a
        -- `Squash2` the context reading is round 6's; the own-width reading
        -- (the round 5 one) must still be defined, so a shape round 5
        -- refused (`4'd8 / (U + 1'b1)` divides by zero at U's 4 bits) stays
        -- loud. The squash2-free twin never had this gate.
        if a.isSquash2 then discard (evalAt env (wa, sa) a)
        let x ← evalAt env (ty.1, sa) a
        .ok (canonInt ty.1 ty.2 x)
      else
        match a.negGenvarAt env ty.1 with
        | some g => .error (negGenvarMsg g ty.1)
        | none => do
            let x ← evalAt env (wa, sa) a
            .ok (canonInt ty.1 ty.2 (x.emod ((2 : Int) ^ wa)))
  | .signedResize _ a => do
      -- A SIGNED conversion to the context: sign extension of the operand's
      -- own value (a context-propagating operand evaluated at the context).
      let (wa, sa) ← ctype env a
      if a.ctxPropagates && decide (wa < ty.1) then do
        -- Round 7 folds: the `Squash2` own-width gate (the `resize` arm).
        if a.isSquash2 then discard (evalAt env (wa, sa) a)
        let x ← evalAt env (ty.1, sa) a
        .ok (canonInt ty.1 ty.2 x)
      else do
        let x ← evalAt env (wa, sa) a
        .ok (convertConst wa ty.1 ty.2 (canonInt wa true x))
  | .squash2 _ a => do
      -- 4-state → 2-state: no width of its own (x/z are loud in this tier).
      let (wa, sa) ← ctype env a
      if a.ctxPropagates && decide (wa < ty.1) then do
        -- Round 7 folds: the `Squash2` own-width gate (the `resize` arm).
        if a.isSquash2 then discard (evalAt env (wa, sa) a)
        let x ← evalAt env (ty.1, sa) a
        .ok (canonInt ty.1 ty.2 x)
      else do
        let x ← evalAt env (wa, sa) a
        .ok (convertConst wa ty.1 ty.2 x)
  | .cast s a => do
      let (wa, sa) ← ctype env a
      let x ← evalAt env (wa, sa) a
      .ok (convertConst wa ty.1 ty.2 (canonInt wa s x))
  | .bitSel base idx => do
      let (wb, sb) ← ctype env base
      paramSelectOk env base
      let bv ← evalAt env (wb, sb) base
      let i ← evalAt env (← ctype env idx) idx
      if i < 0 || (wb : Int) ≤ i then
        .error "constant bit select out of range (reads x)"
      else
        .ok (convertConst 1 ty.1 ty.2
          (Int.ofNat (((bv.emod ((2 : Int) ^ wb)).toNat >>> i.toNat) % 2)))
  | .partSel base m l => do
      let (wb, sb) ← ctype env base
      paramSelectOk env base
      let bv ← evalAt env (wb, sb) base
      let mv ← evalAt env (← ctype env m) m
      let lv ← evalAt env (← ctype env l) l
      if lv < 0 || mv < lv || (wb : Int) ≤ mv then
        .error "constant part select out of range (reads x)"
      else
        let fw := (mv - lv).toNat + 1
        .ok (convertConst fw ty.1 ty.2
          (Int.ofNat (((bv.emod ((2 : Int) ^ wb)).toNat >>> lv.toNat) % 2 ^ fw)))
  | .functionCall n _ => .error s!"function '{n}' in a constant context"
  | .arrayElem n _ | .arrayPart n .. => .error s!"signal '{n}' in a constant context"
  | .aggregateMember n _ => .error s!"signal '{n}' in a constant context"
  | .packageAggElem pkg n index =>
      match env.packageAgg? pkg n with
      | none => .error s!"package aggregate '{pkg}::{n}' in a constant context"
      | some agg => do
          let i ← evalAt env (← ctype env index) index
          match (packageAggLabels agg.msb agg.lsb).zip agg.elements |>.find?
              (fun (label, _) => label == i) with
          | some (_, v) =>
              match v.toNat? with
              | some k => .ok (convertConst v.width ty.1 ty.2 k)
              | none => .error s!"package aggregate '{pkg}::{n}' contains x/z bits in a constant context"
          | none => .error s!"package aggregate '{pkg}::{n}' index {i} is out of range"
  | .fill _ => .error "unbased-unsized literal in a constant context (no context width)"
  | .concat ps => do
      let parts ← evalAtList env ps
      let (w, v) := parts.foldl (fun (total, value) (pw, pv) =>
        (total + pw, value * ((2 : Int) ^ pw) + pv.emod ((2 : Int) ^ pw))) (0, 0)
      if w == 0 then .error "empty concatenation in a constant context"
      else .ok (convertConst w ty.1 ty.2 v)
  | .repl count arg =>
      if arg.readsSignalConst then
        match arg.signalRoot? with
        | some n => .error s!"signal '{n}' in a constant context"
        | none => .error "signal operand in a constant context"
      else do
        let (wa, sa) ← ctype env arg
        let n ← evalAt env (← ctype env count) count
        let v ← evalAt env (wa, sa) arg
        if n < 0 then .error "negative replication count"
        else if n == 0 then .error "empty replication in a constant context"
        else .ok (convertConst (n.toNat * wa) ty.1 ty.2 (repeatConst n.toNat wa v))
  | .reduce _ _ => .error "reduction in a constant context (width-dependent)"
  | .unsupported k _ => .error s!"unsupported node '{k}' in a constant context"

end

/-! Kernel-reduction guards for the ordinary constant path.  These must stay
`rfl`: if the concatenation workers accidentally force well-founded recursion,
even this non-concatenated literal ceases to reduce in proof-facing code. -/
example : ctype ({} : IEnv) (.int 5) = .ok (32, true) := by rfl
example : evalAt ({} : IEnv) (32, true) (.int 5) = .ok 5 := by rfl

/- A symbolic replication count must not be inspected before its operand.
   Otherwise a signal operand gets stuck on the parameter's undecidable
   value, which breaks proofs that intentionally classify the replication as
   non-constant. -/
example (accW : Nat) :
    ctype ({ nvals := [("AccW", (0, accW, false))] } : IEnv)
      (.repl (.paramRef "AccW" none) (.ident "a")) =
      .error "signal 'a' in a constant context" := by rfl
example (accW : Nat) :
    evalAt ({ nvals := [("AccW", (0, accW, false))] } : IEnv) (32, true)
      (.repl (.paramRef "AccW" none) (.ident "a")) =
      .error "signal 'a' in a constant context" := by rfl

example (accW : Nat) :
    ctype ({ nvals := [("AccW", (0, accW, false))] } : IEnv)
      (.repl (.paramRef "AccW" none) (.bitSel (.ident "a") (.int 0))) =
      .error "signal 'a' in a constant context" := by rfl
example (accW : Nat) :
    evalAt ({ nvals := [("AccW", (0, accW, false))] } : IEnv) (32, true)
      (.repl (.paramRef "AccW" none) (.bitSel (.ident "a") (.int 0))) =
      .error "signal 'a' in a constant context" := by rfl

example (accW : Nat) :
    ctype ({ nvals := [("AccW", (0, accW, false))] } : IEnv)
      (.repl (.paramRef "AccW" none)
        (.partSel (.ident "a") (.int 7) (.int 0))) =
      .error "signal 'a' in a constant context" := by rfl
example (accW : Nat) :
    evalAt ({ nvals := [("AccW", (0, accW, false))] } : IEnv) (32, true)
      (.repl (.paramRef "AccW" none)
        (.partSel (.ident "a") (.int 7) (.int 0))) =
      .error "signal 'a' in a constant context" := by rfl

/-- **The outside target of a constant root, where its tree records one**
(round 4 folds): `some w` for a conversion AT THE ROOT (`evalSized`
receives it from `evalInt`'s `resize`/`signedResize` arms). slang writes a
conversion around a whole constant only at the root of an assignment-like
context, and the extractor keeps one where slang made it same-width: a
genvar initializer, wrapped in `Resize(32, …)`/`SignedResize(32, …)`
(`_sym_genvar_init`; its target, a 32-bit `integer`, is the same at every
point), and an INT-class instance override into a typed parameter wider than
32 bits, wrapped at that width (`_sym_override_root`). `none` for every
other root: a select label, a generate condition or bound, a dimension
bound, an untyped localparam or parameter default — SELF-DETERMINED roots,
whose type is their own at THESE parameters (`ctype`). No conversion INSIDE
a root is read as a target: a signed-operand marker, a widened literal or a
widened parameter carries the width of the DEFAULT point's widest operand
(`SB + 1'b1` with `logic signed [N-1:0] SB` is `Resize(8, SB) + Resize(8,
1'b1)` at `N = 8`) — or, in a VALUE position, of a sibling signal (`a + P *
2` with a 33-bit `a` is `a + Resize(33, P) * 2`, `constAtCtx2`) — and
reading it as a target gave a self-determined root the default point's
width (round 3 FOLDS verifier, repros `rf_lbl`, `rf_gen`, `rf_lp`,
`rf_par`). -/
def PExpr.pushedTarget : PExpr → Option Nat
  | .resize w _ | .signedResize w _ => some w
  | _ => none

/-- The refusal of a constant root whose two readings differ
(`evalSized`). -/
def assignCtxMsg (w f : Nat) (v v' : Int) : String :=
  s!"Constant:assignment-context — a constant assigned to a {f}-bit target (a genvar initializer, or an INT-class instance override into a wider typed parameter) is {w} bits wide at these parameters, and its value at its own width ({v}) differs from its value at the target's ({v'}): IEEE 1800-2023 §10.8/§11.8.1, slang and Yosys 0.53 evaluate it at the target's width, Icarus 12.0 at its own (measured on genvar initializers) — refused where the readings differ"

/-- The refusal of a constant root assigned to a 32-bit target whose value
that target's signed `integer` would change (`evalSized`). -/
def assignFitMsg (w f : Nat) (v : Int) : String :=
  s!"Constant:assignment-context — a constant assigned to a {f}-bit target (a genvar initializer) is {w} bits wide at these parameters and its value {v} is not a 32-bit signed integer: IEEE 1800-2023 §27.4 and slang convert a genvar initializer to its `integer` (truncated and read signed), Icarus 12.0 and Yosys 0.53 keep the value whole (measured) — refused"

/-- **Width-exact constant evaluation** (round 4 folds): the value of `e`
at its OWN type at THESE parameters (`ctype` then `evalAt`) — `evalInt`'s
regime for every expression outside the INT class, the reading of every
self-determined root. Where the tree records an outside assignment-like
target (`PExpr.pushedTarget`: a genvar initializer, an INT-class override
into a typed parameter wider than 32 bits), the target's reading is `max(target, own width)`
(§10.8, §11.8.1) while Icarus 12.0 evaluates a genvar initializer at its own
width (repro `rf_gv`: `genvar g = U + 1'b1` with `logic [N-1:0] U = -1`
starts at 0 in Icarus and at 16 in slang's elaboration and the Yosys 0.53
netlist at `N = 4`): the own-width value is returned where the two
readings agree, and the root is REFUSED where they differ
(`Constant:assignment-context`), or where a root assigned to a 32-bit target
has a value that is no 32-bit signed integer (a genvar initializer of
2^32 + 1 is 1 in slang and §27.4, and one of `32'hFFFF_FFFF` is -1, while
Icarus and Yosys keep both whole; the check is keyed on the genvar's 32
bits, so an instance override of such a value into a 32-bit typed
parameter is refused the same way, a recorded over-refusal). The
target width is the default point's metadata, exact for a genvar's 32-bit
`integer` and for an override into a parameter of a fixed type; for one
whose own type is parameter-dependent it is the default point's, and only
the refusal side uses it. Typed localparams and typed parameter defaults, whose target is
known at every point, go through `evalAssign`/`evalIntTarget` instead. -/
def evalSized (env : IEnv) (e : PExpr) : Except String Int := do
  let (w, s) ← ctype env e
  let v ← evalAt env (w, s) e
  match e.pushedTarget with
  | none => .ok v
  | some f =>
      if w < f then do
        let v' ← evalAt env (f, s) e
        if convertConst w f s v == v' then .ok v else .error (assignCtxMsg w f v v')
      else if f == 32 && canonInt 32 true v != v then .error (assignFitMsg w f v)
      else .ok v

/-- **An assignment-like constant context** (§10.8, §11.8.1): `e`'s value
when assigned to a `w`-bit target — evaluated at the context `max w (its
own width at THESE parameters)` with its own signedness (the target's
signedness does not propagate into a right-hand side), before the caller
converts it to the target type (`canonInt`). The typed-localparam and
typed-parameter-default twin of the value tier's `fitExpr2` (round 3
folds, verifier finding `vp_lp2`: `localparam logic [N-1:0] L1 = 8'd200 +
8'd100` is `44` at `N = 8` and `300` at `N = 16`; the envelope's
default-point `Resize(4, …)` used to make it `12` at every point). -/
def evalAssign (env : IEnv) (w : Nat) (e : PExpr) : Except String Int :=
  if !env.stale.isEmpty && e.mentionsAny env.stale then
    .error "Constant:override-type — constant expression depends on an overridden untyped parameter"
  else match e with
  | .fill b =>
      -- An unbased unsized 0/1 literal takes the assignment target's
      -- context width (§5.7.1).  It has no self-determined `ctype`, so this
      -- root case must be handled before the ordinary `ctype`/`evalAt` path.
      match b with
      | .l0 => .ok (canonInt w false 0)
      | .l1 => .ok (canonInt w false ((2 : Int) ^ w - 1))
      | .lx | .lz => .error "x/z literal in a constant context"
  | _ => do
      let (we, se) ← ctype env e
      evalAt env (max w we, se) e

/-! ## Constant functions and package constants

One constant evaluator serves package constants, module parameter defaults,
localparams and generate-local parameters.

* **Expressions** get their meaning from `ctype`/`evalAt` (IEEE 1800-2023
  §11.6, §11.8), the width-exact evaluator above, at ANY width: a value is a
  mathematical integer canonical for its propagated type.  `evalVec` is its
  four-state extension: where `evalAt` answers, `evalVec` is that answer; where
  `evalAt` refuses because a bit is x or z, `evalVec` MOVES the bits exactly
  (literals, package constants, concatenation, replication, selects, `?:`
  with a known condition, conversions).  An operator applied to an x/z
  operand stays a loud refusal: it is not modelled, never approximated.
* **Assignment patterns.**  The envelope still carries an assignment pattern
  for a packed struct (§10.9.2) as a concatenation whose operands are
  conversions to the member widths (an ingestion rewrite that is NOT retired
  here: the node needs its own `PExpr` constructor).  `ctype`/`evalAt` read a
  conversion as transparent (its width is the default point's), which is
  wrong for such an operand, so `evalVec` never hands an expression with a
  converted concatenation operand to `evalAt`: it converts each such operand
  to its written width (`evalPart`).  That width is exact in a package, which
  has one point; in a module function a converted operand whose width
  differs from its operand's is refused.
* **Constant functions** (§13.4.3) are kept as written (`PFnStmt`) and are
  executed statement by statement (`execFnStmt`): automatic variables, blocking
  assignments, `if`, `case`, `for`, `return`.  A call is evaluated before the
  expression it stands in (`PExpr.elabConst`): constant functions have no side
  effects, so the order is unobservable.  A call in the unselected arm of a
  `?:` with a known condition is not evaluated; the one difference left from
  §11.3.5 short-circuiting is a refusal where a call in an unevaluated
  operand of `&&` or `||` would itself refuse.
* **Scope.**  A function body is evaluated in the scope that declares the
  function (§13.4.3, §23.9): for a module function, the module scope
  (`IEnv.declEnv`: the caller's environment without the generate-scope
  bindings the canonical E route records), never the generate scope of the
  call.  A module constant the function reads that still has two bindings
  there (a generate scope bound without that record) is refused.
* **Selects of function variables.**  The frontend owns the translation of
  a label to an offset: it writes a literal label of a range that is not
  `[m:0]` as the bit (or element) offset, and refuses a computed label of
  such a range.  The evaluator reads every select index of a function
  variable as an offset (`selWindow`), and refuses a computed index on a
  variable whose range is not `[m:0]`.
* **Explicit size casts** (§6.24.1) arrive in constant positions as a call of
  the reserved name `sizeCastName` (the AST has no cast-to-size constructor
  yet): the operand is self-determined, then padded or truncated to the cast
  width, at every parameter point.
* **Termination without fuel in the meaning.**  A call of a function that is
  already being evaluated on the chain is recursion and is refused by name
  (`constCallAt`'s `active`); a chain without a repeated function is at most
  as long as the function table, which the structural counter starts from.  A `for` loop has an
  elaboration budget (`fnLoopBudget` iterations); exceeding it is a refusal,
  never a value.
* **Package constants** are bound in dependency order (`pkgRounds`), read from
  every reference of the initializer and of the functions it calls.  A cycle
  is refused.  A constant this tool cannot evaluate is recorded with its reason
  and left unbound: the approved parser has accepted the package, so the
  refusal is a limit of this tool and concerns only a design that reads the
  constant (§26.3: a package item is referenced through `pkg::name` or an
  import).  A read of it refuses loudly, as does every constant that depends
  on it. -/

/-- A reference a constant expression depends on. -/
inductive ConstDep where
  | const (pkg name : String)
  | call (name : String)
  /-- An unqualified parameter or localparam (a constant of the declaring scope). -/
  | param (name : String)
deriving Repr, BEq, Inhabited

/-- The reserved callee name of an explicit size cast `w'(e)` (§6.24.1) in a
constant position: `functionCall sizeCastName [.int w, e]`.  No identifier of
the language can spell it. -/
def sizeCastName : String := "<size cast>"

def ConstDep.isCall : ConstDep → Bool
  | .call _ => true
  | .const .. => false
  | .param _ => false

mutual
/-- Every package constant and every function a constant expression names,
at any depth.  Each expression kind has its own case. -/
def PExpr.constDeps : PExpr → List ConstDep
  | .lit _ => []
  | .ident _ => []
  | .paramRef n none => [.param n]
  | .paramRef n (some p) => [.const p n]
  | .genvarRef _ => []
  | .enumRef .. => []
  | .int _ => []
  | .fill _ => []
  | .unary _ a => a.constDeps
  | .binary _ l r => l.constDeps ++ r.constDeps
  | .ternary c t e => c.constDeps ++ t.constDeps ++ e.constDeps
  | .concat ps => PExpr.constDepsList ps
  | .resize _ a => a.constDeps
  | .signedResize _ a => a.constDeps
  | .squash2 _ a => a.constDeps
  | .sysCall _ a => a.constDeps
  | .typeBits .. => []
  | .bitSel b i => b.constDeps ++ i.constDeps
  | .partSel b m l => b.constDeps ++ m.constDeps ++ l.constDeps
  | .repl n a => n.constDeps ++ a.constDeps
  | .reduce _ a => a.constDeps
  | .cast _ a => a.constDeps
  | .arrayElem _ is => PExpr.constDepsList is
  | .arrayPart _ is _ a b => PExpr.constDepsList is ++ a.constDeps ++ b.constDeps
  -- A member path of an unpacked aggregate is a signal read: the constant
  -- tier refuses the node itself, so it has no constant dependencies.
  | .aggregateMember .. => []
  | .packageAggElem pkg n i => .const pkg n :: i.constDeps
  | .functionCall n args => .call n :: PExpr.constDepsList args
  | .unsupported .. => []

def PExpr.constDepsList : List PExpr → List ConstDep
  | [] => []
  | e :: es => e.constDeps ++ PExpr.constDepsList es
end

/-- Whether a constant expression contains a function call. -/
def PExpr.hasCall (e : PExpr) : Bool := e.constDeps.any ConstDep.isCall

/-- A variable of a constant-function activation: its bits at the declared
width, its declared signedness and its packed ranges, outermost first, as
evaluated at its declaration (`[]`: one range `[width-1:0]`). -/
structure CVar where
  v : LVec
  signed : Bool
  dims : List (Int × Int) := []

/-- The local variables of one constant-function activation.  The first
match wins, so an inner declaration shadows an outer one. -/
abbrev CLocals := List (String × CVar)

/-- Overwrite the bits of the innermost variable named `n`. -/
def localsSet : CLocals → String → LVec → CLocals
  | [], _, _ => []
  | (m, x) :: rest, n, v =>
      if m == n then (m, { x with v := v }) :: rest else (m, x) :: localsSet rest n v

/-- A literal index, as the frontend writes a label it has translated. -/
def PExpr.isLiteralIndex : PExpr → Bool
  | .int _ | .lit _ => true
  | _ => false

/-- **The window of a select on a variable's first packed dimension**
(§7.4.1, §11.5.1).  `a` and `b` are OFFSETS (equal for a bit or element
select; the high and low offset of a part select), counted in elements of
the first dimension from its least significant end: the frontend has already
translated a literal label of a shifted or reversed range.  `literal` says
the index expressions are literals; a computed index is admitted only on a
range `[m:0]`, where label and offset coincide.  The window is
`offset * element width` bits up, where an element is the product of the
inner dimensions.  An offset outside the dimension (x in the LRM) is
refused.  Returns the inner dimensions too. -/
def selWindow (width : Nat) (dims : List (Int × Int)) (literal : Bool) (a b : Int) :
    Except String (Nat × Nat × List (Int × Int)) :=
  let ds := if dims.isEmpty then [((width : Int) - 1, 0)] else dims
  match ds with
  | [] => .error "internal: no packed dimension"
  | (l, r) :: rest =>
      let size : Int := ((l - r).natAbs + 1 : Nat)
      let elemW := rest.foldl (fun acc d => acc * ((d.1 - d.2).natAbs + 1)) 1
      if !(r == 0 && decide (0 ≤ l)) && !literal then
        .error s!"select of a function variable whose range is [{l}:{r}] by a computed index: the frontend translates only literal labels of a range other than [m:0]"
      else if a < b then .error "part select of a function variable with its bounds reversed"
      else if b < 0 || size ≤ a then
        .error "constant select of a function variable out of range (reads x)"
      else .ok (b.toNat * elemW, (a - b + 1).toNat * elemW, rest)

/-- The value a select of a local variable reads.  The result is a plain
vector: a further select reads its index as an offset from bit 0, which the
frontend guarantees for literal labels; for a computed index it is exact only
when at most one inner dimension is left and it is `[m:0]`, so any other
shape is a loud node. -/
def localSelect (x : CVar) (literal : Bool) (a b : Int) : Except String PExpr := do
  let (lo, w, rest) ← selWindow x.v.width x.dims literal a b
  match rest with
  | [] => .ok (.lit (x.v.extract lo w))
  | [(m, 0)] =>
      if 0 ≤ m && a == b then .ok (.lit (x.v.extract lo w))
      else .ok (.unsupported "Select:local-dimensions" "a select of a function variable that leaves a packed range other than one element [m:0]")
  | _ => .ok (.unsupported "Select:local-dimensions" "a select of a function variable that leaves a packed range other than one element [m:0]")

/-- The local variable a select reads directly (`v`, or `v` under the
frontend's declared-signed marker). -/
def localBase (σ : CLocals) : PExpr → Option CVar
  | .ident n => σ.lookup n
  | .cast _ (.ident n) => σ.lookup n
  | _ => none

/-- Bits of a value at the propagated type `ty` (§11.8.2), the four-state
twin of `convertConst`: extended with the sign bit only when the propagated
type is signed, else with zeros, or truncated.  x and z bits are carried. -/
def convertVec (ty : Nat × Bool) (v : LVec) : LVec :=
  if ty.2 then v.resizeSigned ty.1 else v.resizeU ty.1

/-- `n` copies of `v`, as one vector (§11.4.12.1). -/
def replVec : Nat → LVec → LVec
  | 0, _ => ⟨#[]⟩
  | n + 1, v => ⟨v.bits ++ (replVec n v).bits⟩

/-- The unsigned integer of a vector whose bits are all known. -/
def knownVec (v : LVec) : Except String Int :=
  match v.toNat? with
  | some n => .ok (n : Int)
  | none => .error "x/z in a constant condition, bound or count: not modelled"

/-- A conversion node (the frontend's width-changing conversions). -/
def PExpr.isConversion : PExpr → Bool
  | .resize .. | .signedResize .. | .squash2 .. => true
  | _ => false

mutual
/-- Whether some concatenation in `e` has a conversion as an operand: the
shape the envelope gives an assignment pattern for a packed struct. -/
def PExpr.hasConvertedPart : PExpr → Bool
  | .concat ps => ps.any PExpr.isConversion || PExpr.hasConvertedPartList ps
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a | .sysCall _ a
  | .reduce _ a | .cast _ a => a.hasConvertedPart
  | .binary _ l r | .bitSel l r | .repl l r => l.hasConvertedPart || r.hasConvertedPart
  | .ternary c t e | .partSel c t e =>
      c.hasConvertedPart || t.hasConvertedPart || e.hasConvertedPart
  | .functionCall _ args => PExpr.hasConvertedPartList args
  | .arrayElem _ is => PExpr.hasConvertedPartList is
  | .arrayPart _ is _ a b =>
      PExpr.hasConvertedPartList is || a.hasConvertedPart || b.hasConvertedPart
  | .packageAggElem _ _ i => i.hasConvertedPart
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _ | .fill _
  | .typeBits .. | .aggregateMember .. | .unsupported .. => false

def PExpr.hasConvertedPartList : List PExpr → Bool
  | [] => false
  | e :: es => e.hasConvertedPart || PExpr.hasConvertedPartList es
end

/-- The refusal of an operator over an assignment pattern. -/
def convertedPartMsg : String :=
  "an operator over a concatenation with converted operands (an assignment pattern) is not modelled"

mutual
/-- **The four-state constant evaluator.**  `mode = some ty` gives the value
at the propagated type `ty` (`evalVec`): `evalAt`'s value where it answers;
otherwise the exact movement of bits through the nodes that only move bits,
with `evalAt`'s refusal for every other node.  `mode = none` gives a
self-determined operand at its own width (`evalPart`: a concatenation
operand, the base of a select, a replicated value).

A conversion node as a self-determined operand is the conversion to the
width it writes (§10.9.2: a member of an assignment pattern is evaluated as
an assignment to the member; §6.24.1 for a size cast): the operand as
assigned to that many bits.  `exact` says the widths the frontend wrote are
the widths at THIS point (a package, which has no parameters); outside a
package a conversion whose width differs from its operand's is refused. -/
def evalVecM (env : IEnv) (exact : Bool) (mode : Option (Nat × Bool)) (e : PExpr) :
    Except String LVec :=
  match mode, e with
  | none, .concat ps => do
      let vs ← evalPartList env exact ps
      .ok (LVec.concatMany vs.toArray)
  -- An unbased unsized literal fills the width it is converted to (§5.7.1).
  | none, .resize w (.fill b) | none, .signedResize w (.fill b) => .ok (LVec.replicate w b)
  | none, .squash2 w (.fill b) => .ok (LVec.replicate w b).toTwoState
  | none, .resize w a | none, .signedResize w a => do
      let (wa, sa) ← ctype env a
      if !exact && wa != w && !a.isFixedLiteral then .error convPartMsg
      else do
        let v ← evalVecM env exact (some (max w wa, sa)) a
        .ok (v.resizeU w)
  | none, .squash2 w a => do
      let (wa, sa) ← ctype env a
      if !exact && wa != w && !a.isFixedLiteral then .error convPartMsg
      else do
        let v ← evalVecM env exact (some (max w wa, sa)) a
        .ok (v.resizeU w).toTwoState
  | mode, e => do
      let ty ← match mode with
        | some ty => pure ty
        | none => ctype env e
      match (if e.hasConvertedPart then .error convertedPartMsg else evalAt env ty e) with
      | .ok v => .ok (LVec.ofInt ty.1 v)
      | .error msg =>
          match e with
          | .lit v => .ok (convertVec ty v)
          | .fill b => .ok (LVec.replicate ty.1 b)
          | .paramRef n (some p) =>
              match env.packageFVal p n with
              | some (v, _, _) => .ok (convertVec ty v)
              | none => .error msg
          | .enumRef tn mem pkg =>
              match env.enumMember tn mem pkg with
              | some v => .ok (convertVec ty v)
              | none => .error msg
          | .ternary c t el => do
              -- §11.4.11 merges the arms under an x/z condition; that merge
              -- is not modelled, so the condition must be known.
              let cv ← knownVec (← evalVecM env exact none c)
              if cv != 0 then evalVecM env exact (some ty) t else evalVecM env exact (some ty) el
          | .resize _ a => do
              let (wa, sa) ← ctype env a
              if a.ctxPropagates && decide (wa < ty.1) then do
                let x ← evalVecM env exact (some (ty.1, sa)) a
                .ok (x.resizeU ty.1)
              else do
                let x ← evalVecM env exact (some (wa, sa)) a
                .ok (x.resizeU ty.1)
          | .signedResize _ a => do
              let (wa, sa) ← ctype env a
              if a.ctxPropagates && decide (wa < ty.1) then do
                let x ← evalVecM env exact (some (ty.1, sa)) a
                .ok (x.resizeU ty.1)
              else do
                let x ← evalVecM env exact (some (wa, sa)) a
                .ok (convertVec ty x)
          | .squash2 _ a => do
              -- 4-state to 2-state (§6.11.2): an x or z bit becomes 0.
              let (wa, sa) ← ctype env a
              if a.ctxPropagates && decide (wa < ty.1) then do
                let x ← evalVecM env exact (some (ty.1, sa)) a
                .ok (x.toTwoState.resizeU ty.1)
              else do
                let x ← evalVecM env exact (some (wa, sa)) a
                .ok (convertVec ty x.toTwoState)
          | .cast _ a => do
              let (wa, sa) ← ctype env a
              let x ← evalVecM env exact (some (wa, sa)) a
              .ok (convertVec ty x)
          | .bitSel base idx => do
              paramSelectOk env base
              let bv ← evalVecM env exact none base
              let i ← knownVec (← evalVecM env exact none idx)
              if (bv.width : Int) ≤ i then
                .error "constant bit select out of range (reads x)"
              else .ok (convertVec ty (bv.extract i.toNat 1))
          | .partSel base m l => do
              paramSelectOk env base
              let bv ← evalVecM env exact none base
              let mv ← knownVec (← evalVecM env exact none m)
              let lv ← knownVec (← evalVecM env exact none l)
              if mv < lv || (bv.width : Int) ≤ mv then
                .error "constant part select out of range (reads x)"
              else .ok (convertVec ty (bv.extract lv.toNat ((mv - lv).toNat + 1)))
          | .concat ps => do
              let vs ← evalPartList env exact ps
              let v := LVec.concatMany vs.toArray
              if v.width == 0 then .error "empty concatenation in a constant context"
              else .ok (convertVec ty v)
          | .repl count arg => do
              let n ← knownVec (← evalVecM env exact none count)
              let v ← evalVecM env exact none arg
              if n == 0 then .error "empty replication in a constant context"
              else .ok (convertVec ty (replVec n.toNat v))
          | _ => .error msg

/-- The operands of a concatenation, each at its own width. -/
def evalPartList (env : IEnv) (exact : Bool) : List PExpr → Except String (List LVec)
  | [] => .ok []
  | p :: ps => do
      let v ← evalVecM env exact none p
      let rest ← evalPartList env exact ps
      .ok (v :: rest)
end

/-- **Four-state value at a propagated type** `ty` (§11.8.2). -/
def evalVec (env : IEnv) (exact : Bool) (ty : Nat × Bool) (e : PExpr) : Except String LVec :=
  evalVecM env exact (some ty) e

/-- **A self-determined operand**, four-state, at its own width. -/
def evalPart (env : IEnv) (exact : Bool) (e : PExpr) : Except String LVec :=
  evalVecM env exact none e

/-- **An assignment-like context, four-state** (§10.8, §11.8.1): the bits a
`w`-bit target receives from `e`.  `e` is evaluated at `max w (its own
width)` with its own signedness, then truncated to the target; an unbased
unsized literal fills the target (§5.7.1).  The four-state twin of
`evalAssign`. -/
def assignVec (env : IEnv) (exact : Bool) (w : Nat) : PExpr → Except String LVec
  | .fill b => .ok (LVec.replicate w b)
  | e =>
      if e.hasConvertedPart then do
        -- An assignment pattern is unsigned and has its own exact width.
        let v ← evalPart env exact e
        .ok (v.resizeU w)
      else do
        let (we, se) ← ctype env e
        let v ← evalVec env exact (max w we, se) e
        .ok (v.resizeU w)

/-- A dimension bound of a type named in a constant function, at its own
type (`evalSized`). -/
def constDimsWidth (env : IEnv) : List PDim → Except String Nat
  | [] => .ok 1
  | d :: rest => do
      let m ← evalSized env d.msb
      let l ← evalSized env d.lsb
      let w ← constDimsWidth env rest
      .ok (((m - l).natAbs + 1) * w)

/-- Width of a type named in a constant function or a package constant:
packed dimensions evaluated here; an enum by its base; a typedef declared in
a package by its recorded width (a package has no parameters to override, so
that width is the same at every point).  A typedef declared in a module is
refused: its recorded width is the default point's. -/
def constTypeWidth (env : IEnv) : PType → Except String Nat
  | .packed dims _ => constDimsWidth env dims
  | .typeRef n pkg r =>
      match env.enumWidth n pkg with
      | some w => .ok w
      | none =>
          match pkg, r with
          | some _, some w => .ok w
          | _, _ => .error s!"type '{n}': its width at these parameters is not retained (only an enum, or a typedef declared in a package)"
  | .unrecoverable _ => .error "unrecoverable packed dimensions"

/-- The packed ranges of a type named in a constant function, evaluated
here; `[]` (one range `[width-1:0]`) for a type that is not a list of packed
dimensions. -/
def constTypeDims (env : IEnv) : PType → Except String (List (Int × Int))
  | .packed dims _ => dims.mapM fun d => do pure ((← evalSized env d.msb), (← evalSized env d.lsb))
  | .typeRef .. => .ok []
  | .unrecoverable _ => .ok []

mutual
/-- **Close a constant expression** over the local variables `σ` of a
function activation and over its constant-function calls (§13.4.3, §11.2):

* a reference to a local variable becomes its current value, with the
  variable's width and signedness;
* a select of a local variable reads the window its declared range gives
  (`localSelect`);
* a call, innermost first, becomes the value `call` gives it, at the return
  width and signedness.  `call` receives `exact` (see `evalVec`), the
  callee's name and the actual arguments, already closed.

Every other node is kept.  With no locals this evaluates the calls of an
expression (`constCalls`).

Only the SELECTED arm of a `?:` whose condition is known has its calls
evaluated (§11.4.11).  The other arm is closed with `stub`: a call there
becomes an all-x value of the callee's return type, which gives the `?:` its
type and is never read. -/
def PExpr.elabConst (env : IEnv) (exact : Bool) (stub : Bool)
    (call : Bool → String → List PExpr → Except String (LVec × Bool)) (σ : CLocals) :
    PExpr → Except String PExpr
  | .ident n =>
      match σ.lookup n with
      | some x => .ok (.cast x.signed (.lit x.v))
      | none => .ok (.ident n)
  | .functionCall n args => do
      let args' ← PExpr.elabConstList env exact stub call σ args
      if n == sizeCastName then
        -- §6.24.1: the operand is self-determined; it is then padded (with
        -- its sign bit when signed) or truncated to the cast width, and keeps
        -- its signedness.
        match args' with
        | [.int w, a] => do
            let (wa, sa) ← ctype env a
            if stub then .ok (.cast sa (.lit (LVec.xVec w.toNat)))
            else do
              let v ← evalVec env exact (wa, sa) a
              .ok (.cast sa (.lit (if sa then v.resizeSigned w.toNat else v.resizeU w.toNat)))
        | _ => .error "malformed size cast"
      else if stub then
        match env.functions.find? (fun f => f.name == n) with
        | some f => do
            let rw ← constTypeWidth env.declEnv f.returnType
            .ok (.cast f.isSigned (.lit (LVec.xVec rw)))
        | none => .error s!"function '{n}' in a constant context"
      else do
        let (v, s) ← call exact n args'
        .ok (.cast s (.lit v))
  | .bitSel b i => do
      let i' ← i.elabConst env exact stub call σ
      match localBase σ b with
      | some x => do
          let iv ← evalAt env (← ctype env i') i'
          localSelect x i.isLiteralIndex iv iv
      | none => do .ok (.bitSel (← b.elabConst env exact stub call σ) i')
  | .partSel b m l => do
      let m' ← m.elabConst env exact stub call σ
      let l' ← l.elabConst env exact stub call σ
      match localBase σ b with
      | some x => do
          let mv ← evalAt env (← ctype env m') m'
          let lv ← evalAt env (← ctype env l') l'
          localSelect x (m.isLiteralIndex && l.isLiteralIndex) mv lv
      | none => do .ok (.partSel (← b.elabConst env exact stub call σ) m' l')
  | .lit v => .ok (.lit v)
  | .paramRef n p => .ok (.paramRef n p)
  | .genvarRef n => .ok (.genvarRef n)
  | .enumRef t m p => .ok (.enumRef t m p)
  | .int v => .ok (.int v)
  | .fill b => .ok (.fill b)
  | .unary o a => do .ok (.unary o (← a.elabConst env exact stub call σ))
  | .binary o l r => do
      .ok (.binary o (← l.elabConst env exact stub call σ) (← r.elabConst env exact stub call σ))
  | .ternary c t e => do
      let c' ← c.elabConst env exact stub call σ
      let known : Option Bool :=
        if stub then none
        else
          match (do let ty ← ctype env c'; evalAt env ty c' : Except String Int) with
          | .ok v => some (v != 0)
          | .error _ => none
      match known with
      | some true =>
          .ok (.ternary c' (← t.elabConst env exact false call σ) (← e.elabConst env exact true call σ))
      | some false =>
          .ok (.ternary c' (← t.elabConst env exact true call σ) (← e.elabConst env exact false call σ))
      | none =>
          .ok (.ternary c' (← t.elabConst env exact stub call σ) (← e.elabConst env exact stub call σ))
  | .concat ps => do .ok (.concat (← PExpr.elabConstList env exact stub call σ ps))
  | .resize w a => do .ok (.resize w (← a.elabConst env exact stub call σ))
  | .signedResize w a => do .ok (.signedResize w (← a.elabConst env exact stub call σ))
  | .squash2 w a => do .ok (.squash2 w (← a.elabConst env exact stub call σ))
  | .sysCall f a => do .ok (.sysCall f (← a.elabConst env exact stub call σ))
  | .typeBits n w => .ok (.typeBits n w)
  | .repl n a => do
      .ok (.repl (← n.elabConst env exact stub call σ) (← a.elabConst env exact stub call σ))
  | .reduce o a => do .ok (.reduce o (← a.elabConst env exact stub call σ))
  | .cast s a => do .ok (.cast s (← a.elabConst env exact stub call σ))
  | .arrayElem n is => do .ok (.arrayElem n (← PExpr.elabConstList env exact stub call σ is))
  | .arrayPart n is mode a b => do
      .ok (.arrayPart n (← PExpr.elabConstList env exact stub call σ is) mode
        (← a.elabConst env exact stub call σ) (← b.elabConst env exact stub call σ))
  | .aggregateMember n path => .ok (.aggregateMember n path)
  | .packageAggElem pkg n i => do .ok (.packageAggElem pkg n (← i.elabConst env exact stub call σ))
  | .unsupported k t => .ok (.unsupported k t)

def PExpr.elabConstList (env : IEnv) (exact : Bool) (stub : Bool)
    (call : Bool → String → List PExpr → Except String (LVec × Bool)) (σ : CLocals) :
    List PExpr → Except String (List PExpr)
  | [] => .ok []
  | e :: es => do
      let e' ← e.elabConst env exact stub call σ
      let es' ← PExpr.elabConstList env exact stub call σ es
      .ok (e' :: es')
end

/-- Elaboration budget of one constant-function `for` loop. -/
def fnLoopBudget : Nat := 65536

/-- How a statement of a constant function ends: it falls through with the
variables it leaves, or the function returns a value. -/
inductive FnFlow where
  | normal (σ : CLocals)
  | returned (v : LVec)

/-- A `for` loop (§12.7.1): test, body, step, at most `fnLoopBudget` times.
The count is an elaboration budget whose exhaustion is a refusal. -/
def fnLoop (cond : CLocals → Except String Bool)
    (body step : CLocals → Except String FnFlow) : Nat → CLocals → Except String FnFlow
  | 0, _ => .error s!"a constant-function loop runs more than {fnLoopBudget} iterations (elaboration budget)"
  | n + 1, σ => do
      if !(← cond σ) then return .normal σ
      match ← body σ with
      | .returned v => return .returned v
      | .normal σ1 =>
          match ← step σ1 with
          | .returned v => return .returned v
          | .normal σ2 => fnLoop cond body step n σ2

/-- What a constant-function activation evaluates against: the constants in
scope, how to evaluate a nested call, and the function's own result variable
(§13.4.1: the function name is an implicit variable of the return type). -/
structure FnCtx where
  env : IEnv
  /-- The function is declared in a package (`evalVec`'s `exact`). -/
  exact : Bool
  call : Bool → String → List PExpr → Except String (LVec × Bool)
  retName : String
  retWidth : Nat

/-- An expression of the body, with the local variables read and the calls
evaluated. -/
def FnCtx.expr (c : FnCtx) (σ : CLocals) (e : PExpr) : Except String PExpr :=
  e.elabConst c.env c.exact false c.call σ

/-- The bits a `w`-bit variable receives from `e`. -/
def FnCtx.assign (c : FnCtx) (σ : CLocals) (w : Nat) (e : PExpr) : Except String LVec := do
  assignVec c.env c.exact w (← c.expr σ e)

/-- A self-determined integer (a select bound). -/
def FnCtx.int (c : FnCtx) (σ : CLocals) (e : PExpr) : Except String Int := do
  let e' ← c.expr σ e
  evalAt c.env (← ctype c.env e') e'

/-- The condition of an `if` or a loop (§12.4): taken exactly when the value
has a 1 bit; 0, x and z are not taken. -/
def FnCtx.cond (c : FnCtx) (σ : CLocals) (e : PExpr) : Except String Bool := do
  let e' ← c.expr σ e
  let v ← evalVec c.env c.exact (← ctype c.env e') e'
  .ok v.condTrue

/-- Every pattern expression of a `case` (they size the comparison, §12.5.1). -/
def fnCasePatterns : List (List PExpr × PFnStmt) → List PExpr
  | [] => []
  | (pats, _) :: rest => pats ++ fnCasePatterns rest

mutual
/-- **One statement of a constant function** (§13.4.3, §12). -/
def execFnStmt (c : FnCtx) (σ : CLocals) : PFnStmt → Except String FnFlow
  | .decl name ty s two init => do
      -- §6.8: an uninitialized variable starts at x (4-state) or 0 (2-state).
      let w ← constTypeWidth c.env ty
      let dims ← constTypeDims c.env ty
      let v ← match init with
        | some e => c.assign σ w e
        | none => pure (if two then LVec.replicate w .l0 else LVec.xVec w)
      return .normal ((name, { v := v, signed := s, dims := dims }) :: σ)
  | .assign target value =>
      match target with
      | .ident n =>
          match σ.lookup n with
          | none => .error s!"assignment to '{n}', which is not a variable of the constant function (§13.4.3)"
          | some x => do
              let v ← c.assign σ x.v.width value
              return .normal (localsSet σ n v)
      | .bitSel n idx =>
          match σ.lookup n with
          | none => .error s!"assignment to '{n}', which is not a variable of the constant function (§13.4.3)"
          | some x => do
              let i ← c.int σ idx
              let (lo, w, _) ← selWindow x.v.width x.dims idx.isLiteralIndex i i
              let v ← c.assign σ w value
              return .normal (localsSet σ n (x.v.insertAt lo v))
      | .partSel n msb lsb =>
          match σ.lookup n with
          | none => .error s!"assignment to '{n}', which is not a variable of the constant function (§13.4.3)"
          | some x => do
              let m ← c.int σ msb
              let l ← c.int σ lsb
              let (lo, w, _) ← selWindow x.v.width x.dims (msb.isLiteralIndex && lsb.isLiteralIndex) m l
              let v ← c.assign σ w value
              return .normal (localsSet σ n (x.v.insertAt lo v))
      | _ => .error "assignment target outside the constant-function tier"
  | .incDec n inc =>
      -- §11.4.2: `i++` is `i = i + 1`; an x or z bit makes the result x.
      match σ.lookup n with
      | none => .error s!"assignment to '{n}', which is not a variable of the constant function (§13.4.3)"
      | some x =>
          let v := match x.v.toNat? with
            | some k => LVec.ofInt x.v.width ((k : Int) + (if inc then 1 else -1))
            | none => LVec.xVec x.v.width
          .ok (.normal (localsSet σ n v))
  | .ifStmt cnd t el => do
      if ← c.cond σ cnd then execFnStmt c σ t
      else
        match el with
        | some s => execFnStmt c σ s
        | none => return .normal σ
  | .caseStmt subj items dflt => do
      -- §12.5.1: the case expression and every item expression are sized to
      -- the widest of them (signed only if all are), then compared bit for
      -- bit, x and z included.
      let se ← c.expr σ subj
      let pes ← (fnCasePatterns items).mapM (c.expr σ)
      let tys ← (se :: pes).mapM (ctype c.env)
      let ty : Nat × Bool := (tys.foldl (fun w t => max w t.1) 0, tys.all (·.2))
      let sv ← evalVec c.env c.exact ty se
      match ← execFnItems c σ sv ty items with
      | some flow => return flow
      | none =>
          match dflt with
          | some s => execFnStmt c σ s
          | none => return .normal σ
  | .forLoop init cnd step body => do
      match ← execFnStmts c σ init with
      | .returned v => return .returned v
      | .normal σ1 =>
          match ← fnLoop (fun s => c.cond s cnd) (fun s => execFnStmt c s body)
              (fun s => execFnStmts c s step) fnLoopBudget σ1 with
          | .returned v => return .returned v
          -- The loop variable's scope ends with the loop.
          | .normal σ2 => return .normal (σ2.drop (σ2.length - σ.length))
  | .block ss => do
      match ← execFnStmts c σ ss with
      | .returned v => return .returned v
      -- Variables declared in the block go out of scope at its end.
      | .normal σ' => return .normal (σ'.drop (σ'.length - σ.length))
  | .ret (some e) => do
      -- §13.4.1: `return e` assigns `e` to the result and ends the function.
      return .returned (← c.assign σ c.retWidth e)
  | .ret none =>
      match σ.lookup c.retName with
      | some x => .ok (.returned x.v)
      | none => .error "internal: the function result variable is not in scope"
  | .unsupported k _ => .error s!"statement '{k}' in a constant function is not modelled"

def execFnStmts (c : FnCtx) (σ : CLocals) : List PFnStmt → Except String FnFlow
  | [] => .ok (.normal σ)
  | s :: rest => do
      match ← execFnStmt c σ s with
      | .returned v => return .returned v
      | .normal σ' => execFnStmts c σ' rest

/-- The first `case` item with a matching expression, in source order. -/
def execFnItems (c : FnCtx) (σ : CLocals) (sv : LVec) (ty : Nat × Bool) :
    List (List PExpr × PFnStmt) → Except String (Option FnFlow)
  | [] => .ok none
  | (pats, body) :: rest => do
      let hit ← pats.anyM fun p => do
        let pv ← evalVec c.env c.exact ty (← c.expr σ p)
        pure (pv == sv)
      if hit then return some (← execFnStmt c σ body)
      else execFnItems c σ sv ty rest
end

/-- The constant dependencies of a function declaration: its types, and its
body as written. -/
def PType.constDeps : PType → List ConstDep
  | .packed dims _ => dims.flatMap fun d => d.msb.constDeps ++ d.lsb.constDeps
  | .typeRef .. => []
  | .unrecoverable _ => []

/-- The index expressions of an assignment target.  A concatenation target
is refused by the executor, so it contributes none. -/
def PLhs.constDeps : PLhs → List ConstDep
  | .ident _ => []
  | .bitSel _ i => i.constDeps
  | .partSel _ m l => m.constDeps ++ l.constDeps
  | .concat _ => []
  | .arrayElem _ is => PExpr.constDepsList is
  | .arrayBitSel _ is b => PExpr.constDepsList is ++ b.constDeps
  | .arrayPart _ is _ a b => PExpr.constDepsList is ++ a.constDeps ++ b.constDeps
  | .aggregateMember .. => []

mutual
def PFnStmt.constDeps : PFnStmt → List ConstDep
  | .decl _ ty _ _ init =>
      ty.constDeps ++ (match init with | some e => e.constDeps | none => [])
  | .assign t v => t.constDeps ++ v.constDeps
  | .incDec .. => []
  | .ifStmt c t el =>
      c.constDeps ++ t.constDeps ++ (match el with | some s => s.constDeps | none => [])
  | .caseStmt subj items dflt =>
      subj.constDeps ++ PFnStmt.constDepsItems items ++
        (match dflt with | some s => s.constDeps | none => [])
  | .forLoop init c step body =>
      PFnStmt.constDepsList init ++ c.constDeps ++ PFnStmt.constDepsList step ++ body.constDeps
  | .block ss => PFnStmt.constDepsList ss
  | .ret (some e) => e.constDeps
  | .ret none => []
  | .unsupported .. => []

def PFnStmt.constDepsList : List PFnStmt → List ConstDep
  | [] => []
  | s :: rest => s.constDeps ++ PFnStmt.constDepsList rest

def PFnStmt.constDepsItems : List (List PExpr × PFnStmt) → List ConstDep
  | [] => []
  | (pats, body) :: rest =>
      PExpr.constDepsList pats ++ body.constDeps ++ PFnStmt.constDepsItems rest
end

def PFunction.constDeps (f : PFunction) : List ConstDep :=
  f.returnType.constDeps ++ f.formals.flatMap (·.type.constDeps) ++
    (match f.stmts with
     | some ss => PFnStmt.constDepsList ss
     | none => f.body.constDeps)

/-- The dependencies of the functions `names`, and of every function they
call; the count bounds the chain as in `constCallAt`. -/
def fnConstDepsAt (fs : List PFunction) : Nat → List String → List ConstDep
  | 0, _ => []
  | d + 1, names =>
      names.flatMap fun n =>
        match fs.find? (fun f => f.name == n) with
        | none => []
        | some f =>
            let ds := f.constDeps
            ds ++ fnConstDepsAt fs d (ds.filterMap fun
              | .call m => some m
              | .const .. | .param _ => none)

/-- Bind the formals to the actuals, each as if by assignment (§13.5).  The
actuals are the caller's expressions, evaluated in the caller's environment
`env` with the caller's `exact`; the formal types belong to the function and
are evaluated in its declaring scope `denv`. -/
def bindFormals (denv env : IEnv) (exact : Bool) : List PDecl → List PExpr → Except String CLocals
  | f :: fs, a :: as => do
      let w ← constTypeWidth denv f.type
      let dims ← constTypeDims denv f.type
      let v ← assignVec env exact w a
      let rest ← bindFormals denv env exact fs as
      .ok ((f.name, { v := v, signed := f.isSigned, dims := dims }) :: rest)
  | _, _ => .ok []

/-- The module constants a function reads, directly or through the functions
it calls. -/
def fnFreeParams (fs : List PFunction) (f : PFunction) : List String :=
  let ds := f.constDeps
  (ds ++ fnConstDepsAt fs fs.length (ds.filterMap fun
    | .call m => some m
    | .const .. | .param _ => none)).filterMap fun
      | .param n => some n
      | .const .. | .call _ => none

/-- How many bindings a constant name has in an environment. -/
def IEnv.bindingCount (env : IEnv) (n : String) : Nat :=
  (env.vals.filter (·.1 == n)).length + (env.nvals.filter (·.1 == n)).length

/-- **A constant function call** (§13.4.3): the result at the return width,
with the return type's signedness.  `d` counts the calls still allowed on
this chain; it starts at the number of declared functions (`constCalls`).
`active` is the chain of functions being evaluated: a call of one of them is
recursion and is refused by name, so the count never reaches 0 (a chain
without a repeated function is no longer than the function table).  `env` and `exact` are
the caller's (for the actual arguments).  The body, the formal types and the
calls of the body are evaluated in the scope that declares the function
(`IEnv.declEnv`), with the callee's own `exact` (`PFunction.fromPackage`).
A module constant the function reads that has more than one binding there
is shadowed by a scope this environment does not record: refused.  Storage
is irrelevant to a constant call: each elaboration-time call starts from the
variables' initial values (§13.4.3), so a static function is evaluated like
an automatic one. -/
def constCallAt (d : Nat) (active : List String) (env : IEnv) (exact : Bool) (name : String)
    (args : List PExpr) : Except String (LVec × Bool) :=
  match env.functions.find? (fun f => f.name == name) with
  | none => .error s!"function '{name}' in a constant context"
  | some f =>
      match d with
      | 0 =>
          .error s!"function '{name}': the call chain is longer than the number of functions (a recursive constant function is not modelled)"
      | d + 1 =>
          let denv := env.declEnv
          if active.contains name then
            .error s!"function '{name}' calls itself, directly or through other functions: a recursive constant function is not modelled"
          else if f.formals.length != args.length then
            .error s!"function '{name}' argument count mismatch"
          else
            match (fnFreeParams env.functions f).find? (fun n => denv.bindingCount n > 1) with
            | some n =>
                .error s!"function '{name}' reads the constant '{n}', which is bound more than once at this call (a generate scope shadows the declaring scope): refused"
            | none =>
            (do
              let σ ← bindFormals denv env exact f.formals args
              let rw ← constTypeWidth denv f.returnType
              let rdims ← constTypeDims denv f.returnType
              let init := if f.returnTwoState then LVec.replicate rw .l0 else LVec.xVec rw
              let c : FnCtx :=
                { env := denv, exact := f.fromPackage, call := constCallAt d (name :: active) denv,
                  retName := f.name, retWidth := rw }
              let stmts := match f.stmts with
                | some ss => ss
                | none => [PFnStmt.ret (some f.body)]
              let result : CVar := { v := init, signed := f.isSigned, dims := rdims }
              match ← execFnStmts c ((f.name, result) :: σ) stmts with
              | .returned v => pure (v, f.isSigned)
              | .normal σ' =>
                  match σ'.lookup f.name with
                  | some x => pure (x.v, f.isSigned)
                  | none => throw "internal: the function result variable is not in scope"
            : Except String (LVec × Bool)).mapError fun m =>
              -- One prefix, the innermost refused function of the chain.
              if m.startsWith "constant function " then m else s!"constant function '{name}': {m}"

/-- Evaluate every constant-function call of `e` in `env`.  `exact` as in
`evalVec`: the expression is a package's. -/
def constCalls (env : IEnv) (e : PExpr) (exact : Bool := false) : Except String PExpr :=
  e.elabConst env exact false (constCallAt env.functions.length [] env) []

/-- A constant expression with calls, evaluated by `use` after its calls;
`msg` (the refusal of the call-free reading) when it has none. -/
def withConstCalls {α : Type} (env : IEnv) (e : PExpr) (msg : String)
    (use : PExpr → Except String α) : Except String α :=
  if e.hasCall then do
    let e' ← constCalls env e
    use e'
  else .error msg

/-- Evaluate a symbolic expression as an integer constant (parameter
defaults, localparams, generate headers/conditions, dimension bounds,
system calls, select labels) at its SELF-DETERMINED type. Loud `.error` on
anything value-tier or unbound. INT-class operands take the mathematical
fast path below (the ledger's unbounded-`Int` regime, unchanged equations
for every proof over genvar/parameter arithmetic); any other operand sends
the node to `evalSized`, the width-exact §11.6/§11.8 evaluation — see the
module docstring. -/
def evalInt (env : IEnv) : PExpr → Except String Int
  | .int v => .ok v
  | .typeBits _ width => .ok width
  | .lit v =>
      match v.toNat? with
      | some n => .ok (n : Int)
      | none => .error "x/z literal in a constant context"
  | .ident n => .error s!"signal '{n}' in a constant context"
  -- A constant function call (§13.4.3), or an explicit size cast, as an
  -- integer: evaluated by the constant-function evaluator (`constCalls`),
  -- then read at the result's own type.
  | .functionCall n args =>
      match constCalls env (.functionCall n args) with
      | .ok e' => evalSized env e'
      | .error m => .error m
  | .paramRef n none =>
      match env.vals.lookup n with
      | some v => .ok v
      | none =>
          if n ∈ env.stale then .error "Constant:override-type — constant expression depends on an overridden untyped parameter"
          else
            match env.nvals.lookup n with
            | some (v, _, _) => .ok v
            | none => .error s!"unbound parameter '{n}'"
  | .paramRef n (some p) =>
      match env.packageFVal p n with
      | some (v, w, s) =>
          match v.toNat? with
          -- The value at the constant's declared type: a signed constant with
          -- its top bit set is negative (§11.8.1), as in `evalAt`.
          | some k => .ok (canonInt w s k)
          | none => .error s!"package parameter '{p}::{n}' contains x/z bits in an integer-required constant context"
      | none =>
          match env.packageVal p n with
          | some v => .ok v
          | none =>
              match env.packageNVal p n with
              | some (v, _, _) => .ok v
              | none => .error s!"package-scoped parameter '{p}::{n}'"
  | .genvarRef n =>
      match env.vals.lookup n with
      | some v => .ok v
      | none =>
          match env.nvals.lookup n with
          | some (v, _, _) => .ok v
          | none => .error s!"genvar '{n}' outside its loop"
  | .enumRef ty mem pkg =>
      match env.enumMember ty mem pkg with
      | some v =>
          match v.toNat? with
          | some n => .ok (n : Int)
          | none => .error s!"enum member {ty}::{mem} has x/z bits"
      | none => .error s!"unknown enum member {ty}::{mem}"
  | .fill _ => .error "unbased-unsized literal in a constant context (no context width)"
  | .unary op a =>
      if a.isInt env then do
        let v ← evalInt env a
        match op with
        | .m0 .neg => .ok (-v)
        | .m0 .lnot => .ok (b2i (v == 0))
        | .m0 .bnot => .error "'~' in a constant context (width-dependent)"
        | .m0 .pos | .plus => .ok v
        | .inc | .dec => .error "'++'/'--' outside a generate step"
      else evalSized env (.unary op a)
  | .binary op l r =>
      if l.isInt env && r.isInt env then do
        let a ← evalInt env l
        let b ← evalInt env r
        match op with
        | .m0 .add => .ok (a + b)
        | .m0 .sub => .ok (a - b)
        | .m0 .and | .m0 .or | .m0 .xor =>
            if a < 0 || b < 0 then
              .error "bitwise operator on a negative constant (width-dependent)"
            else
              let x := a.toNat
              let y := b.toNat
              .ok (Int.ofNat (match op with
                | .m0 .and => x &&& y
                | .m0 .or => x ||| y
                | _ => x ^^^ y))
        | .m0 .eq => .ok (b2i (a == b))
        | .m0 .ne => .ok (b2i (a != b))
        | .m0 .caseEq => .ok (b2i (a == b))
        | .m0 .caseNe => .ok (b2i (a != b))
        | .m0 .wildEq => .ok (b2i (a == b))
        | .m0 .wildNe => .ok (b2i (a != b))
        | .m0 .casez | .m0 .casex =>
            .error "wildcard case matching is not a constant expression"
        | .m0 .land => .ok (b2i (a != 0 && b != 0))
        | .m0 .lor => .ok (b2i (a != 0 || b != 0))
        | .m0 .lt | .m0 .slt | .slt => .ok (b2i (decide (a < b)))
        | .m0 .le | .m0 .sle | .sle => .ok (b2i (decide (a ≤ b)))
        | .m0 .gt | .m0 .sgt | .sgt => .ok (b2i (decide (a > b)))
        | .m0 .ge | .m0 .sge | .sge => .ok (b2i (decide (a ≥ b)))
        | .ceq => .ok (b2i (a == b))
        | .cne => .ok (b2i (a != b))
        | .land => .ok (b2i (a != 0 && b != 0))
        | .lor => .ok (b2i (a != 0 || b != 0))
        | .m0 .mul | .mul => .ok (a * b)
        | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem =>
            .error "vector quotient/remainder requires operand widths"
        | .m0 (.pow ..) => .error "vector power requires operand widths"
        | .m0 (.shl ..) | .m0 (.shr ..) | .m0 (.ashl ..) | .m0 (.ashr ..) =>
            .error "vector shift requires operand widths"
        | .div => if b == 0 then .error "division by zero" else .ok (a.tdiv b)
        | .mod => if b == 0 then .error "modulo by zero" else .ok (a.tmod b)
        | .pow =>
            if b < 0 then .error "'**' with a negative exponent" else .ok (a ^ b.toNat)
        | .shl | .ashl =>
            if b < 0 then .error "shift by a negative amount"
            else if 32 ≤ b then .error "shift amount above 32 in an untyped constant context"
            else .ok (a * (2 : Int) ^ b.toNat)
        | .shr =>
            if a < 0 then .error "'>>' of a negative constant (width-dependent)"
            else if b < 0 then .error "shift by a negative amount"
            else if 32 ≤ b then .error "shift amount above 32 in an untyped constant context"
            else .ok (a.tdiv ((2 : Int) ^ b.toNat))
        | .ashr =>
            if b < 0 then .error "shift by a negative amount"
            else if 32 ≤ b then .error "shift amount above 32 in an untyped constant context"
            else .ok (a.fdiv ((2 : Int) ^ b.toNat))
      else evalSized env (.binary op l r)
  | .ternary c t e =>
      if t.isInt env && e.isInt env then do
        let cv ← evalInt env c
        if cv != 0 then evalInt env t else evalInt env e
      else evalSized env (.ternary c t e)
  | .concat ps => evalSized env (.concat ps)
  -- A conversion at a root (round 3 folds; round 4: `evalSized` reads it
  -- as an assignment-like target, `PExpr.pushedTarget`) — the operand's
  -- own bits zero-extended (a signed operand under the
  -- `_sym_unsigned_simple_operand` marker taken modulo its own width
  -- first: `-3` is `2^32 - 3`), never truncated to the default point's
  -- width (the caller converts to its target), loud where the target's
  -- reading differs (a genvar initializer, `_sym_genvar_init`).
  | .resize w a => evalSized env (.resize w a)
  -- A sign extension (extractor `_sym_signed_widening`, `SB + 5` with a
  -- `byte` SB): width-exact.
  | .signedResize w a => evalSized env (.signedResize w a)
  | .squash2 _ a => evalInt env a
  | .sysCall fn a =>
      match fn, a with
      | .clog2, e => do
          let v ← evalInt env e
          -- The INT-class path is exactly the unsized 32-bit argument of
          -- §20.8.1, including negative values interpreted modulo 2^32.
          let u := if v < 0 then v.emod ((2 : Int) ^ 32) else v
          .ok (clog2 u.toNat : Int)
      | .bits, .ident n =>
          match env.widths.lookup n with
          | some w => .ok (w : Int)
          | none => .error s!"$bits/$size of undeclared signal '{n}'"
      | .bits, .paramRef n none =>
          match env.vals.lookup n with
          | some _ => .ok 32
          | none =>
              match env.nvals.lookup n with
              | some (_, w, _) => .ok (w : Int)
              | none => .error s!"$bits/$size of undeclared parameter '{n}'"
      | .bits, .paramRef n (some p) =>
          match env.packageFVal p n with
          | some (_, w, _) => .ok (w : Int)
          | none =>
              match env.packageVal p n with
              | some _ => .ok 32
              | none =>
                  match env.packageNVal p n with
                  | some (_, w, _) => .ok (w : Int)
                  | none => .error s!"$bits/$size of undeclared parameter '{p}::{n}'"
      | .bits, .typeBits _ w => .ok (w : Int)
      | .size, .ident n => dimQuery env "$size" n false
      | .high, .ident n => dimQuery env "$high" n true
      | f, _ => .error s!"{f.sym} argument outside the declared-signal tier"
  | .bitSel base idx =>
      if base.isInt env then do
        let v ← evalInt env base
        let i ← evalInt env idx
        if v < 0 then .error "bit select of a negative constant (width-dependent)"
        else if i < 0 || 32 ≤ i then .error "constant bit select out of range (reads x)"
        else .ok (Int.ofNat ((v.toNat >>> i.toNat) % 2))
      else evalSized env (.bitSel base idx)
  | .partSel base msb lsb =>
      if base.isInt env then do
        let v ← evalInt env base
        let m ← evalInt env msb
        let l ← evalInt env lsb
        if v < 0 then .error "part select of a negative constant (width-dependent)"
        else if l < 0 || m < l || 32 ≤ m then .error "bad part-select bounds"
        else .ok (Int.ofNat ((v.toNat >>> l.toNat) % 2 ^ (m - l + 1).toNat))
      else evalSized env (.partSel base msb lsb)
  | .repl _ _ => .error "replication in a constant context"
  | .reduce _ _ => .error "reduction in a constant context (width-dependent)"
  | .cast s a => if s && a.isInt env then evalInt env a else evalSized env (.cast s a)
  | .arrayElem n _ | .arrayPart n .. => .error s!"signal '{n}' in a constant context"
  | .aggregateMember n _ => .error s!"signal '{n}' in a constant context"
  | .packageAggElem pkg n _ => .error s!"package aggregate '{pkg}::{n}' in a constant context"
  | .unsupported k _ => .error s!"unsupported node '{k}' in a constant context"

/-- Exact-mode proof entry point.  INT-class trees whose constants are in
`nvals` are evaluated through their propagated signed-32 type; the legacy
`evalInt` path remains available for unbounded proof arithmetic. -/
def evalIntExactRec (env : IEnv) : PExpr → Except String Int
  | .int v => .ok (canonInt 32 true v)
  | .paramRef n none =>
      match env.intVal? n with
      | some v => .ok (canonInt 32 true v)
      | none => .error s!"unbound parameter '{n}'"
  | .genvarRef n =>
      match env.intVal? n with
      | some v => .ok (canonInt 32 true v)
      | none => .error s!"genvar '{n}' outside its loop"
  | .unary op a =>
      if a.isIntExact env then do
        let v ← evalIntExactRec env a
        match op with
        | .m0 .neg => .ok (canonInt 32 true (-v))
        | .m0 .pos | .plus => .ok (canonInt 32 true v)
        | _ => evalSized env (.unary op a)
      else evalSized env (.unary op a)
  | .binary op l r =>
      if l.isIntExact env && r.isIntExact env && op.intArith then do
        let a ← evalIntExactRec env l
        let b ← evalIntExactRec env r
        match op with
        | .m0 .add => .ok (canonInt 32 true (a + b))
        | .m0 .sub => .ok (canonInt 32 true (a - b))
        | .m0 .mul | .mul => .ok (canonInt 32 true (a * b))
        | .div => if b == 0 then .error "division by zero" else .ok (canonInt 32 true (a.tdiv b))
        | .mod => if b == 0 then .error "modulo by zero" else .ok (canonInt 32 true (a.tmod b))
        | .pow => if b < 0 then .error "negative exponent" else .ok (canonInt 32 true (a ^ b.toNat))
        -- IEEE 1800-2023 §11.4.10 converts the shift amount to an unsigned
        -- value. A negative signed `int` count is therefore far beyond the
        -- 32-bit operand: left/logical-right shifts produce zero, while an
        -- arithmetic-right shift fills with the sign bit. Cap every amount
        -- at 32 before constructing a power so a hostile parameter cannot
        -- make the kernel build `2^2147483647`.
        | .m0 (.shl _) | .m0 (.ashl _) | .shl | .ashl =>
            if b < 0 then .ok 0 else
            if 32 ≤ b then .ok 0 else
            .ok (canonInt 32 true (a * (2 : Int)^b.toNat))
        | .m0 (.shr _) | .shr =>
            if b < 0 then .ok 0 else
            if 32 ≤ b then .ok 0 else
              let ua := if a < 0 then a + (2 : Int) ^ 32 else a
              .ok (canonInt 32 true (ua.tdiv ((2 : Int)^b.toNat)))
        | .m0 (.ashr _) | .ashr =>
            if b < 0 then .ok (if a < 0 then -1 else 0) else
            if 32 ≤ b then .ok (if a < 0 then -1 else 0) else
            .ok (canonInt 32 true (a.fdiv ((2 : Int)^b.toNat)))
        | _ => evalSized env (.binary op l r)
      else evalSized env (.binary op l r)
  | e => evalSized env e

def evalIntExact (env : IEnv) (e : PExpr) : Except String Int :=
  if !env.int32 then evalInt env e else evalIntExactRec env e

#guard (evalIntExact ({ nvals := [("N", (5, 32, true))], int32 := true } : IEnv)
    (.binary (.m0 .add) (.paramRef "N" none) (.int 1))).toOption == some 6
#guard (evalIntExact ({ nvals := [("N", (2147483647, 32, true))], int32 := true } : IEnv)
    (.binary (.m0 .add) (.paramRef "N" none) (.int 1))).toOption == some (-2147483648)

/-- Generate-time integer arithmetic uses the declared `integer`/`int`
32-bit signed type (§27.4, §6.11). -/
def guard32 (v : Int) : Int := canonInt 32 true v

def guardBits (v : Int) : Nat := (guard32 v).emod ((2 : Int) ^ 32) |>.toNat

def guardShift32 (a b : Int) : Except String Int :=
  if b < 0 || 32 ≤ b then .error "invalid shift in generate guard"
  else .ok (guard32 (a * (2 : Int) ^ b.toNat))

def guardLookup (env : IEnv) (n : String) : Option Int :=
  match env.vals.lookup n with
  | some v => some v
  | none => (env.nvals.lookup n).map (·.1)

def guardShr32 (signed : Bool) (a b : Int) : Except String Int :=
  if b < 0 || 32 ≤ b then .error "invalid shift in generate guard"
  else
    let bits := guardBits a
    let q := bits / (2 : Int) ^ b.toNat
    if signed && a < 0 then
      .ok (guard32 (q - (2 : Int) ^ (32 - b.toNat)))
    else .ok (guard32 q)

/-- Generate guards use the same 32-bit integer arithmetic as `int` for the
legacy fallback vocabulary.  Self-determined system functions use their own
operand widths, as required by IEEE 1800-2023 §20.8.1. -/
def evalGenGuard32 (env : IEnv) : PExpr → Except String Int
  | .int v => .ok (guard32 v)
  | .paramRef n none =>
      match guardLookup env n with
      | some v => .ok (guard32 v)
      | none => .error s!"unbound parameter '{n}'"
  | .genvarRef n =>
      match guardLookup env n with
      | some v => .ok (guard32 v)
      | none => .error s!"genvar '{n}' outside its loop"
  | .paramRef n (some p) =>
      match env.packageFVal p n with
      | some (v, _, _) =>
          match v.toNat? with
          | some k => .ok (guard32 k)
          | none => .error s!"package parameter '{p}::{n}' contains x/z bits in an integer-required constant context"
      | none =>
          match env.packageVal p n with
          | some v => .ok (guard32 v)
          | none =>
              match env.packageNVal p n with
              | some (v, _, _) => .ok (guard32 v)
              | none => .error s!"package-scoped parameter '{p}::{n}'"
  | .unary op a => do
      let v ← evalGenGuard32 env a
      match op with
      | .m0 .neg => .ok (guard32 (-v))
      | .m0 .pos | .plus => .ok (guard32 v)
      | .m0 .lnot => .ok (guard32 (b2i (v == 0)))
      | _ => .error "operator outside generate integer guards"
  | .binary op l r => do
      let a ← evalGenGuard32 env l
      let b ← evalGenGuard32 env r
      match op with
      | .m0 .add => .ok (guard32 (a + b))
      | .m0 .sub => .ok (guard32 (a - b))
      | .m0 .mul | .mul => .ok (guard32 (a * b))
      | .m0 .and => .ok (guard32 (Int.ofNat (guardBits a &&& guardBits b)))
      | .m0 .or => .ok (guard32 (Int.ofNat (guardBits a ||| guardBits b)))
      | .m0 .xor => .ok (guard32 (Int.ofNat (guardBits a ^^^ guardBits b)))
      | .m0 .eq => .ok (guard32 (b2i (a == b)))
      | .m0 .ne => .ok (guard32 (b2i (a != b)))
      | .m0 .lt | .m0 .slt | .slt => .ok (guard32 (b2i (a < b)))
      | .m0 .le | .m0 .sle | .sle => .ok (guard32 (b2i (a ≤ b)))
      | .m0 .gt | .m0 .sgt | .sgt => .ok (guard32 (b2i (a > b)))
      | .m0 .ge | .m0 .sge | .sge => .ok (guard32 (b2i (a ≥ b)))
      | .m0 .land | .land => .ok (guard32 (b2i (a != 0 && b != 0)))
      | .m0 .lor | .lor => .ok (guard32 (b2i (a != 0 || b != 0)))
      | .m0 (.shl _) | .shl => guardShift32 a b
      | .m0 (.shr signed) => guardShr32 signed a b
      | .shr => guardShr32 false a b
      | _ => .error "operator outside generate integer guards"
  | .resize _ a | .signedResize _ a | .squash2 _ a | .cast _ a => evalGenGuard32 env a
  | .sysCall .clog2 a => do
      let ty ← ctype env a
      let v ← evalAt env ty a
      let u := v.emod ((2 : Int) ^ ty.1)
      .ok (guard32 (clog2 u.toNat : Int))
  | _ => .error "expression outside generate integer guards"

/-! A generate condition is a constant expression, so its operands retain
their IEEE self-determined widths.  The legacy 32-bit guard above remains the
fallback for the small integer-guard vocabulary whose `ctype` is deliberately
structural (bitwise forms, for example).  Typed parameters and localparams
whose comparison width exceeds 32 bits must go through `evalAt`; forcing them
through `guard32` changes the selected generate branch (`fold_cgrow`, where
`U` is 33 or 40 bits). -/
def evalGenGuard (env : IEnv) (e : PExpr) : Except String Int :=
  if !env.stale.isEmpty && e.mentionsAny env.stale then
    .error "Constant:override-type — generate condition depends on an overridden untyped parameter"
  else match ctype env e with
  | .ok ty =>
      match evalAt env ty e with
      | .ok v => .ok v
      | .error _ => evalGenGuard32 env e
  | .error _ => evalGenGuard32 env e

#guard (match evalGenGuard { nvals := [("N", (16, 32, true))] } (.paramRef "N" none) with
  | .ok 16 => true | _ => false)
#guard (match evalGenGuard { nvals := [("N", (5, 32, true))] }
    (.binary (.m0 .and)
      (.binary (.m0 .sub) (.paramRef "N" none) (.int 6)) (.int 1)) with
  | .ok 1 => true | _ => false)

-- A typed parameter keeps its own width in a generate comparison.  In
-- particular, 33-bit `U = 2^32` is greater than 5 and `U + 1 == 1` is false;
-- evaluating either guard as a signed 32-bit integer selects the wrong branch.
private def wideGenerateEnv : IEnv :=
  { nvals := [("U", (4294967296, 33, false))] }
#guard (evalGenGuard wideGenerateEnv
    (.binary (.m0 .gt) (.paramRef "U" none) (.int 5))).toOption == some 1
#guard (evalGenGuard wideGenerateEnv
    (.binary (.m0 .eq)
      (.binary (.m0 .add) (.paramRef "U" none) (.int 1)) (.int 1))).toOption == some 0

private def staleGenerateEnv : IEnv :=
  { nvals := [("L", (4294967295, 32, false))], stale := ["L"] }
#guard (evalGenGuard staleGenerateEnv (.paramRef "L" none) matches .error _)

/-! ## Widths -/

/-- Width of one packed dimension: `|msb - lsb| + 1`. -/
def PDim.width (env : IEnv) (d : PDim) : Except String Nat := do
  let m ← evalInt env d.msb
  let l ← evalInt env d.lsb
  .ok ((m - l).natAbs + 1)

private def dimsWidth (env : IEnv) : List PDim → Except String Nat
  | [] => .ok 1
  | d :: rest => do
      let w ← d.width env
      let ws ← dimsWidth env rest
      .ok (w * ws)

/-- Instantiated bit width of a declared type (multi-dim packed = product
— a packed array is one bit vector at M0 level). -/
def PType.width (env : IEnv) : PType → Except String Nat
  | .packed dims _ => dimsWidth env dims
  | .typeRef n pkg _ =>
      match env.enumWidth n pkg with
      | some w => .ok w
      | none => .error s!"unknown type '{n}'"
  | .unrecoverable _ => .error "unrecoverable packed dimensions"

/-! ### Package constants -/

private def packageDimsWidth (env : IEnv) : List PDim → Except String Nat
  | [] => .ok 1
  | d :: rest => do
      let m ← evalInt env d.msb
      let l ← evalInt env d.lsb
      let w ← packageDimsWidth env rest
      .ok (((m - l).natAbs + 1) * w)

/-- **The value of a package constant** (§6.20.2, §6.20.4), four-state, at its
declared width and signedness; an untyped one takes its initializer's type. -/
def packageConstValue (env : IEnv) (p : PParam) : Except String (LVec × Nat × Bool) :=
  match p.default? with
  | none => .error "it has no default"
  | some e0 => do
      let e ← constCalls env e0 true
      match p.type? with
      | none =>
          if e.hasConvertedPart then .error convertedPartMsg
          else do
            let (w, s) ← ctype env e
            let v ← evalVec env true (w, s) e
            .ok (v, w, s)
      | some (.packed dims _) => do
          let w ← packageDimsWidth env dims
          let v ← assignVec env true w e
          .ok (v, w, p.signed?.getD (w == 32))
      | some (.typeRef _ _ (some w)) => do
          let v ← assignVec env true w e
          .ok (v, w, p.signed?.getD (w == 32))
      | some (.typeRef _ _ none) | some (.unrecoverable _) =>
          .error "ParamRef:package: its type is not retained"

/-- Bind a package constant: its four-state value always; its integer view
(`packageVals` for a 32-bit signed one, `packageNvals` otherwise) when every
bit is known. -/
def IEnv.bindPackageConst (env : IEnv) (pkg n : String) (v : LVec) (w : Nat) (s : Bool) : IEnv :=
  let env' := env.bindPackageFVal pkg n v w s
  match v.toNat? with
  | none => env'
  | some k =>
      let c := canonInt w s k
      if w == 32 && s then env'.bindPackageVal pkg n c else env'.bindPackageNVal pkg n c w s

private def packageAggIndices (env : IEnv) (msb lsb : PExpr) : Except String (Int × Int) := do
  pure (← evalInt env msb, ← evalInt env lsb)

private def packageAggElement (env : IEnv) (row : List (String × PExpr)) : Except String LVec := do
  let values ← evalPartList env true (← (row.map (·.2)).mapM fun e => constCalls env e true)
  if values.isEmpty then
    .error "package aggregate struct pattern has no fields"
  else
    .ok (LVec.concatMany values.toArray)

private def bindPackageAggregate (env : IEnv) (pkg : String) (p : PParam) : Except String IEnv :=
  match p.aggregate?, p.aggregateDefault? with
  | some (.array msb lsb elem), some rows => do
      let _ := elem
      let (m, l) ← packageAggIndices env msb lsb
      let expected := (m - l).natAbs + 1
      if rows.length != expected then
        .error "assignment pattern array count mismatch"
      else do
        let values ← rows.mapM (packageAggElement env)
        .ok (env.bindPackageAgg pkg p.name { msb := m, lsb := l, elements := values })
  | some _, _ => .error "aggregate default shape is unsupported"
  | none, _ => .error "aggregate metadata is missing"

/-- **Every package constant the value of `p` reads**: the references of its
initializer and of its type, and those of every function the initializer
calls, directly or not. -/
def packageParamDeps (fs : List PFunction) (p : PParam) : List (String × String) :=
  let ds := (match p.default? with | some e => e.constDeps | none => []) ++
    (match p.type? with | some ty => ty.constDeps | none => []) ++
    (match p.aggregateDefault? with
     | some rows => rows.flatMap fun row => row.flatMap fun (_, e) => e.constDeps
     | none => [])
  let all := ds ++ fnConstDepsAt fs fs.length (ds.filterMap fun
    | .call m => some m
    | .const .. | .param _ => none)
  all.filterMap fun
    | .const pkg n => some (pkg, n)
    | .call _ | .param _ => none

/-- The package binder's state: the environment, the constants already
decided, and the ones refused with their reasons (most recent first). -/
structure PkgState where
  env : IEnv
  done : List (String × String) := []
  refused : List ((String × String) × String) := []

/-- Decide one package constant, if every constant it reads is decided:
bind its value, or record why it is not bound.  `none` defers it. -/
def PkgState.step (known : List (String × String)) (st : PkgState) (pkg : String)
    (p : PParam) : Option PkgState :=
  let key := (pkg, p.name)
  let deps := packageParamDeps st.env.functions p
  if !(deps.all fun d => !known.contains d || st.done.contains d) then none
  else
    let refuse (msg : String) : PkgState :=
      { st with done := key :: st.done, refused := (key, msg) :: st.refused }
    if p.isString then some { st with done := key :: st.done }
    else
      match p.unsupported? with
      | some msg => some (refuse msg)
      | none =>
          match deps.find? (fun d => (st.refused.lookup d).isSome) with
          | some (q, m) => some (refuse s!"it reads '{q}::{m}', which is not bound")
          | none =>
              if p.aggregate?.isSome then
                match bindPackageAggregate st.env pkg p with
                | .ok env' => some { st with env := env', done := key :: st.done }
                | .error msg => some (refuse msg)
              else
                match packageConstValue st.env p with
                | .ok (v, w, s) =>
                    some { st with env := st.env.bindPackageConst pkg p.name v w s,
                                   done := key :: st.done }
                | .error msg => some (refuse msg)

/-- One pass in declaration order; the environment grows within the pass. -/
def pkgRound (known : List (String × String)) :
    PkgState → List (String × PParam) → PkgState × List (String × PParam)
  | st, [] => (st, [])
  | st, (pkg, p) :: rest =>
      match st.step known pkg p with
      | some st' => pkgRound known st' rest
      | none =>
          let (st', deferred) := pkgRound known st rest
          (st', (pkg, p) :: deferred)

/-- The constants of a dependency cycle are refused (§6.20.2: a parameter
cannot be defined in terms of itself). -/
def pkgCycle (st : PkgState) (rest : List (String × PParam)) : PkgState :=
  let names := ", ".intercalate (rest.map fun (pkg, p) => s!"{pkg}::{p.name}")
  rest.foldl (fun st (pkg, p) =>
    { st with done := (pkg, p.name) :: st.done,
              refused := ((pkg, p.name), s!"package constant dependency cycle among: {names}")
                :: st.refused }) st

/-- **Bind the package constants in dependency order.**  Each pass decides
every constant whose dependencies are decided; a pass that decides none has
found a cycle.  The count is the number of constants still undecided, which
every other pass lowers, so it never runs out first. -/
def pkgRounds (known : List (String × String)) :
    Nat → PkgState → List (String × PParam) → PkgState
  | _, st, [] => st
  | 0, st, rest => pkgCycle st rest
  | n + 1, st, rest =>
      let (st', deferred) := pkgRound known st rest
      if deferred.length == rest.length then pkgCycle st' deferred
      else pkgRounds known n st' deferred

def bindPackageParamsState (env : IEnv) (ps : List (String × PParam)) : PkgState :=
  pkgRounds (ps.map fun (pkg, p) => (pkg, p.name)) ps.length { env := env } ps

/-- Bind the package constants (elaboration constants, never override
binders).  A constant that cannot be evaluated is left unbound, so that only
a design that reads it is refused (`packageParamRefusals` lists the reasons).
A module without package parameters needs no pass: the clocked instantiation
tactic uses that equation when it unfolds the public binder. -/
def bindPackageParams (env : IEnv) : List (String × PParam) → Res IEnv
  | [] => .ok env
  | ps@(_ :: _) => .ok (bindPackageParamsState env ps).env

-- The symbolic parameter stage reduces this case with an open environment.
example (env : IEnv) : bindPackageParams env [] = .ok env := by rfl

/-- Why each unbound package constant is unbound, in declaration order of
the decisions. -/
def packageParamRefusals (env : IEnv) (ps : List (String × PParam)) : List String :=
  (bindPackageParamsState env ps).refused.reverse.map fun ((pkg, n), m) =>
    s!"package parameter '{pkg}::{n}' is not bound: {m}"

/-! ## Value tier: self-determined widths and `instExpr` -/

private def maxW : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

@[simp] theorem maxW_some (left right : Nat) :
    maxW (some left) (some right) = some (max left right) := rfl

mutual
/-- Self-determined width of a value-position expression (LRM §11.6
restricted to this vocabulary), under the instantiated declaration
widths. `none` = context-determined or unknowable. -/
def selfWidth (env : IEnv) : PExpr → Option Nat
  | .lit v => some v.width
  | .ident n => env.widths.lookup n
  | .paramRef .. | .genvarRef _ | .int _ | .sysCall .. => some 32
  | .typeBits _ _ => some 32
  | .enumRef ty _ pkg => env.enumWidth ty pkg
  | .fill _ => none
  | .unary op a =>
      match op with
      | .m0 .lnot => some 1
      | .m0 _ | .plus => selfWidth env a
      | .inc | .dec => none
  | .binary op l r =>
      match op with
      | .m0 .eq | .m0 .ne | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
      | .m0 .wildEq | .m0 .wildNe
      | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge
      | .slt | .sle | .sgt | .sge | .ceq | .cne | .land | .lor => some 1
      | .shl | .shr | .ashl | .ashr | .pow => selfWidth env l
      | .m0 (.pow ..) | .m0 (.shl ..) | .m0 (.shr ..)
      | .m0 (.ashl ..) | .m0 (.ashr ..) => divOperandWidth env l
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem | .div | .mod =>
          maxW (divOperandWidth env l) (divOperandWidth env r)
      | _ => maxW (selfWidth env l) (selfWidth env r)
  | .ternary _ t e => maxW (selfWidth env t) (selfWidth env e)
  | .concat parts => selfWidthSum env parts
  | .resize w _ | .signedResize w _ => some w
  | .squash2 w _ => some w
  | .functionCall .. => none
  -- Semantic-tier nodes: the M0 layer does not know element widths
  -- (`Param2.lean`'s `selfWidth2` does); `none` = unknowable here.
  | .bitSel .. | .partSel .. | .repl .. | .arrayElem .. | .arrayPart ..
  | .aggregateMember .. | .packageAggElem .. => none
  | .reduce .. => some 1
  | .cast _ a => selfWidth env a
  | .unsupported .. => none

def selfWidthSum (env : IEnv) : List PExpr → Option Nat
  | [] => some 0
  | p :: rest =>
      match selfWidth env p, selfWidthSum env rest with
      | some a, some b => some (a + b)
      | _, _ => none

def divOperandWidth (env : IEnv) : PExpr → Option Nat
  | .resize _ operand | .signedResize _ operand => divOperandWidth env operand
  | .lit value => some value.width
  | .ident name => env.widths.lookup name
  | .paramRef name none => some ((env.pwidths.lookup name).getD 32)
  | .paramRef name (some pkg) => (env.packageConstType pkg name).map Prod.fst
  | .genvarRef _ | .int _ | .sysCall .. => some 32
  | .typeBits _ _ => some 32
  | .enumRef name _ pkg => env.enumWidth name pkg
  | .fill _ => none
  | .unary (.m0 .lnot) _ => some 1
  | .unary (.m0 _) operand | .unary .plus operand => divOperandWidth env operand
  | .unary _ _ => none
  | .binary operator left right =>
      match operator with
      | .m0 .eq | .m0 .ne | .m0 .wildEq | .m0 .wildNe
      | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
      | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge
      | .slt | .sle | .sgt | .sge | .ceq | .cne | .land | .lor => some 1
      | .shl | .shr | .ashl | .ashr | .pow => divOperandWidth env left
      | .m0 (.pow ..) | .m0 (.shl ..) | .m0 (.shr ..)
      | .m0 (.ashl ..) | .m0 (.ashr ..) => divOperandWidth env left
      | _ => maxW (divOperandWidth env left) (divOperandWidth env right)
  | .ternary _ left right => maxW (divOperandWidth env left) (divOperandWidth env right)
  | .concat parts => divOperandWidthSum env parts
  | .squash2 width _ => some width
  | .reduce .. => some 1
  | .cast _ operand => divOperandWidth env operand
  | .bitSel .. | .partSel .. | .repl .. | .arrayElem .. | .arrayPart ..
  | .aggregateMember .. | .packageAggElem ..
  | .functionCall ..
  | .unsupported .. => none

def divOperandWidthSum (env : IEnv) : List PExpr → Option Nat
  | [] => some 0
  | operand :: rest =>
      match divOperandWidth env operand, divOperandWidthSum env rest with
      | some left, some right => some (left + right)
      | _, _ => none
end

def fitDivOperand (signed : Bool) (context sourceWidth : Option Nat) (operand : Expr) : Expr :=
  match context, sourceWidth with
  | some target, some source =>
      if target == source then operand
      else if signed then .resizeSigned target operand
      else if source < target then .concat #[.lit (.replicate (target - source) .l0), operand]
      else .unsupported "Division:operand-width" s!"{source} -> {target}"
  | _, _ => operand

/-- An integer constant materialized at the context width (32 — the SV
int width — when no context width is known). -/
private def intLit (ctx : Option Nat) (v : Int) : Expr :=
  .lit (LVec.ofInt (ctx.getD 32) v)

mutual
/-- Instantiate a value-position expression to an M0 `Expr` under context
width `ctx` (the module docstring's ledger). Total: every failure is a
loud `Expr.unsupported`, reached-sensitive exactly like extractor-emitted
ones. -/
def instExpr (env : IEnv) (ctx : Option Nat) : PExpr → Expr
  | .lit v => .lit v
  | .ident n => .ident n
  | .int v => intLit ctx v
  | .typeBits _ width => intLit ctx width
  | .fill b =>
      match ctx with
      | some w => .lit (LVec.replicate w b)
      | none => .unsupported "Fill:width" "no context width for unbased-unsized literal"
  | .paramRef n none =>
      match env.vals.lookup n with
      | some v => intLit ctx v
      | none =>
          match env.nvals.lookup n with
          | some (v, _, _) =>
              -- A stale constant (`IEnv.stale`, Param2's `instExpr2` twin).
              if env.stale.contains n then
                .unsupported "ParamRef:override-type" s!"'{n}': typed at its default"
              else intLit ctx v
          | none => .unsupported "ParamRef:unbound" n
  | .paramRef n (some p) =>
      match env.packageFVal p n with
      | some (v, w, s) =>
          match ctx with
          | none => .lit v
          | some target => fitDivOperand s (some target) (some w) (.lit v)
      | none =>
          match env.packageVal p n with
          | some v => intLit ctx v
          | none =>
              match env.packageNVal p n with
              | some (v, w, _) => intLit (some (ctx.getD w)) v
              | none => .unsupported "ParamRef:package" s!"{p}::{n}"
  | .genvarRef n =>
      match env.vals.lookup n with
      | some v => intLit ctx v
      | none => .unsupported "GenvarRef:unbound" n
  | .enumRef ty mem pkg =>
      match env.enumMember ty mem pkg with
      | some v => .lit v
      | none => .unsupported "EnumRef:unknown" s!"{ty}::{mem}"
  | .unary op a =>
      match op with
      | .m0 .lnot => .unary .lnot (instExpr env none a)
      | .m0 uop => .unary uop (instExpr env (maxW ctx (selfWidth env a)) a)
      | .plus => .unary .pos (instExpr env (maxW ctx (selfWidth env a)) a)
      | .inc | .dec => .unsupported "UnaryExpression:incdec" ""
  | .binary op l r =>
      match op with
      | .m0 (.pow signedBase signedExponent) =>
          let baseContext := maxW ctx (divOperandWidth env l)
          .binary (.pow signedBase signedExponent)
            (instDivOperand env signedBase baseContext l)
            (instDivOperand env signedExponent (divOperandWidth env r) r)
      | .m0 operator@(.shl signedLeft) | .m0 operator@(.shr signedLeft)
      | .m0 operator@(.ashl signedLeft) | .m0 operator@(.ashr signedLeft) =>
          let leftContext := maxW ctx (divOperandWidth env l)
          .binary operator (instDivOperand env signedLeft leftContext l)
            (instDivOperand env false (divOperandWidth env r) r)
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem =>
          let octx := maxW ctx (maxW (divOperandWidth env l) (divOperandWidth env r))
          .binary (match op with
            | .m0 .sdiv => .sdiv
            | .m0 .srem => .srem
            | .m0 .rem => .rem
            | _ => .div)
            (instDivOperand env (op == .m0 .sdiv || op == .m0 .srem) octx l)
            (instDivOperand env (op == .m0 .sdiv || op == .m0 .srem) octx r)
      | .m0 .add | .m0 .sub | .m0 .and | .m0 .or | .m0 .xor =>
          let octx := match ctx with
            | some w => some w
            | none => maxW (selfWidth env l) (selfWidth env r)
          .binary (match op with
              | .m0 bop => bop
              | _ => .add)  -- unreachable: this arm only matches `.m0`
            (instExpr env octx l) (instExpr env octx r)
      | .m0 .eq | .m0 .ne | .m0 .wildEq | .m0 .wildNe
      | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
      | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge =>
          let octx := maxW (selfWidth env l) (selfWidth env r)
          .binary (match op with
              | .m0 bop => bop
              | _ => .eq)  -- unreachable
            (instExpr env octx l) (instExpr env octx r)
      | .land | .lor =>
          .binary (if op == .land then .land else .lor)
            (instExpr env (selfWidth env l) l)
            (instExpr env (selfWidth env r) r)
      | _ =>
          match evalInt env (.binary op l r) with
          | .ok v => intLit ctx v
          | .error e =>
              match op with
              | .m0 .mul | .mul =>
                  let octx := maxW ctx (maxW (selfWidth env l) (selfWidth env r))
                  .binary .mul (instExpr env octx l) (instExpr env octx r)
              | _ => .unsupported s!"BinaryExpression:{op.sym}" e
  | .ternary c t e =>
      let actx := match ctx with
        | some w => some w
        | none => maxW (selfWidth env t) (selfWidth env e)
      .ternary (instExpr env none c) (instExpr env actx t) (instExpr env actx e)
  | .concat parts => .concat (instParts env parts).toArray
  | .resize w a =>
      if ctx.getD w != w then
        .unsupported "Resize:context"
          s!"default-elaborated resize width {w} vs context width {ctx.getD w}"
      else
        match selfWidth env a with
        | none => .unsupported "Resize:width" "operand width unknown"
        | some ow =>
            if ow == w then instExpr env (some w) a
            else if ow < w then
              .concat #[.lit (LVec.replicate (w - ow) .l0), instExpr env (some ow) a]
            else .unsupported "Resize:truncate" s!"{ow} -> {w}"
  | .squash2 .. => .unsupported "Squash2" "2-state squash outside the M0 value core"
  | .signedResize width operand =>
      .resizeSigned (ctx.getD width) (instExpr env (selfWidth env operand) operand)
  | .sysCall fn a =>
      match evalInt env (.sysCall fn a) with
      | .ok v => intLit ctx v
      | .error e => .unsupported "SysCall" e
  -- Semantic-tier nodes stay loud on the M0 path (they lower in
  -- `Param2.lean`'s `instantiate2` → `Design2`).
  | .bitSel .. => .unsupported "T2:BitSel" "select outside the M0 tier"
  | .partSel .. => .unsupported "T2:PartSel" "select outside the M0 tier"
  | .repl .. => .unsupported "T2:Repl" "replication outside the M0 tier"
  | .reduce .. => .unsupported "T2:Reduce" "reduction outside the M0 tier"
  -- A signed literal (`4'sd3`: `Ingest2` reads it as `cast true (lit)`) is
  -- its bits; signedness acts through the operators the extractor spelled.
  | .cast _ (.lit v) => .lit v
  | .cast .. => .unsupported "T2:Cast" "cast outside the M0 tier"
  | .arrayElem .. | .arrayPart .. =>
      .unsupported "T2:ArraySel" "packed-array select path outside the M0 tier"
  | .aggregateMember .. =>
      .unsupported "MemberAccessExpression:aggregate"
        "source-shaped aggregate member path requires the E aggregate store"
  | .packageAggElem pkg n _ =>
      .unsupported "ParamRef:package-aggregate" s!"{pkg}::{n} outside the E aggregate route"
  | .functionCall n _ => .unsupported "CallExpression:user-function" s!"function '{n}' outside the M0 tier"
  | .unsupported k t => .unsupported k t

/-- Concat parts: each part is self-determined (an inner fill with no
self width is loud — the LRM agrees: unsized literals are illegal in
concats). -/
def instParts (env : IEnv) : List PExpr → List Expr
  | [] => []
  | p :: rest => instExpr env (selfWidth env p) p :: instParts env rest

def instDivOperand (env : IEnv) (signed : Bool) (ctx : Option Nat) : PExpr → Expr
  | .unary (.m0 .lnot) operand =>
      fitDivOperand signed ctx (some 1)
        (.unary .lnot (instDivOperand env false (divOperandWidth env operand) operand))
  | .unary (.m0 operator) operand =>
      .unary operator (instDivOperand env signed (maxW ctx (divOperandWidth env operand)) operand)
  | .unary .plus operand =>
      .unary .pos (instDivOperand env signed (maxW ctx (divOperandWidth env operand)) operand)
  | .binary (.m0 (.pow _ signedExponent)) left right =>
      .binary (.pow signed signedExponent)
        (instDivOperand env signed (maxW ctx (divOperandWidth env left)) left)
        (instDivOperand env signedExponent (divOperandWidth env right) right)
  | .binary (.m0 operator@(.shl _)) left right
  | .binary (.m0 operator@(.shr _)) left right
  | .binary (.m0 operator@(.ashl _)) left right
  | .binary (.m0 operator@(.ashr _)) left right =>
      let shifted := match operator with | .ashr _ => .ashr signed | _ => operator
      .binary shifted
        (instDivOperand env signed (maxW ctx (divOperandWidth env left)) left)
        (instDivOperand env false (divOperandWidth env right) right)
  | .binary (.m0 operator) left right =>
      let own := maxW (divOperandWidth env left) (divOperandWidth env right)
      let comparison := match operator with
        | .eq | .ne | .wildEq | .wildNe | .lt | .le | .gt | .ge => true
        | _ => false
      let common := if comparison then own else maxW ctx own
      let value := Expr.binary operator
        (instDivOperand env signed common left) (instDivOperand env signed common right)
      if comparison then fitDivOperand signed ctx (some 1) value else value
  | .binary .mul left right =>
      let common := maxW ctx (maxW (divOperandWidth env left) (divOperandWidth env right))
      .binary .mul (instDivOperand env signed common left) (instDivOperand env signed common right)
  | .resize width operand => instDivOperand env false (ctx.orElse (fun _ => some width)) operand
  | .signedResize width operand => instDivOperand env true (ctx.orElse (fun _ => some width)) operand
  | .ternary condition left right =>
      let common := maxW ctx (maxW (divOperandWidth env left) (divOperandWidth env right))
      .ternary (instDivOperand env false (divOperandWidth env condition) condition)
        (instDivOperand env signed common left) (instDivOperand env signed common right)
  | .concat parts =>
      fitDivOperand signed ctx (divOperandWidthSum env parts)
        (.concat (instDivParts env parts).toArray)
  | operand =>
      let source := divOperandWidth env operand
      fitDivOperand signed ctx source (instExpr env (source.orElse (fun _ => ctx)) operand)

def instDivParts (env : IEnv) : List PExpr → List Expr
  | [] => []
  | operand :: rest =>
      instDivOperand env false (divOperandWidth env operand) operand :: instDivParts env rest
end

/-! ## Statements, processes, declarations -/

mutual
/-- Instantiate a statement (assign targets take their declared widths as
context). -/
def instStmt (env : IEnv) : PStmt → Stmt
  | .localDecl _ _ _ => .unsupported "LocalDecl" "static procedural declaration is retained for the memory route"
  | .automaticDecl _ _ _ => .unsupported "LocalDecl" "automatic procedural declaration is retained for the memory route"
  | .blockingAssign t v => .blockingAssign t (instExpr env (env.widths.lookup t) v)
  | .nbaAssign t v => .nbaAssign t (instExpr env (env.widths.lookup t) v)
  | .ifStmt c th el =>
      .ifStmt (instExpr env none c) (instStmt env th)
        (match el with
         | some s => some (instStmt env s)
         | none => none)
  | .block body => .block (instStmts env body).toArray
  | .forLoop .. => .unsupported "T2:ForLoop" "parameter-dependent loop is semantic-tier only"
  | .blockingAssignL .. => .unsupported "T2:AssignL" "select target outside the M0 tier"
  | .nbaAssignL .. => .unsupported "T2:AssignL" "select target outside the M0 tier"
  | .caseStmt .. => .unsupported "T2:Case" "case statement outside the M0 tier"
  | .unsupported k t => .unsupported k t

def instStmts (env : IEnv) : List PStmt → List Stmt
  | [] => []
  | s :: rest => instStmt env s :: instStmts env rest
end

/-- Instantiate a process. -/
def instProcess (env : IEnv) : PProcess → Process
  | .alwaysFF c b => .alwaysFF c (instStmt env b)
  | .alwaysFFNegedge _ _ => .unsupported "AlwaysPosedge:edge"
      "edge-qualified clock requires its retained event semantics"
  | .alwaysPlain c b => .alwaysPlain c (instStmt env b)
  | .alwaysComb b => .alwaysComb (instStmt env b)
  | .alwaysLatch b => .unsupported "AlwaysLatch" "level-sensitive latch process is outside the scalar M0 tier"
  | .alwaysImplicit _ => .unsupported "ProceduralBlockSymbol:Always"
      "source-level event-controlled always is retained; the frozen process AST has no event-list constructor"
  | .alwaysEvent _ _ => .unsupported "ProceduralBlockSymbol:Always"
      "source-level event-controlled always is retained; the frozen process AST has no event-list constructor"
  | .assign t v => .assign t (instExpr env (env.widths.lookup t) v)
  | .assignL .. => .unsupported "T2:AssignL" "select target outside the M0 tier"
  | .alwaysFFR .. => .unsupported "T2:AlwaysFFR" "async reset outside the M0 tier"
  | .initial .. => .unsupported "T2:Initial" "initial process outside the M0 tier"
  | .unsupported k t => .unsupported k t

/-- Instantiate one declaration (earlier declarations' widths already in
`env` — `$bits`/`$high` may look back, never forward). A non-literal
initializer is outside the M0 ingestion tier (loud). -/
def instDecl (env : IEnv) (pd : PDecl) : Res Decl :=
  if !pd.unpackedDims.isEmpty || pd.isInout then
    .unsupported (if pd.isInout then
      s!"decl '{pd.name}': bidirectional inout net requires IEEE 1800-2023 §6.6 driver resolution (PortSymbol:InOut)"
      else s!"decl '{pd.name}': unpacked array storage outside E (UnpackedDecl:memory)")
  else match pd.type.width env with
  | .error e => .unsupported s!"decl '{pd.name}': {e}"
  | .ok w =>
      match pd.init with
      | none =>
          .ok { name := pd.name, width := w, isSigned := pd.isSigned,
                isNet := pd.isNet, twoState := pd.twoState,
                isInput := pd.isInput, isOutput := pd.isOutput }
      | some ie =>
          match instExpr env (some w) ie with
          | .lit v =>
              .ok { name := pd.name, width := w, isSigned := pd.isSigned,
                    isNet := pd.isNet, twoState := pd.twoState,
                    isInput := pd.isInput, isOutput := pd.isOutput, init := some v }
          | _ =>
              -- A constant expression such as `reg [1:0] r = -1` is
              -- evaluated by the declaration's context width (§6.8,
              -- §11.8).  Keep signal-dependent initializers loud, while
              -- admitting the exact INT-class constant path already used
              -- for parameters and localparams.
              match evalInt env ie with
              | .ok v =>
                  .ok { name := pd.name, width := w, isSigned := pd.isSigned,
                        isNet := pd.isNet, twoState := pd.twoState,
                        isInput := pd.isInput, isOutput := pd.isOutput,
                        init := some (LVec.ofInt w v) }
              | .error _ =>
                  .unsupported s!"decl '{pd.name}': non-literal initializer outside the M0 tier"

/-- Instantiate the declarations in order, threading each new width into
the environment. -/
def buildDecls (env : IEnv) : List PDecl → Res (List Decl)
  | [] => .ok []
  | pd :: rest => do
      let dc ← instDecl env pd
      let ds ← buildDecls { env with widths := (pd.name, dc.width) :: env.widths } rest
      .ok (dc :: ds)

/-- Whether every declared bound of a type is a literal, so that its width
is the same at every parameter point (round 5 folds, `declConstType`). -/
def PType.boundsLiteral : PType → Bool
  | .packed ds _ => ds.all fun d =>
      (match d.msb with | .int _ | .lit _ => true | _ => false) &&
      (match d.lsb with | .int _ | .lit _ => true | _ => false)
  | _ => true

/-- The constant-tier type of a declared parameter/localparam type:
`none` = the INT class (no type, or a 32-bit signed type — `int`,
`integer`), `some (w, s)` otherwise. `signed?` is the envelope's `signed`
field; absent, a type is signed exactly when it is 32 bits wide (the
extractor emits the field for every type departing from that default:
`int unsigned`, `logic [31:0]`, `byte`, …) — a rule about ONE width, so a
type with a non-literal bound (`logic signed [M-1:0]`) without the field is
loud (round 5 folds; the extractor always emits it for such a type). -/
def declConstType (env : IEnv) (ty? : Option PType) (signed? : Option Bool) :
    Except String (Option (Nat × Bool)) :=
  match ty? with
  -- No type and no range: the type of the final value — an integer override
  -- is an `int` (§6.20.2), unless an explicit `unsigned` keyword makes it
  -- 32-bit unsigned. (The default point is `PDesign.atPoint`'s.)
  | none => .ok (if signed? == some false then some (32, false) else none)
  -- An enum-typed parameter holds a member value; enum tables bind after the
  -- parameters (`bindEnums`), so it keeps the INT reading it always had.
  | some (.typeRef ..) => .ok none
  | some ty => do
      let w ← ty.width env
      let s ← match signed? with
        | some s => pure s
        | none =>
            -- Round 5 folds (verifier repros `vq_sgn2`, `vq_sgn3`): the
            -- default rule is a fact of ONE width; a type whose width
            -- depends on a parameter must say (the extractor always emits
            -- the field for one, `_sym_param_signedness`).
            if ty.boundsLiteral then pure (w == 32)
            else throw "a parameter-dependent type without its declared signedness (envelope `signed`): the default rule (signed exactly when 32 bits wide) would be read at this point's width"
      .ok (if w == 32 && s then none else some (w, s))

/-- A literal dimension bound (`PDim` as the extractor writes `[7:4]`). -/
def PExpr.isLitBound : PExpr → Bool
  | .int _ | .lit _ => true
  | _ => false

/-- `IEnv.pdims` after binding the typed constant `n` of type `ty?`: its
evaluated range when some declared bound is not a literal (round 3 folds,
`paramSelectOk`); `env` unchanged otherwise (literal bounds, a `typeRef`,
no type, or bounds that do not evaluate — the width computation that
typed the constant has already reported those). -/
def IEnv.withPDims (env : IEnv) (n : String) (ty? : Option PType) : IEnv :=
  match ty? with
  | some (.packed ds _) =>
      if ds.all (fun d => d.msb.isLitBound && d.lsb.isLitBound) then env
      else
        match ds.mapM (fun d => do pure ((← evalInt env d.msb), (← evalInt env d.lsb))) with
        | .ok es => { env with pdims := (n, es) :: env.pdims }
        | .error _ => env
  | _ => env

/-- Bind module parameters to their argument values in declaration order
(each type sees the earlier parameters): INT-class parameters append to
`vals` (so a parameter list of INT parameters binds exactly
`(names).zip args`), every other typed parameter goes to `nvals` with its
value converted to the declared type (`canonInt` — what SV does with an
override that does not fit). -/
def bindParams (env : IEnv) : List PParam → List Int → Except String IEnv
  | p :: ps, v :: vs =>
      if p.isString then
        let width := match p.default? with
          | some (.lit value) => value.width
          | _ => 0
        if width == 0 then
          .error s!"string parameter '{p.name}' has no retained literal width"
        else
          bindParams (env.bindStringVal p.name (LVec.ofInt width v)) ps vs
      else do
        if p.type?.isNone && p.signed? == some false then
          throw "Constant:untyped-unsigned — IEEE 1800-2023 §6.20.2 leaves unsigned no-range parameters implementation-defined"
        if p.hasAggregateDefault env then
          -- An aggregate parameter is not an integer binder.  Preserve its
          -- absence from the integer environment so a forwarded reference
          -- remains parser-shaped and direct use fails loudly downstream.
          bindParams { env with stale := p.name :: env.stale } ps vs
        else
        match ← (declConstType env p.type? p.signed?).mapError
            (fun e => s!"parameter '{p.name}' type: {e}") with
        | none =>
            if p.overrideRetypes then
              bindParams { env.bindNVal p.name (canonInt 32 true v) 32 true with
                stale := p.name :: env.stale } ps vs
            else if env.int32 then
              bindParams (env.bindNVal p.name (canonInt 32 true v) 32 true) ps vs
            else bindParams { env with vals := env.vals ++ [(p.name, v)] } ps vs
        | some (w, s) =>
            if p.overrideRetypes then
              bindParams { (env.withPDims p.name p.type?).bindNVal p.name (canonInt w s v) w s with
                stale := p.name :: env.stale } ps vs
            else bindParams ((env.withPDims p.name p.type?).bindNVal p.name (canonInt w s v) w s) ps vs
  | _, _ => .ok env

/-- `bindParams` in `Res` (a failure is a loud `.unsupported`). -/
def bindParamsRes (env : IEnv) (ps : List PParam) (args : List Int) : Res IEnv :=
  match bindParams env ps args with
  | .ok e => .ok e
  | .error e => .unsupported e

/-! ### §6.20.2 at the default point

`instantiate`/`instantiate2` read every argument as an integer OVERRIDE
(`#(.P(5))`), and an untyped parameter takes the type of its FINAL value
(IEEE 1800-2023 §6.20.2) — at an overridden point that is the override's
type, an `int`, which is what `bindParams` binds. At a point where the
parameter is NOT overridden its final value is its default, so its type is
the default expression's: `parameter P = 3'd5` is 3-bit unsigned there and
`v[P + 3'd4 +: 2]` wraps to `v[2:1]` in every simulator (verifier finding
2026-10-28). `PDesign.atPoint` models such a point by RETYPING the
not-overridden parameters (`PParam.retype`) before instantiation; the
load-time gate (`crossCheck`) and the differential runner instantiate
through it. -/

/-- `e` with every shift (`<< >> <<< >>>`) on its context-propagation chain
read at its OWN type (a `.cast` of its own signedness): the wide reading of
`evalUntyped` (round 5). Icarus 12.0's lossless evaluation of an untyped
parameter value stops at a shift (measured: `(SB + 1'b1) >> 1`, `(SB +
1'b1) << 1`, `SB << 4` and `(SB * SB) >> 8` keep their own 8 bits there,
while `+ - * / **`, unary `-` and the arms of `?:` widen), and
comparisons, logical operators, casts and selects are self-determined in
`evalAt` already. Round 7 folds: that holds for a RIGHT shift and for a
SIZED left operand only; a LEFT shift whose left operand is or contains an
unsized or INT-class operand widens in Icarus (`1 << N` is 32 + N bits,
2^40 at `N = 40`), so `PExpr.icarusWidens` refuses every left shift before
`evalUntyped` reaches this reading. -/
def PExpr.shiftBarriers (env : IEnv) : PExpr → PExpr
  | .unary op a => .unary op (a.shiftBarriers env)
  | .binary op l r =>
      match op with
      | .shl | .shr | .ashl | .ashr =>
          match ctype env l with
          | .ok (_, s) => .cast s (.binary op l r)
          | .error _ => .binary op l r
      | .pow => .binary op (l.shiftBarriers env) r
      | _ =>
          match op.constClass with
          | .arith => .binary op (l.shiftBarriers env) (r.shiftBarriers env)
          | _ => .binary op l r
  | .ternary c t e => .ternary c (t.shiftBarriers env) (e.shiftBarriers env)
  | .resize w a => .resize w (a.shiftBarriers env)
  | .signedResize w a => .signedResize w (a.shiftBarriers env)
  | .squash2 w a => .squash2 w (a.shiftBarriers env)
  | e => e

/-- The refusal of an untyped constant whose self-determined value wraps
(`evalUntyped`). -/
def untypedWrapMsg (w : Nat) (v v' : Int) : String :=
  s!"Constant:untyped-overflow — an untyped parameter or localparam takes its expression's own type (IEEE 1800-2023 §6.20.2), {w} bits here, where its value is {v}; evaluated without that bound it is {v'}: slang, the LRM and Yosys 0.53 keep the {w}-bit value, Icarus 12.0 evaluates an untyped parameter value losslessly (measured: `SB + 1'b1` with an 8-bit SB = 255 is 0 against 256) — refused where the readings differ"

/-- **Whether Icarus 12.0 can give an untyped constant a WIDER type than its
own** (round 6 folds, round 5 FOLDS verifier major 3 and minor 4).
IEEE 1800-2023 §6.20.2 types an untyped parameter or localparam by its
expression (slang, Yosys 0.53: `$bits` of `SB + 1'b1` with an 8-bit `SB`
is 8, of `N + 1` with an `int N` 32); Icarus 12.0, in its default
`-gno-strict-expr-width` mode, gives it the LOSSLESS width of that
expression (measured with `$bits`, scratch `gaps5/folds/p/uw`): one carry
bit per `+` and `-` (`SB + 1'b1` 9, `N + 1` and `5 + 1` 33, `SB + 8'd0 -
8'd0` 10), the operand widths summed for `*` (`SB * 2'd2` 10, `N * 2`
64), a base- and value-dependent width for `**` (`SB ** 2` 16, `N ** 2`
64, `2'd2 ** SB` 2, `2 ** N` 32 at `N = 8` and 42 at `N = 40`), carried
through `/ % & | ^`, unary `- ~ +` and both arms of `?:` (`(N + 1) / 2`,
`M ? N : N + 1`: 33), and stopped by a RIGHT shift, a comparison, a
cast, a select and a concatenation part (`(N + 1) >> 1` 32, `$signed(N +
1)` 32, `{SB + 1'b1}` 8). Round 7 folds (round 6 FOLDS verifier blocker
3, scratch `gaps5/vfolds/w/w3.sv`, `w4.sv`): a LEFT shift is not a
barrier — Icarus widens `<<`/`<<<` by the shift amount where the left
operand is or contains an unsized or INT-class operand (`1 << N` 40 bits
at `N = 8` and 72 at `N = 40`, where the value is 2^40 and Yosys gives 0;
`1 << 3` 35, `7 << 1` 33, `(N | 1) << 2` 34, carried through `(1 << N) |
1` and `(1 << N) / 2`), so every left shift counts as widening, a sized
left operand included (`SB << 4` stays 8 bits in Icarus — a recorded
over-refusal). A wider type is observable wherever the constant's width
is: as a concatenation part (`{a, B}` with `localparam B = N + 1`: Icarus
`0x1e00000009`, Yosys `0xf00000009` at `a = 4'hF`; `{a, E}` with
`localparam E = 2 ** N` at `N = 40`, where the 32-bit materialization made
`int32Agrees` see no difference and the model followed Yosys), as a
negative operand zero-extended into a wider unsigned context (`a + B` with
`B = N - 9 = -1` into 64 bits: `0x200000002` against `0x100000002`), and
in a context it widens (`(Y + 8'd255) >> 1` into 8 bits with `Y = SB +
1'b1`, `SB = 5`: 130 against 2). `true` over-approximates: `+ - * **`
and a left shift anywhere on the expression's context chain (`2 ** N` is
32 bits in Icarus at `N = 8` and refused too — a recorded over-refusal;
the value-position spellings `u/`, `s%`, `u**u`, `u<<` count like `/ % **
<<`). -/
def PExpr.icarusWidens (env : IEnv) : PExpr → Bool
  | .binary op l r =>
      match op with
      | .m0 .add | .m0 .sub | .m0 .mul | .mul | .pow | .m0 (.pow ..) => true
      -- Round 7 folds: a LEFT shift widens (`1 << N` is 32 + N bits).
      | .shl | .ashl | .m0 (.shl _) | .m0 (.ashl _) => true
      | .m0 .and | .m0 .or | .m0 .xor | .div | .mod
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem => l.icarusWidens env || r.icarusWidens env
      | _ => false
  | .unary (.m0 .lnot) _ => false
  | .unary _ a => a.icarusWidens env
  | .ternary _ t e => t.icarusWidens env || e.icarusWidens env
  | .resize _ a | .signedResize _ a | .squash2 _ a => a.icarusWidens env
  | _ => false

/-- The refusal of an untyped constant that Icarus 12.0 types wider than
its own type (`evalUntyped`, `PExpr.icarusWidens`). -/
def untypedWidthMsg : String :=
  s!"Constant:untyped-width — an untyped parameter or localparam takes its expression's own type (IEEE 1800-2023 §6.20.2; slang, Yosys 0.53), while Icarus 12.0 gives it the lossless width of an expression built with + - * or ** ($bits of `SB + 1'b1` with an 8-bit SB is 9, of `N + 1` with an int N 33): the two are different constants wherever the width is observable (a concatenation part, a negative value extended into a wider unsigned context, a context it widens) — refused for every such untyped constant, at every point"

/-! The former implementation rejected expressions whose intermediate width
Icarus widened.  IEEE 1800-2023 §6.20.2 requires the final value's own type,
so that implementation-dependent refusal is retained only as a compatibility
reference below. -/
/-- **The value of an UNTYPED parameter default or localparam**.

IEEE 1800-2023 §6.20.2 gives an untyped parameter the type and range of its
final assigned value.  The expression is evaluated at its own §11.6/§11.8
type, including the 32-bit signed `int` type of an INT-class expression.
Xcelium is the oracle where Icarus' historical lossless-width mode differs. -/
def evalUntypedExact (env : IEnv) (e : PExpr) : Except String Int := do
  let ty ← ctype env e
  evalAt env ty e

/-! The former refusal boundary is retained verbatim as a reference.  It is
kept for audit comparisons only.  The exact §6.20.2 evaluator intentionally
changes old INT-class readings at the 32-bit boundary, so no unconditional
conservativity theorem is stated here.  For example, the old evaluator reads
`-2147483648 / -1` and a 33-bit INT-class literal differently from the exact
final-value evaluator required by §§6.20.2, 11.6, and 11.8. -/
def evalUntypedLegacy (env : IEnv) (e : PExpr) : Except String Int := do
  if e.icarusWidens env then throw untypedWidthMsg
  let v ← evalInt env e
  if e.isInt env then .ok v
  else
    let (w, s) ← ctype env e
    let v' ← evalAt env (w + 64, s) (e.shiftBarriers env)
    if v' == v then .ok v else .error (untypedWrapMsg w v v')

/-- Whether a constant tree contains a literal wider than the guaranteed
32-bit minimum for an unsized based literal (§5.7.1). The envelope does not
retain the source's sized/unsized spelling, so the conservative admission
boundary refuses every such literal rather than choosing a tool width. -/
def PExpr.hasWideLiteral : PExpr → Bool
  | .lit v => 32 < v.width
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => a.hasWideLiteral
  | .binary _ l r | .bitSel l r | .repl l r => l.hasWideLiteral || r.hasWideLiteral
  | .partSel b m l | .ternary b m l => b.hasWideLiteral || m.hasWideLiteral || l.hasWideLiteral
  | .concat _ | .arrayElem _ _ => false
  | .arrayPart _ _ _ a b => a.hasWideLiteral || b.hasWideLiteral
  | .functionCall _ _ => false
  | .aggregateMember .. | .packageAggElem .. | .ident _ | .genvarRef _ | .enumRef ..
  | .paramRef .. | .int _ | .fill _ | .typeBits .. | .unsupported .. => false

/-! Public untyped admission remains loud wherever the implementation-defined
width or an overridden type could change the result. The exact evaluator is
kept separately for cases whose source retains a portable final type. -/
def evalUntyped (env : IEnv) (e : PExpr) : Except String Int :=
  if !env.stale.isEmpty && e.mentionsAny env.stale then
    .error "Constant:override-type — constant expression depends on an overridden untyped parameter"
  else if e.hasWideLiteral then
    .error "Constant:untyped-width — unsized based literal wider than 32 bits has implementation-defined width (IEEE 1800-2023 §5.7.1)"
  else evalUntypedLegacy env e

/- The old and exact evaluators deliberately disagree on these boundary cases.
These rows make the dropped conservativity claim explicit while retaining the
old evaluator verbatim for audit comparison.  No unconditional theorem is
claimed because the INT-class 32-bit boundary changes the defined value. -/
#guard (match evalUntypedLegacy { vals := [("N", -2147483648)] }
    (.unary (.m0 .neg) (.paramRef "N" none)) with
  | .ok v => v == 2147483648
  | _ => false)
#guard (match evalUntypedExact { vals := [("N", -2147483648)] }
    (.unary (.m0 .neg) (.paramRef "N" none)) with
  | .ok v => v == -2147483648
  | _ => false)
#guard (match evalUntypedLegacy {} (.int 4294967296) with
  | .ok v => v == 4294967296
  | _ => false)
#guard (match evalUntypedExact {} (.int 4294967296) with
  | .ok v => v == 0
  | _ => false)

/- These are explicit regressions against the verbatim pre-exact evaluator.
   The INT-class expression is now evaluated at its required 32-bit signed
   type, so the old unbounded values at the 2^31/2^32 boundaries are not
   conservativity claims.  Keeping both sides here prevents the old result
   from being accidentally reintroduced while documenting the deliberate
   §6.20.2 change. -/
#guard (match evalUntypedLegacy { vals := [("N", 4294967296)] }
    (.binary .div (.paramRef "N" none) (.int 2)) with
  | .ok v => v == 2147483648
  | _ => false)
#guard (match evalUntypedExact { vals := [("N", 4294967296)] }
    (.binary .div (.paramRef "N" none) (.int 2)) with
  | .ok v => v == 0
  | _ => false)
#guard (match evalUntypedLegacy { vals := [("N", -2147483648)] }
    (.unary (.m0 .neg) (.paramRef "N" none)) with
  | .ok v => v == 2147483648
  | _ => false)
#guard (match evalUntypedExact { vals := [("N", -2147483648)] }
    (.unary (.m0 .neg) (.paramRef "N" none)) with
  | .ok v => v == -2147483648
  | _ => false)

/- Negative and oversized shifts in the historical untyped constant tier stay
   loud: their self-determined width is not fixed by a declared `int` target.
   This is the deliberate untyped-localparam boundary, while the exact `int`
   tier follows §11.4.10 with a 32-bit amount cap. -/
#guard (evalUntyped ({} : IEnv)
    (.binary .ashr (.int (-8)) (.int (-1)))) matches .error _
#guard (evalUntyped ({} : IEnv)
    (.binary .ashr (.int (-8)) (.int 40))) matches .error _
#guard (evalUntyped ({} : IEnv) (.lit (LVec.ofNat 33 1))) matches .error _

/-- **The initializer of an INT-class TARGET** (round 4 folds): an
`integer` or `int` localparam, or an `integer`/`int` parameter's default — an
assignment to a 32-bit signed target (§10.8, §11.8.1). An INT-class
initializer (or one under the `Squash2` of an `int` target) keeps
`evalInt`'s unbounded reading; any other is evaluated at `max(32, its own
width)` at THESE parameters (`evalAssign`), the caller converting to the
32-bit target. Before, such an initializer went through `evalInt`, i.e. at
its own width wherever the default point's tree held no conversion to read:
`localparam integer L = U + 1'b1` with `logic [N-1:0] U = -1` (32 bits at
the default `N = 32`) was 0 at `N = 4` and `N = 8`, where Icarus 12.0 and
the Yosys 0.53 netlist give 16 and 256 (round 3 FOLDS verifier, repros
`rf_int`, `rf_ipar` — a regression of round 3's transparent `ctype`). -/
def evalIntTarget (env : IEnv) (e : PExpr) : Except String Int :=
  if e.isInt env then
    -- An INT-class target is still a 32-bit signed expression context.  In
    -- int32 mode every intermediate arithmetic node must wrap before the
    -- parent consumes it (§11.4, §11.6.1, §11.8.1); the old unbounded path
    -- wrapped only the final localparam result.
    if env.int32 then evalIntExact env e else evalInt env e
  else
    match e with
    | .squash2 _ a =>
        if a.isInt env then
          if env.int32 then evalIntExact env a else evalInt env a
        else evalAssign env 32 e
    | _ => evalAssign env 32 e

/-- A parameter's DEFAULT value, before its conversion to the declared type
(round 3 folds): a typed parameter's non-INT default at its declared width
at THESE parameters (`evalAssign` — `parameter logic [N-1:0] Q = 8'd200 +
8'd100` is `300` at `N = 16`, where the envelope's default-point tree was
sized to `N = 4`; an `integer`/`int` one at 32 bits, `evalIntTarget`, round
4); an untyped default by `evalInt` (its own type, §6.20.2), loud where
that value wraps (`evalUntyped`, round 5). -/
def PParam.evalDefault (env : IEnv) (p : PParam) (e : PExpr) : Except String Int :=
  if p.isString then
    match e with
    | .lit value =>
        match value.toNat? with
        | some n => .ok n
        | none => .error "string parameter default contains x/z bits"
    | _ => .error "string parameter default is not a retained literal"
  else match p.type? with
  | some _ =>
      if e.isInt env then evalInt env e
      else do
        match ← declConstType env p.type? p.signed? with
        | some (w, _) => evalAssign env w e
        | none =>
            -- An enum-typed parameter (`declConstType` reads it as INT) keeps
            -- `evalInt`; an `integer`/`int` one is a 32-bit target.
            match p.type? with
            | some (.typeRef ..) => evalInt env e
            | _ => evalIntTarget env e
  | none => evalUntyped env e

/-- The constant type an UNTYPED parameter (`type? = none`) has when it is
NOT overridden: its default expression's self-determined type (`ctype`),
with a declared signing keyword (`signed?` — `parameter signed P = 4'd3`)
applied; `none` when that is the INT class (32-bit signed — `bindParams`'
reading already). Typed and ranged parameters keep their declared type at
every point (`none`). -/
def PParam.defaultConstType (env : IEnv) (p : PParam) :
    Except String (Option (Nat × Bool)) :=
  if p.isString then .ok none else match p.type?, p.default? with
  | none, some e =>
      if e.isInt env && p.signed? != some false then .ok none
      else do
        let (w, s) ← ctype env e
        let s := p.signed?.getD s
        -- The override reading (`declConstType none p.signed?`) already.
        if w == 32 && s == p.signed?.getD true then .ok none
        else .ok (some (w, s))
  | _, _ => .ok none

/-- `p` declared at the constant type `(w, s)`: a `[w-1:0]` packed type
with explicit signedness (`PDesign.atPoint`'s retyping). -/
def PParam.retype (p : PParam) (w : Nat) (s : Bool) : PParam :=
  { p with type? := some (.packed [⟨.int ((w : Int) - 1), .int 0⟩] (some w)),
           signed? := some s, overrideRetypes := false }

/-! Package enum metadata is available before module parameter defaults are
evaluated.  The package slice is fixed by the compilation unit, so its base
width and members can be bound before any module parameter is bound. -/
private def bindPackageEnumMembers (ty : String) (pkg : Option String) (w : Nat) :
    List PEnumMember → Res (List ((String × String) × LVec))
  | [] => .ok []
  | m :: rest => do
      let v ← match m.value with
        | .int v => pure (LVec.ofInt w v)
        | .bits s =>
            match LVec.ofBinLit? w s with
            | some v => pure v
            | none => Res.unsupported s!"enum member {ty}::{m.name}: bad bits {s.quote}"
      let vs ← bindPackageEnumMembers ty pkg w rest
      .ok (((enumKey ty pkg, m.name), v) :: vs)

def bindPackageEnums (env : IEnv) : List PEnumType → Res IEnv
  | [] => .ok env
  | et :: rest =>
      if et.pkg.isNone then bindPackageEnums env rest
      else
        match et.base.width env with
        | .error e => .unsupported s!"enum '{et.name}': {e}"
        | .ok w => do
            let ms ← bindPackageEnumMembers et.name et.pkg w et.members
            bindPackageEnums { env with enums := (enumKey et.name et.pkg, w) :: env.enums,
                                         members := ms ++ env.members } rest

/-- A parameter's default value (`PParam.evalDefault`).  A default that
calls a constant function is evaluated after its calls (`constCalls`). -/
def defaultValAt (env : IEnv) (p : PParam) (e : PExpr) : Except String Int :=
  match p.evalDefault env e with
  | .ok v => .ok v
  | .error msg => withConstCalls env e msg fun e' => p.evalDefault env e'

/-- The type of an untyped parameter at its default
(`PParam.defaultConstType`), with the same treatment of calls. -/
def defaultTypeAt (env : IEnv) (p : PParam) (e : PExpr) :
    Except String (Option (Nat × Bool)) :=
  match p.defaultConstType env with
  | .ok ty => .ok ty
  | .error msg =>
      withConstCalls env e msg fun e' =>
        ({ p with default? := some e' } : PParam).defaultConstType env

/-- **A partially overridden parameter point** `#(.P(v), …)`: `given[i] =
some v` overrides the i-th parameter with the integer `v`; `none` (or a
missing entry) keeps its default, evaluated in declaration order (each
default sees the earlier parameters). Returns the design with every
not-overridden untyped parameter whose default is not INT-class retyped to
the default's type (`PParam.defaultConstType`) and the argument list for
`instantiate`/`instantiate2`, defaults converted to their bound type (the
`defaultArgs` rule). At the all-default point this is the design slang
elaborated the envelope's `resolved` metadata at. -/
def PDesign.atPoint (d : PDesign) («given» : List (Option Int)) :
    Except String (PDesign × List Int) := do
  let envPE ← match bindPackageEnums { functions := d.functions } d.enums with
    | .ok e => .ok e
    | .unsupported e => .error e
    | .timeout => .error "package enum binding timed out"
  let envP ← match bindPackageParams envPE d.packageParams with
    | .ok e => .ok e
    | .unsupported e => .error e
    | .timeout => .error "package parameter binding timed out"
  let (ps, args) ← go envP d.params given
  return ({ d with params := ps }, args)
where
  go (env : IEnv) : List PParam → List (Option Int) → Except String (List PParam × List Int)
    | [], _ => .ok ([], [])
    | p :: rest, given => do
        let g := given.head?.join
        let (p', v) ← match g with
          | some v => pure (p, v)
          | none =>
              match p.default? with
              | none => throw s!"parameter '{p.name}' has no default"
              | some e => do
                  if p.hasAggregateDefault env then
                    -- Aggregate defaults are source-shaped values, not Nat
                    -- arguments.  Keep the placeholder out of the integer
                    -- environment in `bindParams`; hierarchy forwarding
                    -- recognizes the retained default and preserves it.
                    pure (p, 0)
                  else
                    let v ← (defaultValAt env p e).mapError fun m => s!"parameter '{p.name}' default: {m}"
                    match ← (defaultTypeAt env p e).mapError
                        (fun m => s!"parameter '{p.name}' default type: {m}") with
                    | none => pure (p, v)
                    | some (w, s) => pure (p.retype w s, v)
        let env' ← bindParams env [p'] [v]
        let v' := match g, env'.nvals.lookup p'.name with
          | none, some (c, _, _) => c
          | _, _ => v
        let (ps, vs) ← go env' rest given.tail
        .ok (p' :: ps, v' :: vs)

/-- Set `PParam.overrideRetypes` on exactly the parameters `atPoint []`
retypes — the untyped ones whose default-point type is not their override
reading. Ingestion (`Ingest2`) applies it to every loaded envelope; a design
whose defaults fail to evaluate is left unmarked (the load gate refuses it). -/
def PDesign.markOverrideRetypes (d : PDesign) : PDesign :=
  match d.atPoint [] with
  | .ok (d', _) =>
      { d with params := (d.params.zip d'.params).map fun (p, p') =>
          { p with overrideRetypes := p.type?.isNone && p'.type?.isSome } }
  | .error _ => d

/-- Bind one localparam: a typed one takes its declared type (the value
converted to it — the assignment-like context of §10.8, evaluated at the
declared width at THESE parameters by `evalAssign`: slang sized the tree
to the DEFAULT point's width only); an untyped one takes the type of its
expression (INT class to `vals`, anything else to `nvals` at its `ctype`). -/
def bindLocal (env : IEnv) (lp : PLocalParam) : Except String IEnv := do
  if lp.type?.isNone && lp.signed?.isSome then
    throw "Constant:untyped-signing — IEEE 1800-2023 §6.20.2 leaves no-range localparam signing implementation-defined"
  match lp.type? with
  | none =>
      -- Round 5 folds: loud where its own-type value wraps (`evalUntyped`).
      let v ← evalUntyped env lp.expr
      if lp.expr.isInt env then .ok (env.bindVal lp.name v)
      else
        let (w, inferredSigned) ← ctype env lp.expr
        let s := lp.signed?.getD inferredSigned
        -- Its type is its expression's, so it is stale where that reads one.
        let env' := env.bindNVal lp.name (canonInt w s v) w s
        .ok (if !env.stale.isEmpty && lp.expr.mentionsAny env.stale then
          { env' with stale := lp.name :: env.stale } else env')
  | some ty =>
      match ← declConstType env lp.type? lp.signed? with
      | none =>
          -- Round 4 folds: an `integer`/`int` localparam is a 32-bit target
          -- (`evalIntTarget`, repro `rf_int`); an enum-typed one keeps `evalInt`.
          let v ← match ty with
            | .typeRef .. => evalInt env lp.expr
            | _ => evalIntTarget env lp.expr
          if env.int32 then
            match lp.expr with
            | .squash2 _ (.sysCall .clog2 _) =>
                -- The result of `$clog2` over a signed-32 parameter is at
                -- most 31, so the signed-32 conversion is definitionally
                -- the identity on this structural path.
                .ok (env.bindNVal lp.name v 32 true)
            | _ => .ok (env.bindNVal lp.name (canonInt 32 true v) 32 true)
          else .ok (env.bindVal lp.name (if lp.expr.isInt env then v else canonInt 32 true v))
      | some (w, s) =>
          -- Round 3 folds: the initializer at the declared width HERE
          -- (`evalAssign`), not the default point's (`vp_lp2`, `vp_lp`).
          let v' ← if lp.expr.isInt env then evalInt env lp.expr else evalAssign env w lp.expr
          .ok ((env.withPDims lp.name lp.type?).bindNVal lp.name (canonInt w s v') w s)

/-- A localparam whose value calls a constant function (§13.4.3), reached
when `bindLocal` refuses the expression as written (`msg`): the calls are
evaluated first (`constCalls`), then `bindLocal` binds the result.  Without a
call the refusal stands. -/
def bindLocalCalls (env : IEnv) (lp : PLocalParam) (msg : String) : Except String IEnv :=
  withConstCalls env lp.expr msg fun e => bindLocal env { lp with expr := e }

/-- `bindLocal`, with constant-function calls (`bindLocalCalls`). -/
def bindLocalC (env : IEnv) (lp : PLocalParam) : Except String IEnv :=
  match bindLocal env lp with
  | .ok env' => .ok env'
  | .error e => bindLocalCalls env lp e

/-- Bind localparams in declaration order (each sees the parameters and
all earlier localparams). -/
def bindLocals (env : IEnv) : List PLocalParam → Res IEnv
  | [] => .ok env
  | lp :: rest =>
      match bindLocal env lp with
      | .error e =>
          match bindLocalCalls env lp e with
          | .error e' => .unsupported s!"localparam '{lp.name}': {e'}"
          | .ok env' => bindLocals env' rest
      | .ok env' => bindLocals env' rest

private def enumMemberVals (ty : String) (pkg : Option String) (w : Nat) :
    List PEnumMember → Res (List ((String × String) × LVec))
  | [] => .ok []
  | m :: rest => do
      let v ← match m.value with
        | .int v => pure (LVec.ofInt w v)
        | .bits s =>
            match LVec.ofBinLit? w s with
            | some v => pure v
            | none => Res.unsupported s!"enum member {ty}::{m.name}: bad bits {s.quote}"
      let vs ← enumMemberVals ty pkg w rest
      .ok (((enumKey ty pkg, m.name), v) :: vs)

/-- Bind the enum tables (base widths may mention parameters). -/
def bindEnums (env : IEnv) : List PEnumType → Res IEnv
  | [] => .ok env
  | et :: rest =>
      match et.base.width env with
      | .error e => .unsupported s!"enum '{et.name}': {e}"
      | .ok w => do
          let ms ← enumMemberVals et.name et.pkg w et.members
          bindEnums { env with enums := (enumKey et.name et.pkg, w) :: env.enums,
                               members := ms ++ env.members } rest

/-! ## Generate expansion -/

/-- Decode a generate step: `g++` ↦ `+1`, `g--` ↦ `-1` (the extractor's
committed step vocabulary). -/
def stepDelta (g : String) : PExpr → Except String Int
  | .unary .inc (.genvarRef g') =>
      if g' == g then .ok 1 else .error s!"step increments '{g'}', loop genvar is '{g}'"
  | .unary .dec (.genvarRef g') =>
      if g' == g then .ok (-1) else .error s!"step decrements '{g'}', loop genvar is '{g}'"
  | _ => .error "generate step outside the ++/-- tier"

/-- The genvar value sequence of a generate-for: from `i`, keep values
while `bound` evaluates nonzero, stepping by `δ`. Fueled — the one
genuinely unbounded recursion of instantiation (`.timeout` = fuel
exhausted; loop bounds beyond the surface fuel are loud, never wrong). -/
def genvarSeq (env : IEnv) (g : String) (bound : PExpr) (δ : Int) :
    Nat → Int → Res (List Int)
  | 0, _ => .timeout
  | fuel + 1, i =>
      match evalInt (env.bindVal g i) bound with
      | .error e => .unsupported s!"generate bound: {e}"
      | .ok v =>
          if v == 0 then .ok []
          else do
            let rest ← genvarSeq env g bound δ fuel (i + δ)
            .ok (i :: rest)

mutual
/-- Expand one generate item into M0 processes. Generate-local
declarations are outside this slice (they need per-instance scoping) —
they arrive as loud unsupported items from the parser. -/
def GenItem.expand (env : IEnv) (iterFuel : Nat) : GenItem → Res (List Process)
  | .process p => .ok [instProcess env p]
  | .decl d => .ok [.unsupported "GenerateDecl:UnpackedDecl"
      s!"generate-local declaration '{d.name}' outside the flat process tier"]
  | .localParam p => .ok [.unsupported "GenerateDecl:LocalParam"
      s!"generate-local parameter '{p.name}' outside the flat process tier"]
  | .unsupported k t => .ok [.unsupported k t]
  | .inst i => .ok [.unsupported "Instance"
      s!"module instance '{i.name}' of '{i.module}' outside the M0 tier"]
  | .genIf cond thenB elseB =>
      match evalGenGuard env cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v =>
          if v != 0 then expandScopedList env iterFuel thenB
          else expandScopedList env iterFuel elseB
  | .genFor _label g initE bound step _rc body =>
      match evalInt env initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env g bound δ iterFuel i0
          expandIters env iterFuel g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- Expand a generate item list (concatenation, source order). -/
def expandList (env : IEnv) (iterFuel : Nat) : List GenItem → Res (List Process)
  | [] => .ok []
  | it :: rest => do
      let ps ← it.expand env iterFuel
      let qs ← expandList env iterFuel rest
      .ok (ps ++ qs)
  termination_by l => (sizeOf l, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- Expand a generate branch with its source-shaped localparams in scope.
Each local parameter belongs to the enclosing generate block (§27.4), so
the binding is threaded only through that branch and is never leaked into a
sibling or the module scope. -/
def expandScopedList (env : IEnv) (iterFuel : Nat) : List GenItem → Res (List Process)
  | [] => .ok []
  | .localParam p :: rest =>
      match bindLocal env p with
      | .error e => .unsupported s!"generate-local parameter '{p.name}': {e}"
      | .ok env' => expandScopedList env' iterFuel rest
  | it :: rest => do
      let ps ← it.expand env iterFuel
      let qs ← expandScopedList env iterFuel rest
      .ok (ps ++ qs)
  termination_by l => (sizeOf l, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- Expand a generate-for body template at each genvar value —
**the** family recursion (`expandIters_*` lemmas below are its
induction handles). -/
def expandIters (env : IEnv) (iterFuel : Nat) (g : String) :
    List Int → List GenItem → Res (List Process)
  | [], _ => .ok []
  | v :: vs, body => do
      let ps ← expandList (env.bindVal g v) iterFuel body
      let qs ← expandIters env iterFuel g vs body
      .ok (ps ++ qs)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

/-! ## `instantiate` -/

/-- The loud error design: any run of it is `.unsupported` at the first
cycle (`Process.unsupported` is comb-phase — the M0 loudness discipline),
and `Design.hasUnsupported` is `true`. -/
def Design.errorDesign (name msg : String) : Design :=
  { name, decls := #[], processes := #[.unsupported "Instantiate" msg] }

/-- **Instantiate a parametric design at concrete parameter values**
(`args` in declaration order — the binder encoding of
`load_design_sv2`). Substitutes parameters, evaluates localparams/enum
tables/declared widths in order, instantiates every process, and expands
the generate items (`iterFuel` bounds each generate loop's iteration
count). Errors are loud: `.unsupported` on bad parameters (arity,
failing constant evaluation), `.timeout` on generate fuel exhaustion.
Out-of-M0-tier *constructs* do NOT fail instantiation — they become
`.unsupported` nodes inside the design, loud only when the M0 interpreter
reaches them. -/
def PDesign.instantiate (d : PDesign) (args : List Int) (iterFuel : Nat := 4096) :
    Res Design :=
  if args.length != d.params.length then
    .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
  else do
    let envPkgEnums ← bindPackageEnums { functions := d.functions } d.enums
    let envPkgParams ← bindPackageParams envPkgEnums d.packageParams
    let env0 ← bindParamsRes envPkgParams d.params args
    let env1 ← bindLocals env0 d.localParams
    let env2 ← bindEnums env1 d.enums
    let decls ← buildDecls env2 d.decls
    let envP := { env2 with widths := decls.map fun dc => (dc.name, dc.width) }
    let gens ← expandList envP iterFuel d.generates
    .ok { name := d.name
          decls := decls.toArray
          processes :=
            ((d.processes.map (instProcess envP)) ++ gens
              ++ d.others.map fun (k, t) => Process.unsupported k t).toArray }

/-- Surface iteration fuel: covers every generate loop whose iteration
count is at most quadratic in the total parameter magnitude (in
particular the `2^(clog2 W)`-shaped tree loops of `ff_one`). A loop
beyond it instantiates to the loud timeout design — never wrong,
possibly conservative. -/
def PDesign.surfaceFuel (args : List Int) : Nat :=
  let s := (args.map Int.natAbs).sum
  (s + 2) * (s + 2) + 64

/-- The `Design`-valued instantiation used by the `load_design_sv2`
binder encoding (`name : (params : Nat…) → Design`): errors collapse to
the loud `errorDesign` (any run is `.unsupported`), so the family is
total without ever being silently wrong. Proof work should prefer
`instantiate` (the `Res` form) and the lemmas below. -/
def PDesign.instantiateD (d : PDesign) (args : List Int) : Design :=
  match d.instantiate args (PDesign.surfaceFuel args) with
  | .ok m => m
  | .timeout => .errorDesign d.name "generate expansion fuel exhausted"
  | .unsupported msg => .errorDesign d.name msg

/-! ## Defaults and the metadata cross-check

The envelope's `resolved`-family fields are slang's own
defaults-elaboration — metadata, never the contract. `crossCheck`
replays our elaboration at the defaults and compares: a nonempty result
means the Lean elaboration semantics and slang disagree, and the
`load_design_sv2` command refuses the envelope (the ingestion-time
differential test against the frontend). -/

/-- Evaluate the parameter defaults in declaration order (each sees the
earlier ones). -/
def PDesign.defaultArgs (d : PDesign) : Res (List Int) :=
  -- Defaults are elaborated as the declared 32-bit `int` context.  The
  -- previous empty environment selected the unbounded proof evaluator, so a
  -- localparam could lose an overflowing intermediate before its final cast.
  -- Carry source-shaped pure function declarations into parameter defaults;
  -- otherwise a module/package constant function is reported as a generic
  -- `CallExpression` during the loader's own differential cross-check.
  let env0 : IEnv := { int32 := true, functions := d.functions }
  match bindPackageEnums env0 d.enums with
  | .ok envE =>
      match bindPackageParams envE d.packageParams with
      | .ok envP => go envP d.params
      | .unsupported msg => .unsupported msg
      | .timeout => .timeout
  | .unsupported msg => .unsupported msg
  | .timeout => .timeout
where
  go (env : IEnv) : List PParam → Res (List Int)
    | [] => .ok []
    | p :: rest =>
        match p.default? with
        | none => .unsupported s!"parameter '{p.name}' has no default"
        | some e =>
            match defaultValAt env p e with
            | .error err => .unsupported s!"parameter '{p.name}' default: {err}"
            | .ok v =>
                -- The default converted to the declared type, bound the way
                -- `instantiate` binds it (later defaults see the same class).
                match bindParams env [p] [v] with
                | .error err => .unsupported err
                | .ok env' => do
                    let v' := match env'.nvals.lookup p.name with
                      | some (c, _, _) => c
                      | none => v
                    let vs ← go env' rest
                    .ok (v' :: vs)

private def checkLocals (env : IEnv) : List PLocalParam → List String × IEnv
  | [] => ([], env)
  | lp :: rest =>
      match bindLocalC env lp with
      | .error e => ([s!"localparam '{lp.name}': {e}"], env)
      | .ok env' =>
          let v := match env'.vals.lookup lp.name, env'.nvals.lookup lp.name with
            | some x, _ => x
            | none, some (x, _, _) => x
            | none, none => 0
          let tail := checkLocals env' rest
          (match lp.resolved? with
            | some r =>
                if r == v then tail.1
                else s!"localparam '{lp.name}': ours {v} ≠ resolved {r}" :: tail.1
            | none => tail.1, tail.2)

/-- Compare every bound package constant with the parser's own value.
Where the envelope gives the value bit for bit (`resolvedBits?`), the bits
(x and z included), the width and the signedness are compared; an older
envelope gives one integer (`resolved?`), compared with the constant's
integer view. -/
def checkPackageParams (env : IEnv) : List (String × PParam) → List String
  | [] => []
  | (pkg, p) :: rest =>
      let tail := checkPackageParams env rest
      match env.packageFVal pkg p.name with
      | none => tail
      | some (v, w, s) =>
          let who := s!"package parameter '{pkg}::{p.name}'"
          match p.resolvedBits? with
          | some bits =>
              let ours := v.toBinString
              (if ours != bits then [s!"{who}: ours {ours} ≠ resolved {bits}"] else []) ++
              (if w != bits.length then [s!"{who}: our width {w} ≠ resolved {bits.length}"] else []) ++
              (match p.resolvedSigned? with
               | some rs => if rs != s then
                   [s!"{who}: ours is {if s then "signed" else "unsigned"}, resolved {if rs then "signed" else "unsigned"}"]
                 else []
               | none => []) ++ tail
          | none =>
              match p.resolved? with
              | none => tail
              | some r =>
                  match v.toNat? with
                  | some k =>
                      if canonInt w s k == r then tail
                      else s!"{who}: ours {canonInt w s k} ≠ resolved {r}" :: tail
                  | none => s!"{who}: ours has x/z bits, resolved {r}" :: tail

def checkPackageAggs (env : IEnv) : List (String × PParam) → List String
  | [] => []
  | (pkg, p) :: rest =>
      let tail := checkPackageAggs env rest
      match p.aggregate?, p.resolvedBits?, env.packageAgg? pkg p.name with
      | some _, some bits, some agg =>
          let ours := String.intercalate "" (agg.elements.map (·.toBinString))
          (if ours == bits then []
           else [s!"package aggregate '{pkg}::{p.name}': ours {ours} ≠ resolved {bits}"]) ++ tail
      | _, _, _ => tail

/-- How many package constants `checkPackageParams` compares. -/
def comparablePackageParams (env : IEnv) (ps : List (String × PParam)) : Nat :=
  (ps.filter fun (pkg, p) =>
    (p.resolved?.isSome || p.resolvedBits?.isSome) && (env.packageFVal pkg p.name).isSome).length

def comparablePackageAggs (env : IEnv) (ps : List (String × PParam)) : Nat :=
  (ps.filter fun (pkg, p) =>
    p.aggregate?.isSome && p.resolvedBits?.isSome && (env.packageAgg? pkg p.name).isSome).length

/-- A refusal is reported with the package constants that are not bound and
why: a read of one of them is the usual cause. -/
def packageNotes (d : PDesign) (msgs : List String) : List String :=
  if msgs.isEmpty then []
  else
    msgs ++ match bindPackageEnums { int32 := true, functions := d.functions } d.enums with
      | .ok e => packageParamRefusals e d.packageParams
      | .unsupported _ | .timeout => []

private def PType.resolved? : PType → Option Nat
  | .packed _ r => r
  | .typeRef _ _ r => r
  | .unrecoverable r => r

private def checkDecls (env : IEnv) : List PDecl → List String
  | [] => []
  | pd :: rest =>
      -- A parser-retained aggregate declaration carries its source-shaped
      -- `PAggType` in `aggregate?`; its packed `PType` is deliberately
      -- unrecoverable because the scalar width is not the declaration's
      -- aggregate layout.  The aggregate bridge performs the exact
      -- structure check when E instantiates the declaration, so the scalar
      -- defaults cross-check must leave this node to that bridge rather than
      -- reporting a false `unrecoverable packed dimensions` mismatch.
      if pd.aggregate?.isSome then
        checkDecls env rest
      else
      -- A one-rank unpacked declaration is retained for the E memory route.
      -- The legacy flat store still cannot turn it into a `Decl`, but its
      -- packed element width is a real elaboration fact and must participate
      -- in the loader's defaults cross-check rather than making every
      -- source-shaped memory look like a differential disagreement.
      if pd.unpackedDims.length == 1 then
        match pd.type.width env with
        | .error e => [s!"decl '{pd.name}': {e}"]
        | .ok w =>
            let tail := checkDecls
              { env with widths := (pd.name, w) :: env.widths } rest
            match pd.type.resolved? with
            | some r => if r == w then tail
                        else s!"decl '{pd.name}': our width {w} ≠ resolved {r}" :: tail
            | none => tail
      else match pd.type.width env with
      | .error e => [s!"decl '{pd.name}': {e}"]
      | .ok w =>
          -- A runtime declaration initializer is source-shaped state at
          -- time zero, not defaults metadata. Keep the width differential
          -- check here; flat M0 instantiation remains loud, while the
          -- source-shaped memory route evaluates the retained expression.
          let tail := checkDecls
            { env with widths := (pd.name, w) :: env.widths } rest
          match pd.type.resolved? with
          | some r =>
              if r == w then tail
              else s!"decl '{pd.name}': our width {w} ≠ resolved {r}" :: tail
          | none => tail

private def checkGenerateLocals (env : IEnv) (iterFuel : Nat) : Nat → List GenItem → List String
  | 0, _ => []
  | fuel + 1, [] => []
  | fuel + 1, .localParam p :: rest =>
      let (msgs, env') := checkLocals env [p]
      msgs ++ checkGenerateLocals env' iterFuel fuel rest
  | fuel + 1, .genIf cond thenB elseB :: rest =>
      let branch := match evalGenGuard env cond with
        | .ok v => if v != 0 then thenB else elseB
        | .error _ => []
      checkGenerateLocals env iterFuel fuel branch ++ checkGenerateLocals env iterFuel fuel rest
  | fuel + 1, .genFor _label g initE bound step _rc body :: rest =>
      let branch := match evalInt env initE, stepDelta g step with
        | .ok i0, .ok δ =>
            match genvarSeq env g bound δ iterFuel i0 with
            | .ok (i :: _) => checkGenerateLocals (env.bindVal g i) iterFuel fuel body
            | .ok [] | .timeout | .unsupported _ => []
        | .error _, _ | _, .error _ => []
      branch ++ checkGenerateLocals env iterFuel fuel rest
  | fuel + 1, _ :: rest => checkGenerateLocals env iterFuel fuel rest

private def checkGenerates (env : IEnv) (iterFuel : Nat) : List GenItem → List String
  | [] => []
  | .genFor label g initE bound step rc? body :: rest =>
      let name := label.getD g
      let here :=
        match evalInt env initE, stepDelta g step with
        | .ok i0, .ok δ =>
            match genvarSeq env g bound δ iterFuel i0, rc? with
            | .ok vs, some rc =>
                if vs.length == rc then []
                else [s!"generate '{name}': our count {vs.length} ≠ resolved {rc}"]
            | .ok _, none => []
            | .timeout, _ => [s!"generate '{name}': iteration fuel exhausted"]
            | .unsupported e, _ => [s!"generate '{name}': {e}"]
        | .error e, _ | _, .error e => [s!"generate '{name}': {e}"]
      here ++ checkGenerateLocals env iterFuel 64 [.genFor label g initE bound step rc? body] ++
        checkGenerates env iterFuel rest
  | .genIf cond thenB elseB :: rest =>
      checkGenerateLocals env iterFuel 64 [.genIf cond thenB elseB] ++ checkGenerates env iterFuel rest
  | .localParam p :: rest =>
      checkGenerateLocals env iterFuel 64 [.localParam p] ++ checkGenerates env iterFuel rest
  | _ :: rest => checkGenerates env iterFuel rest

/-- Replay the defaults elaboration and compare against every `resolved`
metadata field the envelope carries: parameter defaults, localparams,
declared widths, and **top-level** generate-for counts (nested counts
are defaults-dependent per instance; the top level is what slang's
`resolved_count` reports for these envelopes). `[]` = clean. -/
def PDesign.crossCheck (d₀ : PDesign) : List String :=
  -- The DEFAULT point (`atPoint []`): untyped parameters with a non-INT
  -- default carry the default's type, as in slang's elaboration.
  match d₀.atPoint [] with
  | .error e => afterDefaultsError d₀ (s!"defaults: {e}")
  | .ok (d, args) =>
      let paramMsgs := (d.params.zip args).filterMap fun (p, v) =>
        match p.resolved? with
        | some r => if r == v then none else some s!"parameter '{p.name}': ours {v} ≠ resolved {r}"
        | none => none
      let envP : IEnv := match bindPackageEnums { int32 := true, functions := d.functions } d.enums with
        | .ok e => match bindPackageParams e d.packageParams with
          | .ok p => p
          | _ => {}
        | _ => {}
      let env0 : IEnv := (bindParams envP d.params args).toOption.getD envP
      let pkgMsgs := checkPackageParams envP d.packageParams ++ checkPackageAggs envP d.packageParams
      let (localMsgs, env1) := checkLocals env0 d.localParams
      let restMsgs := match bindEnums env1 d.enums with
        | .ok env2 =>
            paramMsgs ++ localMsgs ++ checkDecls env2 d.decls
              ++ checkGenerates
                  { env2 with widths := declWidths env2 d.decls } (PDesign.surfaceFuel args)
                  d.generates
        | .timeout => paramMsgs ++ localMsgs ++ ["enums: timeout"]
        | .unsupported e => paramMsgs ++ localMsgs ++ [s!"enums: {e}"]
      packageNotes d (pkgMsgs ++ restMsgs)
where
  /-- Continue the differential checks after a defaults error.  A failed
  package or parameter binding must not hide independent localparam,
  declaration-width, or generate-count mismatches later in the envelope. -/
  afterDefaultsError (d : PDesign) (head : String) : List String :=
    let env0 : IEnv := { int32 := true, functions := d.functions }
    let envP : IEnv :=
      match bindPackageEnums env0 d.enums with
      | .ok e =>
          match bindPackageParams e d.packageParams with
          | .ok p => p
          | .unsupported _ | .timeout => env0
      | .unsupported _ | .timeout => env0
    -- Keep every parameter that succeeded before the failing default in the
    -- environment used by the independent declaration checks.  Dropping
    -- those bindings would turn a real width into a spurious "unbound
    -- parameter" diagnostic and would prevent the hierarchy sidecar's
    -- memory-only exception from recognising the intended default failure.
    let envD := bindDefaultParams envP d.params
    let (localMsgs, env1) := checkLocals envD d.localParams
    let env2 :=
      match bindEnums env1 d.enums with
      | .ok e => e
      | .unsupported _ | .timeout => env1
    let declMsgs := checkDecls env2 d.decls
    let genMsgs := checkGenerates
      { env2 with widths := declWidths env2 d.decls }
      (PDesign.surfaceFuel []) d.generates
    packageNotes d (head :: (checkPackageParams envP d.packageParams ++ checkPackageAggs envP d.packageParams ++ localMsgs ++ declMsgs ++ genMsgs))

  bindDefaultParams (env : IEnv) : List PParam → IEnv
    | [] => env
    | p :: ps =>
        match p.default? with
        | none => bindDefaultParams env ps
        | some e =>
            match defaultValAt env p e with
            | .error _ => bindDefaultParams env ps
            | .ok v =>
                match bindParams env [p] [v] with
                | .ok env' => bindDefaultParams env' ps
                | .error _ => bindDefaultParams env ps

  declWidths (env : IEnv) (decls : List PDecl) : List (String × Nat) :=
    match buildDecls env decls with
    | .ok ds => ds.map fun dc => (dc.name, dc.width)
    | _ => []

/-- How many metadata fields `crossCheck` can actually COMPARE.

**Why this exists.** `crossCheck` skips every field whose `resolved?`
metadata is absent — the `| none =>` arms in the parameter fold, in
`checkLocals`, in `checkDecls`, and the count-less `genFor` — and returns
`[]`. So `[]` means BOTH "everything agreed" and "nothing was compared",
and an envelope carrying no `resolved` metadata at all passed the
"ingestion-time differential test against the frontend" without a single
comparison being made (quality audit 2026-08-23, `sv` MEDIUM,
`Param.lean:997`).

That is the same defect the family's `live` flag fixes for verdict rows:
**a vacuous run must not serialize as agreement.** Counting the
*comparable* fields is exact rather than approximate here, because
`crossCheck` compares precisely the fields whose metadata is `some` —
this count and the number of comparisons performed are the same number. -/
private def comparableCount (d : PDesign) : Nat :=
  (d.params.filter (·.resolved?.isSome)).length
  + (d.localParams.filter (·.resolved?.isSome)).length
  + (d.decls.filter (fun pd => (PType.resolved? pd.type).isSome)).length
  + (d.generates.filter (fun g =>
        match g with
        | .genFor _ _ _ _ _ rc _ => rc.isSome
        | _ => false)).length

/-- `crossCheck`'s messages PAIRED WITH the number of comparisons made, so
that "clean" and "compared nothing" stop being the same value.

`crossCheck` itself is unchanged and still returns just the messages, so
every existing `#guard … == []` keeps its meaning; the loader
(`load_design_sv2`) is what consumes the count and refuses **VACUOUS**. -/
def PDesign.crossCheckFull (d : PDesign) : List String × Nat :=
  (d.crossCheck, comparableCount d +
    match bindPackageEnums { int32 := true, functions := d.functions } d.enums with
    | .ok e =>
        match bindPackageParams e d.packageParams with
        | .ok envP => comparablePackageParams envP d.packageParams + comparablePackageAggs envP d.packageParams
        | .unsupported _ | .timeout => 0
    | .unsupported _ | .timeout => 0)

/-! ## Starter lemmas 1: instantiation preserves the declaration surface

Specs are ports-only, so the load-bearing well-formedness fact is that
`instantiate` never invents, drops, reorders, or re-flags declarations —
the name/direction surface of the instantiated design is
**parameter-independent** data of the `PDesign`. -/

/-- The parameter-independent declaration surface: names and port
directions, in declaration order. -/
def PDesign.declSig (d : PDesign) : List (String × Bool × Bool) :=
  d.decls.map fun pd => (pd.name, pd.isInput, pd.isOutput)

/-- Names of a `PDesign`'s declarations (ports first, declaration
order). -/
def PDesign.declNames (d : PDesign) : List String := d.decls.map (·.name)

/-- Name well-formedness of a parametric design: declared names are
distinct. -/
def PDesign.WFNames (d : PDesign) : Prop := d.declNames.Nodup

/-- Name well-formedness of an M0 design (what `SvState.set`/`lookup`
determinism arguments want). -/
def Design.WFNames (m : Design) : Prop := (m.decls.toList.map (·.name)).Nodup

instance (d : PDesign) : Decidable d.WFNames :=
  inferInstanceAs (Decidable d.declNames.Nodup)

instance (m : Design) : Decidable m.WFNames :=
  inferInstanceAs (Decidable (m.decls.toList.map (·.name)).Nodup)

theorem instDecl_sig {env : IEnv} {pd : PDecl} {dc : Decl}
    (h : instDecl env pd = .ok dc) :
    dc.name = pd.name ∧ dc.isInput = pd.isInput ∧ dc.isOutput = pd.isOutput := by
  unfold instDecl at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · cases h
    · split at h
      · cases h
        exact ⟨rfl, rfl, rfl⟩
      · split at h
        · cases h
          exact ⟨rfl, rfl, rfl⟩
        · split at h
          · cases h
            exact ⟨rfl, rfl, rfl⟩
          · cases h

theorem buildDecls_sig {l : List PDecl} :
    ∀ {env : IEnv} {r : List Decl}, buildDecls env l = .ok r →
      r.map (fun dc => (dc.name, dc.isInput, dc.isOutput)) =
        l.map (fun pd => (pd.name, pd.isInput, pd.isOutput)) := by
  induction l with
  | nil => intro env r h; cases h; rfl
  | cons pd rest ih =>
      intro env r h
      simp only [buildDecls, Res.bind_eq_ok] at h
      obtain ⟨dc, hdc, ds, hds, hr⟩ := h
      cases hr
      obtain ⟨hn, hi, ho⟩ := instDecl_sig hdc
      simp [hn, hi, ho, ih hds]

/-- **Instantiation preserves the declaration surface** — for every
parameter vector and fuel, the instantiated design's (name, input,
output) list is the `PDesign`'s `declSig`, i.e. the port surface is
parameter-independent. -/
theorem instantiate_declSig {d : PDesign} {args : List Int} {F : Nat} {m : Design}
    (h : d.instantiate args F = .ok m) :
    m.decls.toList.map (fun dc => (dc.name, dc.isInput, dc.isOutput)) = d.declSig := by
  unfold PDesign.instantiate at h
  split at h
  · exact absurd h (by simp)
  · simp only [Res.bind_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, decls, hdecls, gens, _, hm⟩ := h
    cases hm
    simpa [PDesign.declSig] using buildDecls_sig hdecls

/-- The instantiated design's name is the source module name. -/
theorem instantiate_name {d : PDesign} {args : List Int} {F : Nat} {m : Design}
    (h : d.instantiate args F = .ok m) : m.name = d.name := by
  unfold PDesign.instantiate at h
  split at h
  · exact absurd h (by simp)
  · simp only [Res.bind_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := h
    cases hm; rfl

/-- Declared names are parameter-independent. -/
theorem instantiate_declNames {d : PDesign} {args : List Int} {F : Nat} {m : Design}
    (h : d.instantiate args F = .ok m) :
    m.decls.toList.map (·.name) = d.declNames := by
  have hs := instantiate_declSig h
  have h1 : (m.decls.toList.map (fun dc => (dc.name, dc.isInput, dc.isOutput))).map Prod.fst
      = d.declSig.map Prod.fst := by rw [hs]
  simpa [PDesign.declSig, PDesign.declNames, List.map_map, Function.comp_def] using h1

/-- **Instantiation preserves name well-formedness**: distinct declared
names in the parametric design give distinct declared names in every
instantiation. -/
theorem instantiate_WFNames {d : PDesign} {args : List Int} {F : Nat} {m : Design}
    (h : d.instantiate args F = .ok m) (hd : d.WFNames) : m.WFNames := by
  unfold Design.WFNames
  rw [instantiate_declNames h]
  exact hd

/-! ## Starter lemmas 2: generate expansion — the family induction handles -/

/-- `expandIters` **is** flatten-of-map: if each iteration's body
expansion is known, the whole family is their concatenation in genvar
order. Everything else about a `GenerateFor` family reduces through this
equation. -/
theorem expandIters_eq_flatten {env : IEnv} {F : Nat} {g : String}
    {body : List GenItem} {f : Int → List Process} :
    ∀ {vs : List Int},
      (∀ v ∈ vs, expandList (env.bindVal g v) F body = .ok (f v)) →
      expandIters env F g vs body = .ok (vs.map f).flatten := by
  intro vs
  induction vs with
  | nil => intro _; simp [expandIters]
  | cons v vs ih =>
      intro h
      have hv := h v (List.mem_cons_self ..)
      have hrest := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
      simp [expandIters, hv, hrest]

/-- Membership in an expanded family: exactly the per-iteration
processes, for some genvar value of the loop. -/
theorem mem_expandIters {env : IEnv} {F : Nat} {g : String}
    {body : List GenItem} {f : Int → List Process} {vs : List Int} {ps : List Process}
    (hf : ∀ v ∈ vs, expandList (env.bindVal g v) F body = .ok (f v))
    (h : expandIters env F g vs body = .ok ps) (p : Process) :
    p ∈ ps ↔ ∃ v ∈ vs, p ∈ f v := by
  rw [expandIters_eq_flatten hf] at h
  cases h
  simp [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨l, ⟨v, hv, rfl⟩, hp⟩; exact ⟨v, hv, hp⟩
  · rintro ⟨v, hv, hp⟩; exact ⟨f v, ⟨v, hv, rfl⟩, hp⟩

/-- Family size, uniform-template case: a body that expands to `c`
processes at every genvar value gives `c * |vs|` processes — the length
arithmetic of every `GenerateFor` family proof. -/
theorem expandIters_length_const {env : IEnv} {F : Nat} {g : String}
    {body : List GenItem} {f : Int → List Process} {c : Nat}
    {vs : List Int} {ps : List Process}
    (hf : ∀ v ∈ vs, expandList (env.bindVal g v) F body = .ok (f v))
    (hc : ∀ v ∈ vs, (f v).length = c)
    (h : expandIters env F g vs body = .ok ps) : ps.length = c * vs.length := by
  rw [expandIters_eq_flatten hf] at h
  cases h
  clear hf
  induction vs with
  | nil => simp
  | cons v vs ih =>
      have hi := ih fun w hw => hc w (List.mem_cons_of_mem _ hw)
      simp [List.flatten_cons, hc v (List.mem_cons_self ..), hi,
            Nat.mul_succ, Nat.add_comm]

/-- `[i0, i0+1, …, i0+n-1]` — the canonical ascending genvar value
sequence (the `List Int` counterpart of `List.range`, offset-friendly:
generate loops start anywhere). -/
def intRange (i0 : Int) : Nat → List Int
  | 0 => []
  | n + 1 => i0 :: intRange (i0 + 1) n

@[simp] theorem intRange_length : ∀ (n : Nat) (i0 : Int), (intRange i0 n).length = n
  | 0, _ => rfl
  | n + 1, i0 => by simp [intRange, intRange_length n]

@[simp] theorem mem_intRange {v : Int} :
    ∀ {n : Nat} {i0 : Int}, v ∈ intRange i0 n ↔ i0 ≤ v ∧ v < i0 + n := by
  intro n
  induction n with
  | zero => intro i0; simp [intRange]
  | succ n ih => intro i0; simp [intRange, ih]; omega

/-- A genvar reference under its own binding evaluates to the bound
value. -/
theorem evalInt_genvarRef_bind {env : IEnv} {g : String} {v : Int} :
    evalInt (env.bindVal g v) (.genvarRef g) = .ok v := by
  simp [evalInt, IEnv.bindVal]

/-- Signed `<` on evaluated INT-class operands (the canonical generate-loop
bound shape). -/
theorem evalInt_slt {env : IEnv} {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary .slt l r) = .ok (b2i (decide (a < b))) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr]
  rfl

/-- The genvar sequence of the canonical ascending loop
(`for (g = i0; g s< e; g++)` with a loop-invariant bound expression
`e ⇓ N`): consecutive integers `i0, i0+1, …, N-1`, provided the fuel
exceeds the trip count. **The** induction workhorse for `ff_one`-shaped
∀-parameter families. -/
theorem genvarSeq_ascending {env : IEnv} {g : String} {e : PExpr} {N : Int}
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N) :
    ∀ {fuel : Nat} (i0 : Int), (N - i0).toNat < fuel →
      genvarSeq env g (.binary .slt (.genvarRef g) e) 1 fuel i0 =
        .ok (intRange i0 (N - i0).toNat) := by
  intro fuel
  induction fuel with
  | zero => intro i0 h; omega
  | succ fuel ih =>
      intro i0 hfuel
      have hbound := evalInt_slt (env := env.bindVal g i0) (l := .genvarRef g) rfl (hei i0)
        (evalInt_genvarRef_bind (env := env) (g := g) (v := i0)) (he i0)
      by_cases hlt : i0 < N
      · have hcount : (N - i0).toNat = (N - (i0 + 1)).toNat + 1 := by omega
        have hrec := ih (i0 + 1) (by omega)
        rw [hcount]
        simp [genvarSeq, hbound, hlt, b2i, hrec, intRange]
      · have hz : (N - i0).toNat = 0 := by omega
        rw [hz]
        simp [genvarSeq, hbound, hlt, b2i, intRange]

/-- Trip count of the canonical ascending loop. -/
theorem genvarSeq_ascending_length {env : IEnv} {g : String} {e : PExpr} {N : Int}
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N)
    {fuel : Nat} {i0 : Int} (hfuel : (N - i0).toNat < fuel) {vs : List Int}
    (h : genvarSeq env g (.binary .slt (.genvarRef g) e) 1 fuel i0 = .ok vs) :
    vs.length = (N - i0).toNat := by
  rw [genvarSeq_ascending hei he i0 hfuel] at h
  cases h; simp

/-! ## Hand-built parametric smoke

`gen_sel(W, K)`: `W`-bit input `a`, output `y`; a generate-for over
`j s< K` whose body is a generate-if selecting exactly the last
iteration (`j == K-1`, via a localparam) to drive `assign y = a + j` —
exercising symbolic widths, localparam evaluation, `GenerateFor` +
`GenerateIf` expansion, and a genvar in a value position, all fully
inside the M0 tier after instantiation. The localparam is `localparam int
KM1 = K - 1`; its typed 32-bit context is evaluated exactly at each point. -/

private def wm1 : PDim := ⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩

private def km1Expr : PExpr := .binary (.m0 .sub) (.paramRef "K" none) (.int 1)

private def pGenSel : PDesign :=
  { name := "gen_sel"
    params := [
      { name := "W", default? := some (.int 8), resolved? := some 8 },
      { name := "K", default? := some (.int 3), resolved? := some 3 }]
    localParams := [
      { name := "KM1", expr := km1Expr, resolved? := some 2,
        type? := some (.packed [⟨.int 31, .int 0⟩] (some 32)) }]
    enums := []
    decls := [
      { name := "a", type := .packed [wm1] (some 8), isInput := true },
      { name := "y", type := .packed [wm1] (some 8), isOutput := true }]
    processes := []
    generates := [
      .genFor (some "gen") "j" (.int 0)
        (.binary .slt (.genvarRef "j") (.paramRef "K" none))
        (.unary .inc (.genvarRef "j")) (some 3)
        [.genIf (.binary (.m0 .eq) (.genvarRef "j") (.paramRef "KM1" none))
          [.process (.assign "y" (.binary (.m0 .add) (.ident "a") (.genvarRef "j")))]
          []]]
    others := [] }

-- Metadata cross-check at defaults is clean.
#guard pGenSel.crossCheck == []
-- The untyped twin `localparam KM1 = K - 1` is loud (round 6 over-refusal).
#guard (pGenSel.instantiate [8, 3] matches .ok _)
#guard ({ pGenSel with localParams := [{ name := "KM1", expr := km1Expr, resolved? := some 2 }] }
  |>.instantiate [8, 3]) matches .unsupported _

-- Instantiation at the defaults: exactly one surviving assign, `y = a + 2#8`.
#guard pGenSel.instantiate [8, 3] ==
  .ok { name := "gen_sel"
        decls := #[
          { name := "a", width := 8, isInput := true },
          { name := "y", width := 8, isOutput := true }]
        processes := #[.assign "y" (.binary .add (.ident "a") (.lit (.ofNat 8 2)))] }

-- … and it RUNS under the untouched M0 cycle semantics: y = a + (K-1).
#guard (Res.toOption (run (pGenSel.instantiateD [8, 3]) σ_src 64 [[("a", LVec.ofNat 8 5)]])).map
        (fun tr => tr.map (fun st => SvState.showSignal st "y"))
      == some ["00000111"]

-- A different parameter point, same family: W = 4, K = 1 → y = a + 0.
#guard (Res.toOption (run (pGenSel.instantiateD [4, 1]) σ_src 64 [[("a", LVec.ofNat 4 9)]])).map
        (fun tr => tr.map (fun st => SvState.showSignal st "y"))
      == some ["1001"]

-- K = 0: empty family — y is undriven and stays x (still a legal run).
#guard (Res.toOption (run (pGenSel.instantiateD [4, 0]) σ_src 64 [[("a", LVec.ofNat 4 9)]])).map
        (fun tr => tr.map (fun st => SvState.showSignal st "y"))
      == some ["xxxx"]

-- Bad parameters are loud, not wrong.
#guard pGenSel.instantiate [8] == .unsupported "parameter arity: got 1, want 2"
#guard (pGenSel.instantiateD [8]).hasUnsupported
#guard run (pGenSel.instantiateD [8]) σ_src 64 [[]]
        == .unsupported "unsupported process 'Instantiate'"

-- The declaration surface is parameter-independent (executable instance
-- of `instantiate_declSig`).
#guard ((pGenSel.instantiate [4, 1]).toOption.map
          fun m => m.decls.toList.map (·.name)) == some ["a", "y"]

-- The ascending-loop lemma, demonstrated at a symbolic parameter: for
-- every K, the genvar sequence of `for (j = 0; j s< K; j++)` under
-- `K ↦ K` is `[0, …, K-1]`.
example (K : Nat) :
    genvarSeq { vals := [("K", (K : Int))] } "j"
        (.binary .slt (.genvarRef "j") (.paramRef "K" none)) 1 (K + 1) 0 =
      .ok (intRange 0 K) := by
  have he : ∀ i : Int,
      evalInt (IEnv.bindVal { vals := [("K", (K : Int))] } "j" i)
        (.paramRef "K" none) = .ok (K : Int) := by
    intro i
    simp [evalInt, IEnv.bindVal, List.lookup]
  have hei : ∀ i : Int,
      (PExpr.paramRef "K" none).isInt (IEnv.bindVal { vals := [("K", (K : Int))] } "j" i) := by
    intro i
    simp [PExpr.isInt, IEnv.bindVal, List.lookup]
  have h := genvarSeq_ascending hei he (fuel := K + 1) 0 (by omega)
  simpa using h


/-! ## Width-exact constants (verifier probes `ps_wrap`/`pc`, 2026-10-28)

`logic [2:0] K` binds in `nvals`; arithmetic with sized operands wraps at the
self-determined width (IEEE 1800-2023 §11.6/§11.8) exactly as Icarus 12.0 and
Yosys 0.53 compute it; the INT path is untouched. -/

private def okIs (r : Except String Int) (v : Int) : Bool :=
  match r with
  | .ok x => x == v
  | .error _ => false

private def isLoud (r : Except String Int) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

/-- `parameter logic [2:0] K = k`, `parameter int unsigned UI = u`,
`parameter int N = n` (an INT parameter, `vals`). -/
private def wrapEnv (k u n : Int) : IEnv :=
  { vals := [("N", n)], nvals := [("K", (k, 3, false)), ("UI", (u, 32, false))] }

private def kRef : PExpr := .paramRef "K" none
private def lit3 (v : Nat) : PExpr := .lit (.ofNat 3 v)

-- `K + 3'd4` / `K - 3'd6` wrap at 3 bits (K = 5: 1 and 7; K = 7: 3).
#guard okIs (evalInt (wrapEnv 5 0 0) (.binary (.m0 .add) kRef (lit3 4))) 1
#guard okIs (evalInt (wrapEnv 5 0 0) (.binary (.m0 .sub) kRef (lit3 6))) 7
#guard okIs (evalInt (wrapEnv 7 0 0) (.binary (.m0 .add) kRef (lit3 4))) 3
#guard okIs (evalInt (wrapEnv 1 0 0) (.binary (.m0 .sub) kRef (lit3 6))) 3
-- The extractor's `K + 1` is `Resize32(K) + 1`: 32-bit unsigned, no 3-bit wrap…
#guard okIs (evalInt (wrapEnv 7 0 0) (.binary (.m0 .add) (.resize 32 kRef) (.int 1))) 8
-- …and `U - 1` at `U = 0` is 2^32 - 1, not -1 (unsigned 32-bit; the select
-- layer refuses such a label — Icarus and Yosys read it differently).
#guard okIs (evalInt (wrapEnv 0 0 0) (.binary (.m0 .sub) (.resize 32 kRef) (.int 1))) 4294967295
-- `int unsigned UI`: `UI - 1` at 0 is 2^32 - 1 as well.
#guard okIs (evalInt (wrapEnv 0 0 0) (.binary (.m0 .sub) (.paramRef "UI" none) (.int 1))) 4294967295
-- A comparison sizes its operands to each other: `K + 3'd4 > 3'd2` at K = 5
-- compares 1 > 2 (3-bit), the generate-if of probe `ps_wrap2`.
#guard okIs (evalInt (wrapEnv 5 0 0)
  (.binary (.m0 .gt) (.binary (.m0 .add) kRef (lit3 4)) (lit3 2))) 0
-- Bit/part selects of a narrow constant read inside its width only.
#guard okIs (evalInt (wrapEnv 5 0 0) (.bitSel kRef (.int 2))) 1
#guard isLoud (evalInt (wrapEnv 5 0 0) (.bitSel kRef (.int 3)))
#guard okIs (evalInt (wrapEnv 5 0 0) (.partSel kRef (.int 2) (.int 1))) 2
-- `$signed(K)` reinterprets: K = 5 is -3.
#guard okIs (evalInt (wrapEnv 5 0 0) (.cast true kRef)) (-3)
-- A frontend `s<` over an operand typed unsigned is a contradiction: loud.
#guard isLoud (evalInt (wrapEnv 5 0 0) (.binary .slt kRef (lit3 2)))
-- Division by zero reads x: loud.
#guard isLoud (evalInt (wrapEnv 5 0 0) (.binary .div kRef (lit3 0)))
-- The INT path is unchanged: `N - 1` at N = 0 is -1 (32-bit signed).
#guard okIs (evalInt (wrapEnv 0 0 0) (.binary (.m0 .sub) (.paramRef "N" none) (.int 1))) (-1)
#guard (PExpr.binary (.m0 .sub) (.paramRef "N" none) (.int 1)).isInt (wrapEnv 0 0 0)
#guard !(PExpr.binary (.m0 .sub) kRef (.int 1)).isInt (wrapEnv 0 0 0)
-- Typed parameters bind by class: `int` → `vals`, `logic [2:0]` → `nvals`
-- (an override that does not fit is converted: 9 ↦ 1).
private def wrapParams : List PParam :=
  [{ name := "N", type? := some (.packed [⟨.int 31, .int 0⟩] none) },
   { name := "K", type? := some (.packed [⟨.int 2, .int 0⟩] none) },
   { name := "U", type? := some (.packed [⟨.int 31, .int 0⟩] none), signed? := some false }]
#guard (match bindParams {} wrapParams [4, 9, 7] with
  | .ok e => e.vals == [("N", 4)] && e.nvals == [("U", (7, 32, false)), ("K", (1, 3, false))]
  | .error _ => false)
-- Localparams: typed `logic [2:0] L = K + 3'd7` wraps (K = 1 → 0).
-- An untyped `L = K + 3'd7` keeps the expression's own 3-bit type (§6.20.2).
private def lpTyped : PLocalParam :=
  { name := "L", expr := .binary (.m0 .add) kRef (lit3 7),
    type? := some (.packed [⟨.int 2, .int 0⟩] none) }
private def lpUntyped : PLocalParam :=
  { name := "L", expr := .binary (.m0 .add) kRef (lit3 7) }
#guard (match bindLocal (wrapEnv 1 0 0) lpTyped with
  | .ok e => e.nvals.lookup "L" == some (0, 3, false)
  | .error _ => false)
#guard (bindLocal (wrapEnv 0 0 0) lpUntyped matches .error _)
#guard (bindLocal (wrapEnv 1 0 0) lpUntyped matches .error _)

private def lpSignedKeyword : PLocalParam :=
  { name := "LS", expr := .lit (LVec.ofNat 4 8), signed? := some true }
#guard (bindLocal {} lpSignedKeyword matches .error _)
private def pUnsignedKeyword : PParam :=
  { name := "PU", default? := some (.int 1), signed? := some false }
#guard (bindParams {} [pUnsignedKeyword] [1] matches .error _)

/-! ### Constant contexts across parameter points (round 3 repair)

Conversions are transparent to `ctype` (their envelope width is the default
point's); an assignment-like target is supplied by `evalAssign` (and
`evalIntTarget` for an `integer`/`int` one, round 4); a self-determined
root is read at its own width; a root whose tree records an outside target
(`PExpr.pushedTarget`) is loud where that target's reading differs (round
4). Repros `vp_lp2`, `vp_lp`, `fold_lpshr`, `fold_cgrow`, `fold_ovr`,
`rf_lbl`, `rf_int`, `rf_gv`. -/

private def lit8 (v : Nat) : PExpr := .lit (.ofNat 8 v)
-- `localparam logic [N-1:0] L1 = 8'd200 + 8'd100`, sized at N = 4 by slang
-- (`Resize(4, …)`): the carry survives at N = 16, wraps at N = 8.
private def l1 : PExpr := .resize 4 (.binary (.m0 .add) (lit8 200) (lit8 100))
#guard okIs (evalAssign {} 16 l1) 300
#guard okIs (evalAssign {} 8 l1) 44
#guard okIs (evalAssign {} 4 l1) 44   -- the caller's `canonInt 4` makes it 12
#guard okIs (evalAssign {} 8 (.fill .l0)) 0
#guard okIs (evalAssign {} 8 (.fill .l1)) 255
-- `4'd15 << 2` keeps its high bits at a wider target.
#guard okIs (evalAssign {} 16 (.binary .shl (.lit (.ofNat 4 15)) (.int 2))) 60
#guard okIs (evalAssign {} 4 (.binary .shl (.lit (.ofNat 4 15)) (.int 2))) 12
-- `P + 1'b0` (`int P = -3`) into a 40-bit target: P zero-extended past 32.
#guard okIs (evalAssign { vals := [("P", -3)] } 40
  (.resize 8 (.binary (.m0 .add) (.resize 32 (.paramRef "P" none))
    (.resize 32 (.lit (.ofNat 1 0)))))) 4294967293
-- Widened literals are read at their own width where the context is
-- narrower than at the default point (N = 16 there, 8 here): 44 >> 5 = 1.
#guard okIs (evalAssign {} 8 (.binary .shr
  (.binary (.m0 .add) (.resize 16 (lit8 200)) (.resize 16 (lit8 100))) (.int 5))) 1
-- Round 4: a chain of widened non-INT leaves is NO evidence of an outside
-- target (the widths are the default point's widest operand: `SB + 1'b1`
-- is `Resize(8, SB) + Resize(8, 1'b1)` at `N = 8`) — read at its own width
-- here, 44 (repros `rf_lbl`, `rf_gen`, `rf_lp`, `rf_par`)…
#guard okIs (evalInt { nvals := [("U", (200, 8, false))] }
  (.binary (.m0 .add) (.resize 16 (.paramRef "U" none)) (.resize 16 (lit8 100)))) 44
#guard okIs (evalInt { nvals := [("SB", (-1, 4, true))] }
  (.binary (.m0 .add) (.resize 8 (.paramRef "SB" none)) (.resize 8 (.lit (.ofNat 1 1))))) 0
-- …a ROOT conversion is an assignment-like target (a genvar initializer,
-- extractor `_sym_genvar_init`): where its reading (300) differs from the
-- own-width one (44) the root is loud, where they agree it is the value…
#guard isLoud (evalInt { nvals := [("U", (200, 8, false))] }
  (.resize 32 (.binary (.m0 .add) (.paramRef "U" none) (.resize 32 (lit8 100)))))
#guard okIs (evalInt { nvals := [("U", (20, 8, false))] }
  (.resize 32 (.binary (.m0 .add) (.paramRef "U" none) (.resize 32 (lit8 100))))) 120
-- …(`rf_gv`: `U + 1'b1` with a 4-bit `U = 15` is 0 in Icarus, 16 in slang
-- and Yosys; with `U = 3` both give 4), signed too (`S + S`, 4-bit `S = 7`:
-- -2 against 14)…
#guard isLoud (evalInt { nvals := [("U", (15, 4, false))] }
  (.resize 32 (.binary (.m0 .add) (.paramRef "U" none) (.resize 32 (.lit (.ofNat 1 1))))))
#guard okIs (evalInt { nvals := [("U", (3, 4, false))] }
  (.resize 32 (.binary (.m0 .add) (.paramRef "U" none) (.resize 32 (.lit (.ofNat 1 1)))))) 4
#guard isLoud (evalInt { nvals := [("S", (7, 4, true))] }
  (.signedResize 32 (.binary (.m0 .add) (.signedResize 32 (.paramRef "S" none))
    (.signedResize 32 (.paramRef "S" none)))))
#guard okIs (evalInt { nvals := [("S", (-3, 4, true))] }
  (.signedResize 32 (.binary (.m0 .add) (.signedResize 32 (.paramRef "S" none))
    (.signedResize 32 (.paramRef "S" none))))) (-6)
-- …and a value that a genvar's 32-bit `integer` would change is loud
-- (2^32 + 1 at 40 bits, 2^32 - 1 at 32 bits), one that survives is not.
#guard isLoud (evalInt { nvals := [("U", (4294967297, 40, false))] }
  (.resize 32 (.paramRef "U" none)))
#guard isLoud (evalInt { nvals := [("U", (4294967295, 32, false))] }
  (.resize 32 (.paramRef "U" none)))
#guard okIs (evalInt { nvals := [("U", (5, 40, false))] } (.resize 32 (.paramRef "U" none))) 5
-- An INT-class chain widened past 32 bits is NO target by itself — in a
-- value position the width is a sibling signal's (`a + P * 2`, `constAtCtx2`
-- re-evaluates at the operation width): read at its own 32 bits…
#guard okIs (evalInt { vals := [("N", 2147483647)] }
  (.binary (.m0 .add) (.signedResize 40 (.paramRef "N" none)) (.int 1))) (-2147483648)
-- …while an INT-class instance override into a 40-bit typed parameter
-- carries its root conversion (`_sym_override_root`): loud where the 32-bit
-- value overflows, the value where it does not.
#guard okIs (evalInt { vals := [("N", 5)] }
  (.signedResize 40 (.binary (.m0 .add) (.signedResize 40 (.paramRef "N" none)) (.int 1)))) 6
#guard isLoud (evalInt { vals := [("N", 2147483647)] }
  (.signedResize 40 (.binary (.m0 .add) (.signedResize 40 (.paramRef "N" none)) (.int 1))))
-- A self-determined root takes its own width HERE: with an 8-bit U (16
-- bits at the default point) the 16-bit `Resize`s of the literals are no
-- floor, `U + 8'd200 < 8'd50` compares at 8 bits — 100 + 200 wraps to 44.
#guard okIs (evalInt { nvals := [("U", (100, 8, false))] }
  (.binary (.m0 .lt) (.binary (.m0 .add) (.paramRef "U" none) (.resize 16 (lit8 200)))
    (.resize 16 (lit8 50)))) 1
-- An operand wider HERE than the default point's conversion is not
-- truncated: `U > 5` with a 40-bit U = 2^32 is true.
#guard okIs (evalInt { nvals := [("U", (4294967296, 40, false))] }
  (.binary (.m0 .gt) (.resize 32 (.paramRef "U" none)) (.int 5))) 1
-- A negative genvar zero-extended past 32 bits splits the oracles: loud.
#guard isLoud (evalInt (IEnv.bindNVal { vals := [("g", -1)] } "U" 0 40 false)
  (.binary (.m0 .add) (.resize 32 (.genvarRef "g")) (.paramRef "U" none)))
#guard okIs (evalInt { vals := [("g", -1)] }
  (.binary (.m0 .add) (.resize 32 (.genvarRef "g")) (.int 0))) 4294967295
-- Typed localparams bind through `evalAssign`: `logic [N-1:0] L1` at N = 16.
private def lpWide : PLocalParam :=
  { name := "L1", expr := l1,
    type? := some (.packed [⟨.int 15, .int 0⟩] none) }
#guard (match bindLocal {} lpWide with
  | .ok e => e.nvals.lookup "L1" == some (300, 16, false)
  | .error _ => false)
-- Round 4: an `integer`/`int` localparam or parameter default is a 32-bit
-- target (`evalIntTarget`; repros `rf_int`, `rf_ipar`): `U + 1'b1` with a
-- 4-bit `U = 15` is 16, not the 4-bit 0 — with or without the `Squash2` of
-- an `int` target.
private def uPlus1 : PExpr :=
  .binary (.m0 .add) (.paramRef "U" none) (.resize 32 (.lit (.ofNat 1 1)))
private def u15 : IEnv := { nvals := [("U", (15, 4, false))] }
private def int32Ty : PType := .packed [⟨.int 31, .int 0⟩] (some 32)
#guard (evalAssign { nvals := [("P", (-2, 32, true))], stale := ["P"] } 8
    (.binary (.m0 .add) (.paramRef "P" none) (.int 1)) matches .error _)
#guard (match bindLocal u15 { name := "L", expr := uPlus1, type? := some int32Ty } with
  | .ok e => e.vals.lookup "L" == some 16
  | .error _ => false)
#guard (match bindLocal u15 { name := "K", expr := .squash2 32 uPlus1, type? := some int32Ty } with
  | .ok e => e.vals.lookup "K" == some 16
  | .error _ => false)
#guard okIs (PParam.evalDefault u15 { name := "P", type? := some int32Ty } uPlus1) 16
-- An untyped localparam keeps its own type: `(U + 1'b1) >> 1` is 0 at 4 bits.
#guard (match bindLocal u15 { name := "X", expr := .binary .shr uPlus1 (.int 1) } with
  | .ok e => e.nvals.lookup "X" == some (0, 4, false)
  | .error _ => false)

/-! ### Round 5 folds: `Squash2`, declared signedness, untyped wraps

A `Squash2` is transparent to `ctype` (repro `vq_sq2`); a type with a
non-literal bound needs its envelope `signed` (repros `vq_sgn2`,
`vq_sgn3`); an untyped constant whose own-type value wraps is loud
(`evalUntyped`). -/

-- `localparam bit [N-1:0] B1 = (U + 1'b1) >> 1`: slang's `Squash2(32, …)`
-- (the default N = 32) is no floor at N = 4, U = 15 — 0 as in Icarus 12.0
-- and the Yosys 0.53 netlist (it was 8); an `int` target K still reads 8.
private def b1Expr : PExpr :=
  .squash2 32 (.binary .shr uPlus1 (.int 1))
private def bit4Ty : PType := .packed [⟨.int 3, .int 0⟩] none
private def lpB1 : PLocalParam :=
  { name := "B1", expr := b1Expr, type? := some bit4Ty, signed? := some false }
private def lpK : PLocalParam := { name := "K", expr := b1Expr, type? := some int32Ty }
private def pPB : PParam := { name := "PB", type? := some bit4Ty, signed? := some false }
#guard (match bindLocal u15 lpB1 with
  | .ok e => e.nvals.lookup "B1" == some (0, 4, false)
  | .error _ => false)
#guard (match bindLocal u15 lpK with
  | .ok e => e.vals.lookup "K" == some 8
  | .error _ => false)
#guard okIs (PParam.evalDefault u15 pPB b1Expr) 0
-- `logic signed [M-1:0] S`: without the envelope's `signed` the type is
-- loud; with it, the declared signedness at every width (S = -1 at M = 8
-- stays -1, where the default rule read it as 255).
private def tyM : PType := .packed [⟨.binary (.m0 .sub) (.paramRef "M" none) (.int 1), .int 0⟩] none
#guard (declConstType { vals := [("M", 8)] } (some tyM) none matches .error _)
#guard (declConstType { vals := [("M", 32)] } (some tyM) none matches .error _)
#guard (declConstType { vals := [("M", 8)] } (some tyM) (some true) matches .ok (some (8, true)))
#guard (declConstType { vals := [("M", 32)] } (some tyM) (some true) matches .ok none)
#guard (declConstType { vals := [("M", 32)] } (some tyM) (some false) matches .ok (some (32, false)))
#guard (declConstType {} (some int32Ty) none matches .ok none)
private def pMS : List PParam :=
  [{ name := "M", type? := some int32Ty }, { name := "S", type? := some tyM, signed? := some true }]
#guard (match bindParams {} pMS [8, -1] with
  | .ok e => e.nvals.lookup "S" == some (-1, 8, true)
  | .error _ => false)
-- `localparam Y = SB + 1'b1` (untyped, 8-bit SB) keeps the 8-bit
-- self-determined result.  Both wrapping and non-wrapping values use the
-- same §6.20.2 rule, including shifts and arithmetic operators.
private def sbEnv (v : Int) : IEnv := { nvals := [("SB", (v, 8, false))] }
private def yExpr : PExpr :=
  .binary (.m0 .add) (.paramRef "SB" none) (.resize 8 (.lit (.ofNat 1 1)))
#guard (bindLocal (sbEnv 255) { name := "Y", expr := yExpr } matches .error _)
#guard (bindLocal (sbEnv 5) { name := "Y", expr := yExpr } matches .error _)
#guard (PParam.evalDefault (sbEnv 255) { name := "Q" } yExpr matches .error _)
#guard (PParam.evalDefault (sbEnv 5) { name := "Q" } yExpr matches .error _)
#guard okIs (evalUntypedExact (sbEnv 255) (.binary .shl (.paramRef "SB" none) (.int 4))) 240
#guard okIs (evalUntypedExact (sbEnv 255) (.binary .div yExpr (.lit (.ofNat 2 2)))) 0
#guard okIs (evalUntypedExact { vals := [("N", 2147483647)] }
  (.binary (.m0 .add) (.paramRef "N" none) (.int 1))) (-2147483648)

/-! ### Constant widths after the §6.20.2 untyped rule

A `Squash2` under a `Resize` passes the context through (repro `vs_sqn`).
Untyped constants use their final value's own width, independent of Icarus'
lossless-width mode. -/

-- `localparam shortint H1 = (U + 1'b1) >> 1` and `localparam int KI = (UK +
-- 1'b1) >> 1`, with the default point's `Resize(16, Squash2(32, …))` and
-- `Resize(32, Squash2(40, …))`: at a 4-bit `U = 15` the 16- and 32-bit
-- targets are the context, 8 in Icarus 12.0, the Yosys 0.53 netlist and
-- slang (it was 0); `byte Y1 = U + 1'b1` is 16; at a 33-bit operand the
-- operand's own width is the context.
private def h1Expr (w d : Nat) : PExpr := .resize w (.squash2 d (.binary .shr uPlus1 (.int 1)))
private def shortTy : PType := .packed [⟨.int 15, .int 0⟩] (some 16)
private def byteTy : PType := .packed [⟨.int 7, .int 0⟩] (some 8)
private def lpH1 : PLocalParam :=
  { name := "H1", expr := h1Expr 16 32, type? := some shortTy, signed? := some true }
private def lpKI : PLocalParam := { name := "KI", expr := h1Expr 32 40, type? := some int32Ty }
private def lpY1 : PLocalParam :=
  { name := "Y1", expr := .resize 8 (.squash2 32 uPlus1), type? := some byteTy, signed? := some true }
private def pPY : PParam := { name := "PY", type? := some byteTy, signed? := some true }
#guard (match bindLocal u15 lpH1 with
  | .ok e => e.nvals.lookup "H1" == some (8, 16, true)
  | .error _ => false)
#guard (match bindLocal u15 lpKI with
  | .ok e => e.vals.lookup "KI" == some 8
  | .error _ => false)
#guard (match bindLocal u15 lpY1 with
  | .ok e => e.nvals.lookup "Y1" == some (16, 8, true)
  | .error _ => false)
#guard okIs (PParam.evalDefault u15 pPY (h1Expr 8 32)) 8
#guard (match bindLocal { nvals := [("U", (8589934591, 33, false))] } lpH1 with
  | .ok e => e.nvals.lookup "H1" == some (0, 16, true)
  | .error _ => false)
-- Untyped widths: `2 ** SB` (non-INT, a value beyond 64 extra bits at SB =
-- 100), `N + 1` (INT, 33 bits in Icarus) and `2 ** N` (INT, 42 bits in
-- Icarus at N = 40) are loud; `SB >> 1`, `SB == 8'd5` are not.
#guard okIs (evalUntypedExact (sbEnv 100) (.binary .pow (.int 2) (.paramRef "SB" none))) 0
#guard okIs (evalUntypedExact { vals := [("N", 5)] } (.binary (.m0 .add) (.paramRef "N" none) (.int 1))) 6
#guard okIs (evalUntypedExact { vals := [("N", 8)] } (.binary .pow (.int 2) (.paramRef "N" none))) 256
#guard okIs (evalUntypedExact (sbEnv 6) (.binary .shr (.paramRef "SB" none) (.int 1))) 3
#guard okIs (evalUntypedExact (sbEnv 5) (.binary (.m0 .eq) (.paramRef "SB" none) (lit8 5))) 1

/-! ### Left shifts and the `Squash2` own-width gate

An untyped constant with a LEFT shift uses its final value's own width.
Icarus' lossless-width result is covered by the declared oracle-deviation row. A 2-state target narrower than its initializer whose `Squash2`
operand is undefined at its OWN width stays loud (round 6 FOLDS verifier
major 4, repro `vw_sqd`): `localparam shortint H1 = 4'd8 / (U + 1'b1)` at
a 4-bit `U = 15` divides by zero at U's 4 bits (the round 5 reading) and
not at the 16-bit context (round 6's). -/

private def nEnv (n : Int) : IEnv := { vals := [("N", n)] }
private def oneShlN : PExpr := .binary .shl (.int 1) (.paramRef "N" none)
#guard okIs (evalUntypedExact (nEnv 8) oneShlN) 256
#guard okIs (evalUntypedExact (nEnv 40) oneShlN) 0
#guard okIs (evalUntypedExact (nEnv 8) (.binary .ashl (.int 1) (.paramRef "N" none))) 256
#guard isLoud (evalUntypedExact (nEnv 8) (.binary (.m0 (.shl false)) (.int 1) (.paramRef "N" none)))
#guard okIs (evalUntypedExact (nEnv 8) (.binary (.m0 .or) oneShlN (.int 1))) 257
#guard okIs (evalUntypedExact (nEnv 8) (.binary .div oneShlN (.int 2))) 128
#guard okIs (evalUntypedExact (nEnv 8) (.binary (.m0 .div) oneShlN (.int 2))) 128
#guard isLoud (evalUntypedExact (nEnv 8) (.binary (.m0 (.pow false false)) (.int 2) (.paramRef "N" none)))
#guard okIs (evalUntypedExact (nEnv 8) (.binary .shr (.int 256) (.paramRef "N" none))) 1
private def sqDiv : PExpr := .binary .div (.resize 32 (.lit (.ofNat 4 8))) uPlus1
private def lpSqD : PLocalParam :=
  { name := "H1", expr := .resize 16 (.squash2 32 sqDiv), type? := some shortTy, signed? := some true }
#guard (bindLocal u15 lpSqD matches .error _)
#guard (match bindLocal { nvals := [("U", (7, 4, false))] } lpSqD with
  | .ok e => e.nvals.lookup "H1" == some (1, 16, true)
  | .error _ => false)
#guard (bindLocal u15 { lpSqD with expr := .signedResize 16 (.squash2 32 sqDiv) } matches .error _)
-- The squash2-free twin is unchanged (0 at the 16-bit context, as before).
#guard (match bindLocal u15 { lpSqD with expr := .resize 16 sqDiv } with
  | .ok e => e.nvals.lookup "H1" == some (0, 16, true)
  | .error _ => false)

/-! Generate guards use integer arithmetic even for vector-shift syntax. -/
private def guardEnv : IEnv := { vals := [("i", 3), ("l", 1)] }
private def guardShift : PExpr :=
  .binary (.m0 .eq)
    (.binary (.m0 .and)
      (.binary (.m0 (.shr false)) (.genvarRef "i") (.genvarRef "l"))
      (.int 1)) (.int 1)
#guard (match evalGenGuard guardEnv guardShift with | .ok v => v == 1 | .error _ => false)
#guard (match evalGenGuard guardEnv (.binary (.m0 (.shl false)) (.int 1) (.genvarRef "l")) with
  | .ok v => v == 2
  | .error _ => false)

/-! Signed guard regression. -/
private def guardSignedEnv : IEnv := { nvals := [("N", (5, 32, true))] }
private def guardSignedExpr : PExpr :=
  .binary (.m0 .ne) (.binary (.m0 .and)
    (.binary (.m0 .sub) (.paramRef "N" none) (.int 6)) (.int 1)) (.int 0)
#guard (evalGenGuard guardSignedEnv guardSignedExpr).toOption == some 1

/-! ### Constant functions and package constants: unit rows

Hand-built rows for `evalVec`, `constCallAt` and the package binder. The
source-level rows, with the reference simulator's values, are in
`Examples/system-verilog/sem2/package_const_eval/`. -/

private def litB (s : String) : PExpr := .lit (LVec.lit s)
private def vecIs (r : Except String LVec) (s : String) : Bool :=
  match r with
  | .ok v => v.toBinString == s
  | .error _ => false
private def refuses {α : Type} (r : Except String α) (part : String) : Bool :=
  match r with
  | .ok _ => false
  | .error m => (m.splitOn part).length > 1

-- `evalVec` is `evalAt` wherever `evalAt` answers (here at 65 bits, signed and unsigned).
#guard ((evalVec {} true (65, false) (.binary (.m0 .add) (litB "1111") (litB "0001"))).toOption.map (·.toNat?)) ==
  ((evalAt {} (65, false) (.binary (.m0 .add) (litB "1111") (litB "0001"))).toOption.map (fun v => some v.toNat))
#guard vecIs (evalVec {} true (6, true) (.cast true (litB "10"))) "111110"
#guard vecIs (evalVec {} true (6, false) (.cast true (litB "10"))) "000010"
-- x and z bits move through literals, concatenation, replication, selects and conversions.
#guard vecIs (evalVec {} true (8, false) (litB "1x0z")) "00001x0z"
#guard vecIs (evalVec {} true (8, false) (.concat [litB "1x", litB "0z", litB "01", litB "zx"])) "1x0z01zx"
#guard vecIs (evalVec {} true (4, false) (.partSel (litB "1x0z01zx") (.int 5) (.int 2))) "0z01"
#guard vecIs (evalVec {} true (1, false) (.bitSel (litB "1x0z") (.int 2))) "x"
#guard vecIs (evalVec {} true (6, false) (.repl (.int 3) (litB "z1"))) "z1z1z1"
#guard vecIs (evalVec {} true (6, true) (.cast true (litB "x1"))) "xxxxx1"
#guard vecIs (evalVec {} true (4, false) (.squash2 4 (litB "1x0z"))) "1000"
#guard vecIs (evalVec {} true (4, false) (.ternary (litB "1") (litB "x01z") (litB "0000"))) "x01z"
#guard vecIs (assignVec {} true 5 (.fill .lx)) "xxxxx"
#guard vecIs (assignVec {} true 3 (litB "1x0z1")) "0z1"
-- An operator on an x/z operand, and an x condition, are refused, not approximated.
#guard refuses (evalVec {} true (4, false) (.binary (.m0 .add) (litB "1x0z") (litB "0001"))) "x/z"
#guard refuses (evalVec {} true (4, false) (.ternary (litB "x") (litB "0001") (litB "0010"))) "x/z"
-- An assignment pattern arrives as a concatenation of conversions to the member widths: each
-- operand is assigned to its member (truncated, or extended by its own sign), in a package.
#guard vecIs (evalPart {} true (.concat [.resize 4 (litB "10101100"), .signedResize 4 (.cast true (litB "10")),
    .resize 2 (.fill .lx)])) "11001110xx"
#guard vecIs (assignVec {} true 12 (.concat [.resize 4 (litB "10101100"), litB "0001"])) "000011000001"
-- Outside a package that width is the default point's: refused where it differs from the operand's.
#guard refuses (evalPart {} false (.concat [.resize 4 (.binary (.m0 .add) (litB "10101100") (litB "00000000")), litB "0001"])) "outside a package"
-- A literal operand has one width at every point: its recorded conversion is applied.
#guard vecIs (evalPart {} false (.concat [.resize 4 (litB "10101100"), litB "0001"])) "11000001"
#guard vecIs (evalPart {} false (.concat [.resize 8 (litB "10101100"), litB "0001"])) "101011000001"
#guard refuses (evalVec {} true (16, false)
    (.binary (.m0 .add) (.concat [.resize 4 (litB "10101100"), litB "0001"]) (litB "1"))) "assignment pattern"
-- A select of a function variable reads the window its declared range gives.
-- The index is an OFFSET (the frontend has translated a literal label of a shifted or reversed
-- range): offset 7 of `[0:7]` is the label 0, the most significant bit.
#guard (selWindow 16 [(1, 0), (7, 0)] false 1 1).toOption == some (8, 8, [(7, 0)])
#guard (selWindow 8 [(0, 7)] true 7 7).toOption == some (7, 1, [])
#guard (selWindow 12 [(11, 4)] true 7 7).toOption == some (7, 1, [])
#guard (selWindow 8 [(0, 7)] true 7 6).toOption == some (6, 2, [])
-- A computed index is admitted only on `[m:0]`; out of range and reversed bounds are refused.
#guard (selWindow 8 [(0, 7)] false 7 7).toOption == none
#guard (selWindow 8 [(7, 0)] false 5 5).toOption == some (5, 1, [])
#guard (selWindow 8 [(7, 4)] true 4 4).toOption == none
#guard (selWindow 8 [(7, 0)] true 2 5).toOption == none

private def u32 : PType := .packed [⟨.int 31, .int 0⟩] (some 32)
private def fIn (n : String) : PDecl := { name := n, type := u32, isInput := true }
/-- `sum(n)`: a local, a `for` loop, `return`. -/
private def fnSum : PFunction :=
  { name := "sum", formals := [fIn "n"], returnType := u32, body := .unsupported "body" "",
    stmts := some
      [ .decl "t" u32 false true none,
        .forLoop [.decl "i" u32 false true (some (.int 0))]
          (.binary (.m0 .lt) (.ident "i") (.ident "n")) [.incDec "i" true]
          (.block [.assign (.ident "t") (.binary (.m0 .add) (.ident "t") (.ident "i"))]),
        .ret (some (.ident "t")) ] }
/-- A loop that never ends. -/
private def fnSpin : PFunction :=
  { name := "spin", formals := [], returnType := u32, body := .unsupported "body" "",
    stmts := some [.forLoop [] (.int 1) [] (.block []), .ret (some (.int 0))] }
/-- `rec(n) = rec(n)`. -/
private def fnRec : PFunction :=
  { name := "rec", formals := [fIn "n"], returnType := u32,
    body := .functionCall "rec" [.ident "n"] }
/-- A `case` with an x item, the result assigned to the function name, no `return`. -/
private def fnCase : PFunction :=
  { name := "dec", formals := [{ name := "s", type := .packed [⟨.int 1, .int 0⟩] (some 2) }],
    returnType := .packed [⟨.int 3, .int 0⟩] (some 4), body := .unsupported "body" "",
    stmts := some
      [ .caseStmt (.ident "s")
          [([litB "00"], .assign (.ident "dec") (litB "0001")),
           ([litB "1x"], .assign (.ident "dec") (litB "0100"))]
          (some (.assign (.ident "dec") (litB "1000"))) ] }
/-- A table `[3:0][7:0]` filled element by element, then one element read back. -/
private def fnTab : PFunction :=
  { name := "tab", formals := [fIn "k"], returnType := .packed [⟨.int 7, .int 0⟩] (some 8),
    body := .unsupported "body" "",
    stmts := some
      [ .decl "t" (.packed [⟨.int 3, .int 0⟩, ⟨.int 7, .int 0⟩] (some 32)) false false none,
        .assign (.ident "t") (.fill .l0),
        .forLoop [.decl "i" u32 false true (some (.int 0))]
          (.binary (.m0 .lt) (.ident "i") (.resize 32 (.int 4))) [.incDec "i" true]
          (.assign (.bitSel "t" (.ident "i"))
            (.binary (.m0 .add) (.ident "i") (litB "00010000"))),
        .ret (some (.bitSel (.ident "t") (.ident "k"))) ] }
private def s32 : PType := .packed [⟨.int 31, .int 0⟩] (some 32)
/-- `readsK(x) = x + K`, `K` a constant of the declaring scope. -/
private def fnReadsK : PFunction :=
  { name := "readsK", formals := [{ name := "x", type := s32, isSigned := true, isInput := true }],
    returnType := s32, isSigned := true, body := .binary (.m0 .add) (.cast true (.ident "x")) (.paramRef "K" none) }
/-- `sum` with an `int` result (the INT class of `evalInt`). -/
private def fnSumS : PFunction := { fnSum with name := "sumS", isSigned := true }
private def fnEnv : IEnv := { functions := [fnSum, fnSpin, fnRec, fnCase, fnTab, fnSumS] }
private def callIs (e : PExpr) (s : String) : Bool :=
  match constCalls fnEnv e with
  | .ok (.cast _ (.lit v)) => v.toBinString == s
  | _ => false

#guard callIs (.functionCall "sum" [.int 5]) "00000000000000000000000000001010"
#guard refuses (constCalls fnEnv (.functionCall "spin" [])) "elaboration budget"
#guard refuses (constCalls fnEnv (.functionCall "rec" [.int 1])) "recursive constant function"
#guard refuses (constCalls fnEnv (.functionCall "nope" [])) "function 'nope' in a constant context"
-- The unselected arm of a known `?:` is not evaluated: its recursive call does not refuse the value.
#guard (match constCalls fnEnv (.ternary (litB "1") (.functionCall "sum" [.int 3]) (.functionCall "rec" [.int 1])) with
  | .ok e => (evalSized fnEnv e).toOption == some 3
  | .error _ => false)
#guard callIs (.functionCall "dec" [litB "00"]) "0001"
-- §12.5.1: a `case` compares bit for bit, so `2'b1x` matches only `2'b1x`.
#guard callIs (.functionCall "dec" [litB "1x"]) "0100"
#guard callIs (.functionCall "dec" [litB "10"]) "1000"
#guard callIs (.functionCall "tab" [.int 2]) "00010010"
#guard refuses (constCalls fnEnv (.functionCall "tab" [.int 4])) "out of range"
-- An explicit size cast: the operand at its own width, then truncated or padded (with its sign).
#guard callIs (.functionCall sizeCastName [.int 4, litB "10101011"]) "1011"
#guard callIs (.functionCall sizeCastName [.int 8, .cast true (litB "1011")]) "11111011"
#guard callIs (.functionCall sizeCastName [.int 8, .functionCall sizeCastName [.int 4, litB "10101011"]]) "00001011"
-- A function body is evaluated in the declaring scope: the generate scope's `K` (the leading
-- entry, recorded by `scopedVals`) is not the `K` the function reads.
#guard (match constCalls { fnEnv with functions := [fnReadsK], vals := [("K", 100), ("K", 1)], scopedVals := 1 }
    (.functionCall "readsK" [.int 1]) with
  | .ok (.cast _ (.lit v)) => v.toNat? == some 2
  | _ => false)
-- Without that record the shadowing is refused, never resolved to the inner binding.
#guard refuses (constCalls { fnEnv with functions := [fnReadsK], vals := [("K", 100), ("K", 1)] }
    (.functionCall "readsK" [.int 1])) "bound more than once"
-- A signed package constant read by `evalInt` is negative (it was read as its unsigned bits).
#guard (evalInt ((({} : IEnv).bindPackageConst "p" "M" (LVec.ofInt 32 (-3)) 32 true)) (.paramRef "M" (some "p"))).toOption
  == some (-3)
-- A converted concatenation operand whose width is not its operand's own is refused by `evalAt`.
#guard refuses (evalAt {} (12, false) (.concat [.resize 4 (.binary (.m0 .add) (litB "10101100") (litB "00000000")), litB "0001"])) "Concat:converted-operand"
-- A call as a whole integer constant (a dimension bound) goes through the same evaluator.
#guard (evalInt fnEnv (.binary (.m0 .sub) (.functionCall "sumS" [.int 5]) (.int 1))).toOption == some 9
-- A nested call inside arithmetic, through `bindLocalC`.
private def lpCalls : PLocalParam :=
  { name := "K", expr := PExpr.binary (.m0 .add) (.functionCall "sum" [.functionCall "sum" [.int 3]]) (.int 1),
    type? := some u32, signed? := some false }
#guard ((bindLocalC fnEnv lpCalls).toOption.map (·.nvals.lookup "K")) == some (some (4, 32, false))
#guard !(PExpr.hasCall (.binary (.m0 .add) (.int 1) (.paramRef "N" none)))

private def pkgP (n : String) (e : PExpr) (ty : Option PType := some u32) : String × PParam :=
  ("p", { name := n, default? := some e, type? := ty, signed? := some false })
private def pkgRef (n : String) : PExpr := .paramRef n (some "p")
private def pkgVal (ps : List (String × PParam)) (n : String) : Option (String × Nat × Bool) :=
  ((bindPackageParamsState { functions := [fnSum, fnRec] } ps).env.packageFVal "p" n).map
    fun (v, w, s) => (v.toBinString, w, s)

-- Dependency order, whatever the declaration order: C reads B (through a call), B reads A.
private def pkgChain : List (String × PParam) :=
  [pkgP "C" (.functionCall "sum" [pkgRef "B"]), pkgP "B" (.binary (.m0 .add) (pkgRef "A") (.int 1)),
   pkgP "A" (.int 3)]
#guard pkgVal pkgChain "C" == some ("00000000000000000000000000000110", 32, false)
#guard packageParamRefusals { functions := [fnSum, fnRec] } pkgChain == []
-- A cycle is refused, by name; a constant outside it is bound.
private def pkgLoop : List (String × PParam) :=
  [pkgP "X" (pkgRef "Y"), pkgP "Y" (pkgRef "X"), pkgP "Z" (.int 1)]
#guard pkgVal pkgLoop "X" == none && pkgVal pkgLoop "Z" != none
#guard packageParamRefusals {} pkgLoop ==
  ["package parameter 'p::X' is not bound: package constant dependency cycle among: p::X, p::Y",
   "package parameter 'p::Y' is not bound: package constant dependency cycle among: p::X, p::Y"]
-- A constant that cannot be evaluated is left unbound with its reason, and so is its reader.
private def pkgBad : List (String × PParam) :=
  [pkgP "R" (.functionCall "rec" [.int 1]), pkgP "S" (pkgRef "R"), pkgP "T" (.int 2)]
#guard pkgVal pkgBad "R" == none && pkgVal pkgBad "S" == none && pkgVal pkgBad "T" != none
#guard (packageParamRefusals { functions := [fnSum, fnRec] } pkgBad).length == 2
-- Width-exact at the declared type: 65 bits unsigned, 33 bits signed, an x/z literal, an untyped int.
private def pkgWide : List (String × PParam) :=
  [("p", { name := "W", default? := some (.binary .shl (.resize 65 (.int 1)) (.int 64)),
           type? := some (.packed [⟨.int 64, .int 0⟩] (some 65)), signed? := some false }),
   ("p", { name := "N", default? := some (.unary (.m0 .neg) (.int 2)),
           type? := some (.packed [⟨.int 32, .int 0⟩] (some 33)), signed? := some true }),
   pkgP "X" (litB "1x0z") (some (.packed [⟨.int 7, .int 0⟩] (some 8))),
   pkgP "U" (.int (-1)) none]
#guard pkgVal pkgWide "W" == some ("1" ++ "".pushn '0' 64, 65, false)
#guard pkgVal pkgWide "N" == some ("".pushn '1' 32 ++ "0", 33, true)
#guard pkgVal pkgWide "X" == some ("00001x0z", 8, false)
#guard pkgVal pkgWide "U" == some ("".pushn '1' 32, 32, true)
#guard ((bindPackageParamsState {} pkgWide).env.packageVal "p" "U") == some (-1)
-- The package table joins the differential: a `resolved` that disagrees is reported.
#guard checkPackageParams (bindPackageParamsState {} pkgWide).env
    [("p", { name := "U", resolved? := some (-1) }), ("p", { name := "N", resolved? := some 5 })] ==
  ["package parameter 'p::N': ours -2 ≠ resolved 5"]
-- Bit for bit, with x and z, and with the width and the signedness.
#guard checkPackageParams (bindPackageParamsState {} pkgWide).env
    [("p", { name := "X", resolvedBits? := some "00001x0z", resolvedSigned? := some false }),
     ("p", { name := "U", resolvedBits? := some ("".pushn '1' 32), resolvedSigned? := some true })] == []
#guard checkPackageParams (bindPackageParamsState {} pkgWide).env
    [("p", { name := "X", resolvedBits? := some "00001x00", resolvedSigned? := some true }),
     ("p", { name := "U", resolvedBits? := some ("".pushn '1' 33) })] ==
  ["package parameter 'p::X': ours 00001x0z ≠ resolved 00001x00",
   "package parameter 'p::X': ours is unsigned, resolved signed",
   "package parameter 'p::U': ours 11111111111111111111111111111111 ≠ resolved 111111111111111111111111111111111",
   "package parameter 'p::U': our width 32 ≠ resolved 33"]
-- A 2-state member keeps no x: `'x` converted to a 2-state width is 0 (§6.11.2).
#guard vecIs (evalPart {} true (.concat [.squash2 2 (.fill .lx), .resize 2 (.fill .lx), litB "1"])) "00xx1"

end LeanModels.Sv
