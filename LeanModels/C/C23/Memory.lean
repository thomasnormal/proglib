import LeanModels.C.Ast
import LeanModels.C.C23.Value
import LeanModels.Core.Outcome

/-!
# §6.2.4 / §6.2.6.1 / §6.3.2 / §6.5.3-§6.5.4 — objects, pointers, bytes — M2 inch 2

The memory model: what an object is, what a pointer IS, and the three
structural refusals every access goes through. **No interpreter, no
world, no fuel** — every operation here is a PURE function over `Mem`,
which is what lets inch 3 lift them into the monad stack
(`docs/c-semantics-design.md` §4.1a) without rewriting one of them.

Citations are C23 (N3220) by clause and paragraph; refusals name their
Annex J.2 index. The convention is `docs/c23-spec-mirror.md`.

## The decision this file exists for

**A pointer is `(object, offset)` with provenance. There is no integer
address to lose provenance to.** Two measurements force it and neither
can be retrofitted:

* **31 sites take `&` of an automatic object** and 20 take `&` of a
  subobject, so a C local cannot be an environment binding the way the
  Python tier's is. *(The charter published 86 for years; the guard that
  produced it could not see storage duration. §L72.)*
* **`realloc` MOVES the transposition table** (sunfish.c L453-454, on the
  search path), so the corpus exercises PROVENANCE TRANSFER in its
  hottest data structure — old object dies, a fresh object receives the
  bytes. `Addr := Nat` cannot express that; `(obj, off)` can.

## What the census changed about the shape

Inch 2's own census asked which operations actually make and use
pointers, and the answer reordered the file:

| produces | sites | | consumes | sites |
| --- | ---: | --- | --- | ---: |
| **array-to-pointer decay** (§6.3.2.1p3) | **405** | | lvalue conversion (§6.3.2.1p2) | 1837 |
| function-to-pointer decay | 307 | | `p->f` (§6.5.3.4) | **226** |
| `&` (§6.5.4.2p3) | 106 | | `a[i]` (§6.5.3.2) | 328 |
| null pointer constant (§6.3.2.3p3) | 110 | | `x.f` | 184 |
| `void*` ↔ `T*` | 52 | | `*p` (§6.5.4.2p4) | **24** |

**Decay outnumbers `&` four to one, and `->` outnumbers `*` nine to
one.** So `decay` and `member` are stated first and gated hardest; `*`
gets the same treatment because the standard defines it that way, not
because the corpus leans on it.
-/

namespace LeanModels.C.C23

open LeanModels.Clang (QualType)

open LeanModels.C (CType)

/-! ## §6.2.4 Storage durations of objects -/

/-- C23 §6.2.4: how long an object lives.

`static` (p3) — the whole program execution. `automatic` (p6) — "from
entry into the block with which it is associated until execution of that
block ends in any way". `allocated` (§7.24.3p1) — "from the allocation
until the deallocation".

The three are distinguished because their INDETERMINATE reads carry
different Annex J entries: `J.2(11)` for automatic, `J.2(185)` for
`malloc`ed. Pooling them would make the scoreboard unreadable. -/
inductive Duration where
  | static_
  | automatic
  | allocated
deriving Repr, Inhabited, BEq, DecidableEq

/-! ## §6.3.2.3 Pointers

`ObjId`, `Ptr`, `Ptr.null` and `Ptr.toObject` now live in `Value.lean`: a
pointer is a VALUE, and inch 3 is the first consumer that must produce
one. `docs/c-semantics-design.md` §1.1 always said so. -/

/-! ## §6.2.6.1 Representations of types — the byte lattice -/

/-! One byte of an object's representation.

C23 §6.2.6.1p2-p4 gives every object a representation as a sequence of
`CHAR_BIT`-bit bytes; the lattice adds the two states the standard talks
about but a concrete byte cannot express.

Per-BYTE and not per-object, because `setup_fen` declares `Pos p;` then
`memcpy(p.b, board, 120)` (sunfish.c L1130), leaving `p.score`, `p.ep`,
`p.kp` and `p.h` indeterminate while `p.b` is fully determined. A model
that refused any read from a partly-initialized object would refuse the
corpus; one that allowed it would invent values. -/
/-! ## The refusal causes

`docs/c23-goal.md` §3.1 fixed three causes that must never be pooled,
because they retire on completely different schedules. This file's faults
are all of the middle kind — **UB, which never retires: it is the
product** — but the `Cause` projection is defined here so the scorer at
inch 6 reads it off the refusal rather than re-deriving it. -/

/-- The memory model's undefined-behavior classes.

Each names its **Annex J.2 index** — C23 numbers J.2 `(1)`-`(221)`, which
C17 did not — and the normative clause where the rule actually lives.
Both, because Annex J is informative and in one place demonstrably wrong
(`docs/c23-spec-mirror.md` §3.3). -/
inductive MemFault where
  /-- **`J.2(39)`**, §6.5.4.2p4: the operand of unary `*` has an invalid
  value. (Annex J says "invalid value", never "null".) -/
  | nullDeref (off : Int)
  /-- **`J.2(9)`/`J.2(10)`**, §6.2.4p2: an object is referred to outside
  its lifetime, or the value of a pointer to it is used. The `Duration`
  says which story it is — a dead automatic, or freed storage. -/
  | deadObject (o : ObjId) (dur : Duration)
  /-- **`J.2(46)`**, §6.5.3.2 / **`J.2(43)`**, §6.5.7p9: an access or a
  formed pointer leaves the object. Structural here: the offset is
  checked against the size, so no sanitizer is needed to see it. -/
  | outOfBounds (o : ObjId) (off : Int) (want : Nat) (size : Nat)
  /-- **`J.2(11)`**, §6.2.4: the value of an object with AUTOMATIC
  storage duration is used while its representation is indeterminate. -/
  | indetAutomatic (o : ObjId) (off : Nat)
  /-- **`J.2(185)`**, §7.24.3.6p2: the value of a `malloc`ed object is
  used before it is written. A DISTINCT entry from `J.2(11)` — the
  annex separates them and so does this model. -/
  | indetAllocated (o : ObjId) (off : Nat)
  /-- **`J.2(12)`**, §6.2.6.1p5: a non-value representation is read by an
  lvalue expression that does not have character type — here, a torn
  pointer, or a pointer representation read as an integer. -/
  | nonValueRepresentation (o : ObjId) (off : Nat)
  /-- **`J.2(184)`**, §7.24.3.3 / §7.24.3.7: `free` or `realloc` given a
  pointer that no allocation returned, or one already deallocated. -/
  | freeUnmatched (p : Ptr)
  /-- **NO J.2 ENTRY EXISTS.** §7.24.3.7p3 — "or if the size is zero, the
  behavior is undefined" — is new in C23, and Annex J was not updated to
  match. Verified by exhaustive search of all 221 entries. The gap is
  carried in the type, not in a comment: `j2` returns `none` here. -/
  | reallocZero (p : Ptr)
  /-- **`J.2(36)`**, §6.5.1p6-p7: an object's stored value is accessed by
  an lvalue of a type that is not allowable for its effective type.
  Measured: the corpus has ZERO punning casts and ZERO unions, which is
  exactly the condition under which this wall is cheap to install
  correctly and expensive to install later — and no sanitizer on either
  development host detects a strict-aliasing violation, so without it the
  project has no instrument that would ever notice one. -/
  | effectiveType (o : ObjId) (off : Nat) (used : CType) (eff : CType)
  /-- **`J.2(45)`**, §6.5.9p6: pointers into DIFFERENT objects compared
  with a relational operator. Note the asymmetry with `==`, which
  §6.5.10p7 leaves fully DEFINED across unrelated objects — same clause
  family, opposite verdicts. -/
  | relationalAcrossObjects (a b : Ptr)
deriving Repr, Inhabited, BEq

namespace MemFault

/-- The Annex J.2 index for this fault, when one exists.

**`none` is a finding, not a hole.** `reallocZero` is undefined by
§7.24.3.7p3 and has no annex entry at all; returning an `Option` keeps
that gap where a reader will trip over it instead of where a comment
would be skimmed. -/
def j2 : MemFault → Option String
  | .nullDeref _ => some "J.2(39)"
  | .deadObject _ .allocated => some "J.2(10)"
  | .deadObject _ _ => some "J.2(9)"
  | .outOfBounds .. => some "J.2(46)"
  | .indetAutomatic .. => some "J.2(11)"
  | .indetAllocated .. => some "J.2(185)"
  | .nonValueRepresentation .. => some "J.2(12)"
  | .freeUnmatched _ => some "J.2(184)"
  | .reallocZero _ => none                      -- §7.24.3.7p3; the annex has none
  | .effectiveType .. => some "J.2(36)"
  | .relationalAcrossObjects .. => some "J.2(45)"

/-- The normative clause, which every fault HAS even where J.2 does not. -/
def clause : MemFault → String
  | .nullDeref _ => "6.5.4.2p4"
  | .deadObject _ .allocated => "7.24.3"
  | .deadObject _ _ => "6.2.4p2"
  | .outOfBounds .. => "6.5.7p9"
  | .indetAutomatic .. => "6.2.4"
  | .indetAllocated .. => "7.24.3.6p2"
  | .nonValueRepresentation .. => "6.2.6.1p5"
  | .freeUnmatched _ => "7.24.3.3"
  | .reallocZero _ => "7.24.3.7p3"
  | .effectiveType .. => "6.5.1p6"
  | .relationalAcrossObjects .. => "6.5.9p6"

end MemFault

/-- A refusal that rides in `ExceptT`, with its cause kept structural.

Two of `docs/c23-goal.md` §3.1's three causes live here, with the UB one
split by layer — the value rules (`Value.lean`) and the memory rules
(this file) both produce undefined behavior and both must stay separable
for diagnosis while pooling identically for scoring.

**The third cause, `unsupported`, is NOT here: it lives in `Halt`**, per
the family ruling at `docs/family-architecture.md` §3.4. Uncatchability
belongs to the definition rather than to a per-language proof
obligation. -/
inductive Refusal where
  | valueUB (u : UB)
  | memUB (f : MemFault)
  | libc (name : String)
  /-- `abort()` is a terminal program outcome, not a library refusal.  It
  stays in the inner channel so expression evaluation can short-circuit, and
  `EvalM.verdict` exposes it as `Outcome.aborted`. -/
  | aborted
deriving Repr, Inhabited, BEq

/-- The result of a memory operation. `Except` rather than a bespoke sum,
because inch 3's stack is Core's `SemMWith` — `ExceptT` over `StateT` over `Loud` — the
STATE-RETAINING order, which the `mvcgen` pilot proved by `rfl` is the
one that does not discard the world on a raise — and an operation written
against `Except Refusal` today needs no adapter tomorrow
(`docs/c-semantics-design.md` §4.1a).

These operations take and return `Mem` explicitly rather than living in a
state monad, which is what makes the lift a lift rather than a rewrite. -/
abbrev MRes (α : Type) := Except Refusal α

theorem mres_map_error_bind {α β : Type} (g : α → β) (e : Refusal)
    (k : β → MRes α) :
    ((Except.map g (.error e) >>= k) : MRes α) = .error e := by
  rfl

theorem mres_map_bind_congr {α β γ : Type} (g : α → β) (f : β → γ)
    (x : MRes α) (k : α → MRes β) (k' : β → MRes γ)
    (hk : ∀ a, k' (g a) = (k a).map f) :
    ((x.map g) >>= k') = ((x >>= k).map f) := by
  cases x with
  | error e => rfl
  | ok a => exact hk a

/-- Core Lean gives `Except` no `BEq`, and every gate in
`Examples/c/sunfish/memory.lean` compares one. SCOPED, so it does not
leak into the other lanes: it is generic plumbing, and lifting it to
shared substrate is the architecture lane's call once a second consumer
exists — parking a global instance here to serve one lane is what the
lift-don't-copy law forbids. -/
scoped instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-! ## Objects and memory -/

/-- One object: its size in bytes, its lifetime, and its representation.

`effTy` is per-byte per C23 §6.5.1p6 — "the effective type of an object
for an access to its stored value is the declared type of the object, if
any". `none` is the *no declared type* case, which is exactly allocated
storage (footnote 84), and a store through a non-character lvalue is what
gives it one. -/
structure CObj where
  dur : Duration
  /-- Is the object inside its lifetime? A dead object is NOT removed —
  it becomes a tombstone, so a pointer to it stays a well-formed VALUE
  and `J.2(10)` is detectable instead of being a segfault. -/
  live : Bool
  bytes : List CByte
  effTy : Option CType
deriving Repr, Inhabited, BEq

/-- The object's size in bytes. **Computed, not carried.** An object that
stored its size beside its representation could disagree with itself, and
every lemma below would need a well-formedness side condition saying it
does not. `List.length` is that invariant, discharged by construction. -/
def CObj.size (c : CObj) : Nat := c.bytes.length

/-- The object store. Objects are only ever appended, never removed, so
an `ObjId` is stable for the whole execution and provenance never
dangles into a reused slot. -/
structure Mem where
  objs : List CObj
  /-- Parser-native effective-type observations for declaration-backed
  objects. The object representation remains separate from this identity
  table, so legacy envelopes can keep using `CObj.effTy`. -/
  structuredTypes : List (ObjId × QualType) := []
  /-- Bytes emitted by the modeled stdout stream.  This is part of the
  execution world, not an object with pointer provenance. -/
  stdout : List CByte := []
  /-- Abstract `va_list` cursors. Keys are the parser-allocated object ids;
  the representation deliberately contains no ABI addresses or widths. -/
  vaCursors : List (ObjId × List CVal) := []
  /-- Block-scoped compound literals are one parser node's automatic object
  per enclosing block entry (§6.5.2.5p5).  The identity table lets repeated
  loop execution reuse that object instead of fabricating a fresh address. -/
  compoundObjects : List (CSpan × ObjId) := []
  /-- Concrete placements are tracked separately from provenance.  They are
  supplied by the allocation oracle and never authorize an access; only the
  object id in `Ptr.obj` does that. -/
  placements : List (ObjId × Nat) := []
deriving Repr, Inhabited, BEq

namespace Mem

def CObj.renameAddress (resolve : ObjId → Nat) (c : CObj) : CObj :=
  { c with bytes := c.bytes.map (CByte.renameAddress resolve) }

@[simp] theorem CObj_renameAddress_size
    (resolve : ObjId → Nat) (c : CObj) :
    (CObj.renameAddress resolve c).size = c.size := by
  simp [CObj.renameAddress, CObj.size]

/-! The representation-level memory rename used by the evaluator relation.
Provenance keys and parser-native type rows stay fixed while concrete
placements and every stored pointer representation follow `resolve`. -/
def renameAddresses (resolve : ObjId → Nat) (m : Mem) : Mem :=
  { m with
    objs := m.objs.map (CObj.renameAddress resolve)
    stdout := m.stdout.map (CByte.renameAddress resolve)
    vaCursors := m.vaCursors.map (fun (o, vs) => (o, vs.map (CVal.renameAddress resolve)))
    placements := m.placements.map (fun (o, _) => (o, resolve o)) }

@[simp] theorem renameAddresses_structuredTypes
    (resolve : ObjId → Nat) (m : Mem) :
    (m.renameAddresses resolve).structuredTypes = m.structuredTypes := by
  rfl

@[simp] theorem renameAddresses_compoundObjects
    (resolve : ObjId → Nat) (m : Mem) :
    (m.renameAddresses resolve).compoundObjects = m.compoundObjects := by
  rfl

@[simp] theorem renameAddresses_objectCount
    (resolve : ObjId → Nat) (m : Mem) :
    (m.renameAddresses resolve).objs.length = m.objs.length := by
  simp [renameAddresses]

theorem renameAddresses_idem (resolve : ObjId → Nat) (m : Mem) :
    (m.renameAddresses resolve).renameAddresses resolve =
      m.renameAddresses resolve := by
  cases m with
  | mk objs structuredTypes stdout vaCursors compoundObjects placements =>
      simp [renameAddresses, CObj.renameAddress, List.map_map,
        CVal.renameAddress_idem, CByte.renameAddress_idem]

theorem renameAddresses_comp
    (first second : ObjId → Nat) (m : Mem) :
    (m.renameAddresses first).renameAddresses second =
      m.renameAddresses second := by
  cases m with
  | mk objs structuredTypes stdout vaCursors compoundObjects placements =>
      simp [renameAddresses, CObj.renameAddress, List.map_map,
        CVal.renameAddress_comp, CByte.renameAddress_comp]

def empty : Mem := { objs := [] }

def structuredType? (m : Mem) (o : ObjId) : Option QualType :=
  m.structuredTypes.find? (fun entry => entry.1 == o) |>.map (·.2)

def structuredTypeKeys (m : Mem) : List ObjId :=
  m.structuredTypes.map (·.1)

def structuredTypesUnique (m : Mem) : Prop :=
  (m.structuredTypeKeys).Nodup

@[simp] theorem empty_structuredTypesUnique : structuredTypesUnique Mem.empty := by
  simp [structuredTypesUnique, structuredTypeKeys, empty]

def rememberStructuredType (m : Mem) (o : ObjId) (ty : Option QualType) : Mem :=
  match ty with
  | none => m
  | some type => { m with structuredTypes := (o, type) :: m.structuredTypes }

@[simp] theorem rememberStructuredType_lookup
    (m : Mem) (o : ObjId) (ty : QualType) :
    (m.rememberStructuredType o (some ty)).structuredType? o = some ty := by
  simp [rememberStructuredType, structuredType?]

theorem rememberStructuredType_lookup_of_ne
    (m : Mem) (o q : ObjId) (ty : QualType) (hq : q ≠ o) :
    (m.rememberStructuredType o (some ty)).structuredType? q = m.structuredType? q := by
  simp [rememberStructuredType, structuredType?, hq, Ne.symm hq]

theorem rememberStructuredType_unique
    (m : Mem) (o : ObjId) (ty : QualType)
    (h : structuredTypesUnique m)
    (hnew : ∀ ty, (o, ty) ∉ m.structuredTypes) :
    structuredTypesUnique (m.rememberStructuredType o (some ty)) := by
  unfold structuredTypesUnique structuredTypeKeys
  simp only [rememberStructuredType, List.map_cons]
  apply List.nodup_cons.mpr
  constructor
  · intro hkey
    rcases List.mem_map.1 hkey with ⟨⟨key, other⟩, hmem, heq⟩
    simp at heq
    subst key
    exact hnew other hmem
  · exact h

@[simp] theorem rememberStructuredType_placements
    (m : Mem) (o : ObjId) (ty : Option QualType) :
    (m.rememberStructuredType o ty).placements = m.placements := by
  cases ty <;> rfl

def copyStructuredType (m : Mem) (old fresh : ObjId) : Mem :=
  m.rememberStructuredType fresh (m.structuredType? old)

@[simp] theorem copyStructuredType_objs (m : Mem) (old fresh : ObjId) :
    (m.copyStructuredType old fresh).objs = m.objs := by
  cases h : m.structuredType? old <;> simp [copyStructuredType, rememberStructuredType, h]

@[simp] theorem copyStructuredType_stdout (m : Mem) (old fresh : ObjId) :
    (m.copyStructuredType old fresh).stdout = m.stdout := by
  cases h : m.structuredType? old <;> simp [copyStructuredType, rememberStructuredType, h]

@[simp] theorem copyStructuredType_vaCursors (m : Mem) (old fresh : ObjId) :
    (m.copyStructuredType old fresh).vaCursors = m.vaCursors := by
  cases h : m.structuredType? old <;> simp [copyStructuredType, rememberStructuredType, h]

@[simp] theorem copyStructuredType_compoundObjects (m : Mem) (old fresh : ObjId) :
    (m.copyStructuredType old fresh).compoundObjects = m.compoundObjects := by
  cases h : m.structuredType? old <;> simp [copyStructuredType, rememberStructuredType, h]

theorem copyStructuredType_lookup_new
    (m : Mem) (old fresh : ObjId) (ty : QualType)
    (h : m.structuredType? old = some ty) :
    (m.copyStructuredType old fresh).structuredType? fresh = some ty := by
  simp [copyStructuredType, h]

theorem copyStructuredType_lookup_of_ne
    (m : Mem) (old fresh q : ObjId) (hq : q ≠ fresh) :
    (m.copyStructuredType old fresh).structuredType? q = m.structuredType? q := by
  cases hold : m.structuredType? old with
  | none =>
      rw [copyStructuredType, hold]
      rfl
  | some ty =>
      rw [copyStructuredType, hold]
      exact rememberStructuredType_lookup_of_ne m fresh q ty hq

theorem copyStructuredType_unique
    (m : Mem) (old fresh : ObjId)
    (h : structuredTypesUnique m)
    (hnew : ∀ ty, (fresh, ty) ∉ m.structuredTypes) :
    structuredTypesUnique (m.copyStructuredType old fresh) := by
  cases hold : m.structuredType? old with
  | none => simpa [copyStructuredType, hold, rememberStructuredType] using h
  | some ty => simpa [copyStructuredType, hold] using
      (rememberStructuredType_unique m fresh ty h hnew)

@[simp] theorem copyStructuredType_placements
    (m : Mem) (old fresh : ObjId) :
    (m.copyStructuredType old fresh).placements = m.placements := by
  simp [copyStructuredType]

def emitStdout (m : Mem) (bytes : List CByte) : Mem :=
  { m with stdout := m.stdout ++ bytes }

theorem emitStdout_structuredTypesUnique
    (m : Mem) (bytes : List CByte) (h : structuredTypesUnique m) :
    structuredTypesUnique (m.emitStdout bytes) := by
  simpa [structuredTypesUnique, structuredTypeKeys, emitStdout] using h

@[simp] theorem emitStdout_structuredType_lookup
    (m : Mem) (bytes : List CByte) (q : ObjId) :
    (m.emitStdout bytes).structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem emitStdout_placements (m : Mem) (bytes : List CByte) :
    (m.emitStdout bytes).placements = m.placements := by
  rfl

private def vaSet (xs : List (ObjId × List CVal)) (o : ObjId) (vs : List CVal) :
    List (ObjId × List CVal) :=
  match xs with
  | [] => [(o, vs)]
  | (q, old) :: rest => if q == o then (o, vs) :: rest else (q, old) :: vaSet rest o vs

private def vaGet (xs : List (ObjId × List CVal)) (o : ObjId) : Option (List CVal) :=
  match xs with
  | [] => none
  | (q, vs) :: rest => if q == o then some vs else vaGet rest o

/-- The abstract argument sequence of a live `va_list`.  This accessor keeps
the ABI-free cursor representation private while allowing library consumers
such as `vprintf` to walk the parser-provided promoted values. -/
def vaValues (m : Mem) (p : Ptr) : MRes (List CVal) :=
  match p.obj with
  | none => .error (.memUB (.nullDeref p.off))
  | some o =>
      match vaGet m.vaCursors o with
      | some vs => .ok vs
      | none => .error (.memUB (.nonValueRepresentation o 0))

@[simp] theorem vaValues_address_irrel (m : Mem) (p : Ptr) (address : Nat) :
    vaValues m {p with address := address} = vaValues m p := by
  simp [vaValues]

private def vaDrop (xs : List (ObjId × List CVal)) (o : ObjId) : List (ObjId × List CVal) :=
  match xs with
  | [] => []
  | (q, vs) :: rest => if q == o then rest else (q, vs) :: vaDrop rest o

private def placementSet (xs : List (ObjId × Nat)) (o : ObjId) (address : Nat) :
    List (ObjId × Nat) :=
  match xs with
  | [] => [(o, address)]
  | (q, old) :: rest => if q == o then (o, address) :: rest else (q, old) :: placementSet rest o address

private theorem placementSet_mem (xs : List (ObjId × Nat)) (o : ObjId) (address : Nat) :
    (o, address) ∈ placementSet xs o address := by
  induction xs with
  | nil => simp [placementSet]
  | cons x xs ih =>
    by_cases h : x.1 == o <;> simp [placementSet, h, ih]

private theorem placementSet_find (xs : List (ObjId × Nat)) (o : ObjId) (address : Nat) :
    (placementSet xs o address).find? (fun entry => entry.1 == o) =
      some (o, address) := by
  induction xs with
  | nil => simp [placementSet]
  | cons x xs ih =>
    by_cases h : x.1 == o
    · simp [placementSet, h]
    · simp [placementSet, h, ih]

private theorem placementSet_other (xs : List (ObjId × Nat)) (o q : ObjId)
    (address : Nat) (hq : q ≠ o) :
    (placementSet xs o address).find? (fun entry => entry.1 == q) =
      xs.find? (fun entry => entry.1 == q) := by
  induction xs with
  | nil => have hoq : o ≠ q := Ne.symm hq; simp [placementSet, hoq]
  | cons x xs ih =>
    by_cases ho : x.1 == o
    · have hxo : x.1 ≠ q := by
        intro hxq
        apply hq
        exact hxq.symm.trans (beq_iff_eq.mp ho)
      have hqo : o ≠ q := Ne.symm hq
      simp [placementSet, ho, hxo, hqo, ih]
    · by_cases hxq : x.1 == q
      · simp [placementSet, ho, hxq]
      · simp [placementSet, ho, hxq, ih]

def vaStart (m : Mem) (p : Ptr) (args : List CVal) : MRes Mem :=
  match p.obj with
  | none => .error (.memUB (.nullDeref p.off))
  | some o => .ok { m with vaCursors := vaSet m.vaCursors o args }

def vaCopy (m : Mem) (dst src : Ptr) : MRes Mem :=
  match dst.obj, src.obj with
  | some d, some s =>
      match vaGet m.vaCursors s with
      | some vs => .ok { m with vaCursors := vaSet m.vaCursors d vs }
      | none => .error (.memUB (.nonValueRepresentation s 0))
  | none, _ | _, none => .error (.memUB (.nullDeref 0))

def vaEnd (m : Mem) (p : Ptr) : MRes Mem :=
  match p.obj with
  | none => .error (.memUB (.nullDeref p.off))
  | some o => .ok { m with vaCursors := vaDrop m.vaCursors o }

def vaArg (m : Mem) (p : Ptr) : MRes (CVal × Mem) :=
  match p.obj with
  | none => .error (.memUB (.nullDeref p.off))
  | some o =>
      match vaGet m.vaCursors o with
      | none => .error (.memUB (.nonValueRepresentation o 0))
      | some [] => .error (.memUB (.outOfBounds o 0 1 0))
      | some (v :: vs) => .ok (v, { m with vaCursors := vaSet m.vaCursors o vs })

@[simp] theorem vaStart_address_irrel (m : Mem) (p : Ptr) (args : List CVal)
    (address : Nat) : vaStart m {p with address := address} args = vaStart m p args := by
  simp [vaStart]

@[simp] theorem vaCopy_address_irrel (m : Mem) (dst src : Ptr) (addressDst addressSrc : Nat) :
    vaCopy m {dst with address := addressDst} {src with address := addressSrc} =
      vaCopy m dst src := by
  simp [vaCopy]

@[simp] theorem vaEnd_address_irrel (m : Mem) (p : Ptr) (address : Nat) :
    vaEnd m {p with address := address} = vaEnd m p := by
  simp [vaEnd]

@[simp] theorem vaArg_address_irrel (m : Mem) (p : Ptr) (address : Nat) :
    vaArg m {p with address := address} = vaArg m p := by
  simp [vaArg]

theorem vaStart_placements {m m' : Mem} {p : Ptr} {args : List CVal}
    (h : vaStart m p args = .ok m') : m'.placements = m.placements := by
  cases hp : p.obj with
  | none => simp [vaStart, hp] at h
  | some o =>
    simp [vaStart, hp] at h
    cases h
    rfl

theorem vaCopy_placements {m m' : Mem} {dst src : Ptr}
    (h : vaCopy m dst src = .ok m') : m'.placements = m.placements := by
  cases hd : dst.obj with
  | none => simp [vaCopy, hd] at h
  | some d =>
    cases hs : src.obj with
    | none => simp [vaCopy, hd, hs] at h
    | some s =>
      cases hv : vaGet m.vaCursors s with
      | none => simp [vaCopy, hd, hs, hv] at h
      | some vs =>
        simp [vaCopy, hd, hs, hv] at h
        cases h
        rfl

theorem vaEnd_placements {m m' : Mem} {p : Ptr}
    (h : vaEnd m p = .ok m') : m'.placements = m.placements := by
  cases hp : p.obj with
  | none => simp [vaEnd, hp] at h
  | some o =>
    simp [vaEnd, hp] at h
    cases h
    rfl

theorem vaArg_placements {m : Mem} {p : Ptr} {v : CVal} {m' : Mem}
    (h : vaArg m p = .ok (v, m')) : m'.placements = m.placements := by
  cases hp : p.obj with
  | none => simp [vaArg, hp] at h
  | some o =>
    cases hv : vaGet m.vaCursors o with
    | none => simp [vaArg, hp, hv] at h
    | some vs =>
      cases vs with
      | nil => simp [vaArg, hp, hv] at h
      | cons v rest =>
        simp [vaArg, hp, hv] at h
        have hm : m'.placements = m.placements := by
          simpa using (congrArg (fun r : Mem => r.placements) h.2).symm
        exact hm

theorem vaStart_structuredTypesUnique {m m' : Mem} {p : Ptr} {args : List CVal}
    (h : structuredTypesUnique m)
    (hr : vaStart m p args = .ok m') : structuredTypesUnique m' := by
  cases hp : p.obj with
  | none => simp [vaStart, hp] at hr
  | some o =>
    simp [vaStart, hp] at hr
    cases hr
    simpa [structuredTypesUnique, structuredTypeKeys] using h

theorem vaStart_structuredType_lookup {m m' : Mem} {p : Ptr} {args : List CVal}
    (q : ObjId) (hr : vaStart m p args = .ok m') :
    m'.structuredType? q = m.structuredType? q := by
  cases hp : p.obj with
  | none => simp [vaStart, hp] at hr
  | some o =>
    simp [vaStart, hp] at hr
    cases hr
    rfl

theorem vaCopy_structuredTypesUnique {m m' : Mem} {dst src : Ptr}
    (h : structuredTypesUnique m)
    (hr : vaCopy m dst src = .ok m') : structuredTypesUnique m' := by
  cases hd : dst.obj with
  | none => simp [vaCopy, hd] at hr
  | some d =>
    cases hs : src.obj with
    | none => simp [vaCopy, hd, hs] at hr
    | some s =>
      cases hv : vaGet m.vaCursors s with
      | none => simp [vaCopy, hd, hs, hv] at hr
      | some vs =>
        simp [vaCopy, hd, hs, hv] at hr
        cases hr
        simpa [structuredTypesUnique, structuredTypeKeys] using h

theorem vaCopy_structuredType_lookup {m m' : Mem} {dst src : Ptr}
    (q : ObjId) (hr : vaCopy m dst src = .ok m') :
    m'.structuredType? q = m.structuredType? q := by
  cases hd : dst.obj with
  | none => simp [vaCopy, hd] at hr
  | some d =>
    cases hs : src.obj with
    | none => simp [vaCopy, hd, hs] at hr
    | some s =>
      cases hv : vaGet m.vaCursors s with
      | none => simp [vaCopy, hd, hs, hv] at hr
      | some vs =>
        simp [vaCopy, hd, hs, hv] at hr
        cases hr
        rfl

theorem vaEnd_structuredTypesUnique {m m' : Mem} {p : Ptr}
    (h : structuredTypesUnique m)
    (hr : vaEnd m p = .ok m') : structuredTypesUnique m' := by
  cases hp : p.obj with
  | none => simp [vaEnd, hp] at hr
  | some o =>
    simp [vaEnd, hp] at hr
    cases hr
    simpa [structuredTypesUnique, structuredTypeKeys] using h

theorem vaEnd_structuredType_lookup {m m' : Mem} {p : Ptr}
    (q : ObjId) (hr : vaEnd m p = .ok m') :
    m'.structuredType? q = m.structuredType? q := by
  cases hp : p.obj with
  | none => simp [vaEnd, hp] at hr
  | some o =>
    simp [vaEnd, hp] at hr
    cases hr
    rfl

theorem vaArg_structuredTypesUnique {m : Mem} {p : Ptr} {v : CVal} {m' : Mem}
    (h : structuredTypesUnique m)
    (hr : vaArg m p = .ok (v, m')) : structuredTypesUnique m' := by
  cases hp : p.obj with
  | none => simp [vaArg, hp] at hr
  | some o =>
    cases hv : vaGet m.vaCursors o with
    | none => simp [vaArg, hp, hv] at hr
    | some vs =>
      cases vs with
      | nil => simp [vaArg, hp, hv] at hr
      | cons head rest =>
        simp [vaArg, hp, hv] at hr
        have hm : m' = {m with vaCursors := vaSet m.vaCursors o rest} := hr.2.symm
        rw [hm]
        simpa [structuredTypesUnique, structuredTypeKeys] using h

theorem vaArg_structuredType_lookup {m : Mem} {p : Ptr} {v : CVal} {m' : Mem}
    (q : ObjId) (hr : vaArg m p = .ok (v, m')) :
    m'.structuredType? q = m.structuredType? q := by
  cases hp : p.obj with
  | none => simp [vaArg, hp] at hr
  | some o =>
    cases hv : vaGet m.vaCursors o with
    | none => simp [vaArg, hp, hv] at hr
    | some vs =>
      cases vs with
      | nil => simp [vaArg, hp, hv] at hr
      | cons head rest =>
        simp [vaArg, hp, hv] at hr
        cases hr.2
        rfl

def get? (m : Mem) (o : ObjId) : Option CObj := m.objs[o]?

def placement? (m : Mem) (o : ObjId) : Option Nat :=
  (m.placements.find? (fun entry => entry.1 == o)).map Prod.snd

/-! Pointer-byte validity records the concrete placement carried by a stored
pointer representation.  It is deliberately a memory invariant rather than a
property of `CByte`: the placement belongs to the allocation state. -/
def ptrAddressCanonical (m : Mem) (p : Ptr) : Prop :=
  match p.obj with
  | none => True
  | some o => m.placement? o = some p.address

def byteAddressCanonical (m : Mem) : CByte → Prop
  | .ptrByte p _ => ptrAddressCanonical m p
  | .ptrIntByte p _ => ptrAddressCanonical m p
  | _ => True

def pointerBytesCanonical (m : Mem) : Prop :=
  ∀ (o : ObjId) (c : CObj), m.get? o = some c →
    ∀ b, b ∈ c.bytes → byteAddressCanonical m b

theorem placement_renameAddresses (rename : ObjId → Nat) (m : Mem) (o : ObjId) :
    (m.renameAddresses rename).placement? o =
      (m.placement? o).map (fun _ => rename o) := by
  have hfind : ∀ xs : List (ObjId × Nat),
      (xs.find? (fun entry => entry.1 == o)).map (fun x => rename x.1) =
        (xs.find? (fun entry => entry.1 == o)).map (fun _ => rename o) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        by_cases hx : x.1 == o
        · have hxo : x.1 = o := of_decide_eq_true hx
          simp [hx, hxo]
        · simp [hx, ih]
  simp [placement?, renameAddresses, List.find?_map, Function.comp_def, hfind]

theorem ptrAddressCanonical_rename
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (o : ObjId)
    (hp : p.obj = some o) (h : m.placement? o = some p.address) :
    ptrAddressCanonical (m.renameAddresses rename) (Ptr.renameAddress rename p) := by
  simp [ptrAddressCanonical, hp, placement_renameAddresses, h, Ptr.renameAddress]

theorem ptrByte_beq_rename_of_canonical
    (rename : ObjId → Nat) (m : Mem) (p q : Ptr)
    (hobj : p.obj = q.obj)
    (hp : ptrAddressCanonical m p) (hq : ptrAddressCanonical m q) :
    (CByte.renameAddress rename (CByte.ptrByte p 0) ==
      CByte.renameAddress rename (CByte.ptrByte q 0)) =
    (CByte.ptrByte p 0 == CByte.ptrByte q 0) := by
  cases p with
  | mk po pa pf pb =>
      cases q with
      | mk qo qa qf qb =>
          cases po with
          | none =>
              cases qo with
              | none => rfl
              | some qo => cases hobj
          | some po =>
              cases qo with
              | none => cases hobj
              | some qo =>
                  have hpo : m.placement? po = some pa := by
                    simpa [ptrAddressCanonical] using hp
                  have hqo : m.placement? qo = some qa := by
                    simpa [ptrAddressCanonical] using hq
                  have hpoq : po = qo := by
                    simpa using hobj
                  subst hpoq
                  have haddr : pa = qa := by simpa [hpo] using hqo
                  subst haddr
                  simp [CByte.renameAddress, Ptr.renameAddress, BEq.beq,
                    LeanModels.C.C23.instBEqCByte.beq,
                    LeanModels.C.C23.instBEqPtr.beq]

theorem vaStart_placement_lookup {m m' : Mem} {p : Ptr} {args : List CVal} (q : ObjId)
    (h : vaStart m p args = .ok m') : m'.placement? q = m.placement? q := by
  have hp : m'.placements = m.placements := vaStart_placements h
  unfold placement?
  simp only [hp]

theorem vaCopy_placement_lookup {m m' : Mem} {dst src : Ptr} (q : ObjId)
    (h : vaCopy m dst src = .ok m') : m'.placement? q = m.placement? q := by
  have hp : m'.placements = m.placements := vaCopy_placements h
  unfold placement?
  simp only [hp]

theorem vaEnd_placement_lookup {m m' : Mem} {p : Ptr} (q : ObjId)
    (h : vaEnd m p = .ok m') : m'.placement? q = m.placement? q := by
  have hp : m'.placements = m.placements := vaEnd_placements h
  unfold placement?
  simp only [hp]

theorem vaArg_placement_lookup {m : Mem} {p : Ptr} {v : CVal} {m' : Mem} (q : ObjId)
    (h : vaArg m p = .ok (v, m')) : m'.placement? q = m.placement? q := by
  have hp : m'.placements = m.placements := vaArg_placements h
  unfold placement?
  simp only [hp]

def rangesDisjoint (a sizeA b sizeB : Nat) : Bool :=
  a + sizeA ≤ b || b + sizeB ≤ a

/-- A caller-selected placement is aligned and disjoint from every live
object whose placement is known.  This is the validity obligation for the
open-address choice; provenance remains separate. -/
def placementValid (m : Mem) (address size alignment : Nat) : Bool :=
  (alignment == 0 || address % alignment == 0) &&
    m.placements.all (fun entry =>
      match m.get? entry.1 with
      | some c => !c.live || rangesDisjoint entry.2 c.size address size
      | none => true)

@[simp] theorem placementValid_empty (address size alignment : Nat) :
    placementValid Mem.empty address size alignment =
      (alignment == 0 || address % alignment == 0) := by
  simp [placementValid, empty]

@[simp] theorem placementValid_emitStdout (m : Mem) (bytes : List CByte)
    (address size alignment : Nat) :
    placementValid (m.emitStdout bytes) address size alignment =
      placementValid m address size alignment := by
  rfl

def count (m : Mem) : Nat := m.objs.length

def compoundObject? (m : Mem) (span : CSpan) : Option ObjId :=
  (m.compoundObjects.find? (fun entry => entry.1 == span)).bind fun entry =>
    match m.get? entry.2 with
    | some obj => if obj.live then some entry.2 else none
    | none => none

def rememberCompound (m : Mem) (span : CSpan) (o : ObjId) : Mem :=
  { m with compoundObjects := (span, o) :: m.compoundObjects }

@[simp] theorem rememberCompound_structuredTypesUnique
    (m : Mem) (span : CSpan) (o : ObjId)
    (h : structuredTypesUnique m) :
    structuredTypesUnique (m.rememberCompound span o) := by
  simpa [structuredTypesUnique, structuredTypeKeys, rememberCompound] using h

@[simp] theorem rememberCompound_structuredType_lookup
    (m : Mem) (span : CSpan) (o : ObjId) (q : ObjId) :
    (m.rememberCompound span o).structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem rememberCompound_placements (m : Mem) (span : CSpan) (o : ObjId) :
    (m.rememberCompound span o).placements = m.placements := by
  rfl

@[simp] theorem placementValid_rememberCompound (m : Mem) (span : CSpan) (o : ObjId)
    (address size alignment : Nat) :
    placementValid (m.rememberCompound span o) address size alignment =
      placementValid m address size alignment := by
  rfl

/-- C23 §6.2.4 / §6.7.11: create an object whose representation is
INDETERMINATE. Returns the new memory and the object's id.

Every automatic object is created this way on block entry — which is the
locals-are-objects decision, executed. -/
def alloc (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) : Mem × ObjId :=
  let o := m.objs.length
  ({ m with
      objs := m.objs ++ [⟨dur, true, List.replicate size .indet, ty⟩]
      placements := m.placements ++ [(o, o)] }, o)

def allocStructured (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : Option QualType) : Mem × ObjId :=
  let (m', o) := m.alloc dur size ty
  (m'.rememberStructuredType o structured, o)

theorem allocStructured_unique
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : QualType) (h : structuredTypesUnique m)
    (hnew : ∀ q, (m.objs.length, q) ∉ m.structuredTypes) :
    structuredTypesUnique
      (m.allocStructured dur size ty (some structured)).1 := by
  change structuredTypesUnique
    (m.rememberStructuredType m.objs.length (some structured))
  exact rememberStructuredType_unique m m.objs.length structured h hnew

@[simp] theorem allocStructured_lookup
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) (structured : QualType) :
    (m.allocStructured dur size ty (some structured)).1.structuredType?
        (m.allocStructured dur size ty (some structured)).2 = some structured := by
  simp [allocStructured]

/-- `calloc`'s object (§7.24.3.2p2): all bits zero, hence determinate. -/
def allocZeroed (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) : Mem × ObjId :=
  let o := m.objs.length
  ({ m with
      objs := m.objs ++ [⟨dur, true, List.replicate size (.conc 0), ty⟩]
      placements := m.placements ++ [(o, o)] }, o)

def allocZeroedStructured (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : Option QualType) : Mem × ObjId :=
  let (m', o) := m.allocZeroed dur size ty
  (m'.rememberStructuredType o structured, o)

theorem allocZeroedStructured_unique
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : QualType) (h : structuredTypesUnique m)
    (hnew : ∀ q, (m.objs.length, q) ∉ m.structuredTypes) :
    structuredTypesUnique
      (m.allocZeroedStructured dur size ty (some structured)).1 := by
  change structuredTypesUnique
    (m.rememberStructuredType m.objs.length (some structured))
  exact rememberStructuredType_unique m m.objs.length structured h hnew

@[simp] theorem alloc_structuredTypesUnique
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (h : structuredTypesUnique m) :
    structuredTypesUnique (m.alloc dur size ty).1 := by
  simpa [alloc, structuredTypesUnique, structuredTypeKeys] using h

@[simp] theorem alloc_structuredType_lookup
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) (q : ObjId) :
    (m.alloc dur size ty).1.structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem allocZeroed_structuredTypesUnique
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (h : structuredTypesUnique m) :
    structuredTypesUnique (m.allocZeroed dur size ty).1 := by
  simpa [allocZeroed, structuredTypesUnique, structuredTypeKeys] using h

@[simp] theorem allocZeroed_structuredType_lookup
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) (q : ObjId) :
    (m.allocZeroed dur size ty).1.structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem allocZeroedStructured_lookup
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) (structured : QualType) :
    (m.allocZeroedStructured dur size ty (some structured)).1.structuredType?
        (m.allocZeroedStructured dur size ty (some structured)).2 = some structured := by
  simp [allocZeroedStructured]

/-- Allocate at an explicit concrete placement.  The caller supplies the
address choice; provenance remains the returned object id and is what
`resolve` authorises. -/
def allocAt (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (address : Nat) : Mem × Ptr :=
  let (m', o) := m.alloc dur size ty
  ({ m' with placements := placementSet m'.placements o address },
    Ptr.toObjectBoundAt o address size)

def allocAtStructured (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : Option QualType) (address : Nat) : Mem × Ptr :=
  let (m', o) := m.allocStructured dur size ty structured
  ({ m' with placements := placementSet m'.placements o address },
    Ptr.toObjectBoundAt o address size)

@[simp] theorem allocAtStructured_lookup
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : QualType) (address : Nat) :
    (m.allocAtStructured dur size ty (some structured) address).1.structuredType?
        (m.allocStructured dur size ty (some structured)).2 =
      some structured := by
  simp only [allocAtStructured]
  exact allocStructured_lookup m dur size ty structured

theorem allocAtStructured_unique
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : QualType) (address : Nat)
    (h : structuredTypesUnique m)
    (hnew : ∀ q, (m.objs.length, q) ∉ m.structuredTypes) :
    structuredTypesUnique
      (m.allocAtStructured dur size ty (some structured) address).1 := by
  simpa [allocAtStructured, structuredTypesUnique, structuredTypeKeys] using
    allocStructured_unique m dur size ty structured h hnew

def allocZeroedAt (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (address : Nat) : Mem × Ptr :=
  let (m', o) := m.allocZeroed dur size ty
  ({ m' with placements := placementSet m'.placements o address },
    Ptr.toObjectBoundAt o address size)

def allocZeroedAtStructured (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : Option QualType) (address : Nat) : Mem × Ptr :=
  let (m', o) := m.allocZeroedStructured dur size ty structured
  ({ m' with placements := placementSet m'.placements o address },
    Ptr.toObjectBoundAt o address size)

@[simp] theorem allocAt_structuredTypesUnique
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (address : Nat) (h : structuredTypesUnique m) :
    structuredTypesUnique (m.allocAt dur size ty address).1 := by
  simpa [allocAt, alloc, structuredTypesUnique, structuredTypeKeys] using h

@[simp] theorem allocAt_structuredType_lookup
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (address : Nat) (q : ObjId) :
    (m.allocAt dur size ty address).1.structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem allocZeroedAt_structuredTypesUnique
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (address : Nat) (h : structuredTypesUnique m) :
    structuredTypesUnique (m.allocZeroedAt dur size ty address).1 := by
  simpa [allocZeroedAt, allocZeroed, structuredTypesUnique, structuredTypeKeys] using h

@[simp] theorem allocZeroedAt_structuredType_lookup
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (address : Nat) (q : ObjId) :
    (m.allocZeroedAt dur size ty address).1.structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem allocZeroedAtStructured_lookup
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : QualType) (address : Nat) :
    (m.allocZeroedAtStructured dur size ty (some structured) address).1.structuredType?
        (m.allocZeroedStructured dur size ty (some structured)).2 =
      some structured := by
  simp only [allocZeroedAtStructured]
  exact allocZeroedStructured_lookup m dur size ty structured

theorem allocZeroedAtStructured_unique
    (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (structured : QualType) (address : Nat)
    (h : structuredTypesUnique m)
    (hnew : ∀ q, (m.objs.length, q) ∉ m.structuredTypes) :
    structuredTypesUnique
      (m.allocZeroedAtStructured dur size ty (some structured) address).1 := by
  simpa [allocZeroedAtStructured, structuredTypesUnique, structuredTypeKeys] using
    allocZeroedStructured_unique m dur size ty structured h hnew

/-- C23 §6.2.4p6 / §7.24.3: end an object's lifetime. The object stays in
the store as a tombstone — see `CObj.live`. -/
def kill (m : Mem) (o : ObjId) : Mem :=
  { m with objs := m.objs.modify o (fun c => { c with live := false }) }

theorem get?_kill_of_ne (m : Mem) (o q : ObjId) (h : q ≠ o) :
    (m.kill o).get? q = m.get? q := by
  simp only [kill, get?]
  rw [List.getElem?_modify]
  simp [Ne.symm h]

@[simp] theorem kill_placements (m : Mem) (o : ObjId) :
    (m.kill o).placements = m.placements := by
  rfl

@[simp] theorem kill_structuredTypesUnique
    (m : Mem) (o : ObjId) (h : structuredTypesUnique m) :
    structuredTypesUnique (m.kill o) := by
  simpa [structuredTypesUnique, structuredTypeKeys, kill] using h

@[simp] theorem kill_structuredType_lookup (m : Mem) (dead q : ObjId) :
    (m.kill dead).structuredType? q = m.structuredType? q := by
  rfl

theorem placementValid_kill (m : Mem) (o : ObjId) (address size alignment : Nat)
    (hvalid : placementValid m address size alignment = true) :
    placementValid (m.kill o) address size alignment = true := by
  unfold placementValid at hvalid ⊢
  simp only [Bool.and_eq_true] at hvalid ⊢
  refine ⟨hvalid.1, ?_⟩
  rw [List.all_eq_true] at hvalid ⊢
  intro entry hmem
  have hmem' : entry ∈ m.placements := by simpa using hmem
  have hentry := hvalid.2 entry hmem'
  by_cases he : entry.1 = o
  · cases hg : m.get? entry.1 with
    | none =>
      have hg' : m.get? o = none := by simpa [he] using hg
      have hk : (m.kill o).get? entry.1 = none := by
        simp only [kill, get?]
        rw [List.getElem?_modify]
        by_cases ho : o < m.objs.length
        · have : False := by simpa [get?, ho] using hg'
          contradiction
        · simp [hg', he, ho]
      rw [hk]
    | some c =>
      have hg' : m.get? o = some c := by simpa [he] using hg
      have hk : (m.kill o).get? entry.1 = some {c with live := false} := by
        simp only [kill, get?] at hg' ⊢
        rw [List.getElem?_modify]
        simp [hg', he]
      rw [hk]
      simp
  · rw [get?_kill_of_ne m o entry.1 he]
    exact hentry

private theorem killFrom_fold_placementValid (xs : List Nat) (m : Mem) (start : Nat)
    (address size alignment : Nat)
    (hvalid : placementValid m address size alignment = true) :
    placementValid
        (xs.foldl (fun acc i =>
          let o := start + i
          match acc.get? o with
          | some c => if c.dur == .automatic then acc.kill o else acc
          | none => acc) m)
        address size alignment = true := by
  induction xs generalizing m with
  | nil => exact hvalid
  | cons i xs ih =>
    simp only [List.foldl]
    cases hg : m.get? (start + i) with
    | none =>
      simp [hg]
      apply ih m
      simpa [hg] using hvalid
    | some c =>
      by_cases ha : c.dur == .automatic
      · simp [hg, ha]
        apply ih (m.kill (start + i))
        exact placementValid_kill m (start + i) address size alignment hvalid
      · simp [hg, ha]
        apply ih m
        simpa [hg, ha] using hvalid

@[simp] theorem kill_placement_lookup (m : Mem) (dead live : ObjId) :
    (m.kill dead).placement? live = m.placement? live := by
  rfl

/-- End the lifetime of automatic objects allocated at or after `start`.
Static objects remain live for the whole execution (§6.2.4p3). -/
def killFrom (m : Mem) (start : Nat) : Mem :=
  (List.range (m.count - start)).foldl (fun acc i =>
    let o := start + i
    match acc.get? o with
    | some c => if c.dur == .automatic then acc.kill o else acc
    | none => acc) m

private theorem killFrom_fold_placements (xs : List Nat) (m : Mem) (start : Nat) :
    (xs.foldl (fun acc i =>
      let o := start + i
      match acc.get? o with
      | some c => if c.dur == .automatic then acc.kill o else acc
      | none => acc) m).placements = m.placements := by
  induction xs generalizing m with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl]
    rw [ih]
    cases hget : m.get? (start + i) with
    | none => simp [hget]
    | some c =>
      by_cases ha : (c.dur == .automatic) = true
      · simp [hget, ha, kill]
      · simp [hget, ha]

private theorem killFrom_fold_structuredTypesUnique
    (xs : List Nat) (m : Mem) (start : Nat)
    (hunique : structuredTypesUnique m) :
    structuredTypesUnique
      (xs.foldl (fun acc i =>
        let o := start + i
        match acc.get? o with
        | some c => if c.dur == .automatic then acc.kill o else acc
        | none => acc) m) := by
  induction xs generalizing m with
  | nil => exact hunique
  | cons i xs ih =>
    simp only [List.foldl]
    cases hget : m.get? (start + i) with
    | none => exact ih m hunique
    | some c =>
      by_cases ha : (c.dur == .automatic) = true
      · simp [hget, ha]
        apply ih
        exact kill_structuredTypesUnique m (start + i) hunique
      · simp [hget, ha]
        exact ih m hunique

@[simp] theorem killFrom_placements (m : Mem) (start : Nat) :
    (m.killFrom start).placements = m.placements := by
  exact killFrom_fold_placements (List.range (m.count - start)) m start

theorem killFrom_structuredTypesUnique
    (m : Mem) (start : Nat) (hunique : structuredTypesUnique m) :
    structuredTypesUnique (m.killFrom start) := by
  exact killFrom_fold_structuredTypesUnique
    (List.range (m.count - start)) m start hunique

private theorem killFrom_fold_structuredType_lookup
    (xs : List Nat) (m : Mem) (start q : ObjId) :
    (xs.foldl (fun acc i =>
      let o := start + i
      match acc.get? o with
      | some c => if c.dur == .automatic then acc.kill o else acc
      | none => acc) m).structuredType? q = m.structuredType? q := by
  induction xs generalizing m with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl]
    cases hget : m.get? (start + i) with
    | none => simp [hget, ih]
    | some c =>
      by_cases ha : (c.dur == .automatic) = true
      · simp [hget, ha, kill_structuredType_lookup, ih]
      · simp [hget, ha, ih]

@[simp] theorem killFrom_structuredType_lookup (m : Mem) (start q : ObjId) :
    (m.killFrom start).structuredType? q = m.structuredType? q := by
  exact killFrom_fold_structuredType_lookup (List.range (m.count - start)) m start q

@[simp] theorem placementValid_killFrom (m : Mem) (start address size alignment : Nat)
    (hvalid : placementValid m address size alignment = true) :
    placementValid (m.killFrom start) address size alignment = true := by
  exact killFrom_fold_placementValid (List.range (m.count - start)) m start
    address size alignment hvalid

@[simp] theorem killFrom_placement_lookup (m : Mem) (start live : ObjId) :
    (m.killFrom start).placement? live = m.placement? live := by
  simp [placement?, killFrom_placements]

/-! ### The one place the structural refusals are raised -/

/-- Resolve a pointer to a live object and an in-bounds byte range.

**Every load and every store goes through this**, so C's three structural
undefined behaviors are decided in exactly one function:

* §6.5.4.2p4 — indirection through an invalid value (`J.2(39)`);
* §6.2.4p2 — the object is outside its lifetime (`J.2(9)`/`J.2(10)`);
* §6.5.7p9 — the access leaves the object (`J.2(46)`).

A negative offset fails the same test as an oversized one, so a pointer
walked backwards off its object is caught by the same arm. -/
def resolve (m : Mem) (p : Ptr) (n : Nat) : MRes (ObjId × CObj × Nat) :=
  match p.obj with
  | none => .error (.memUB (.nullDeref p.off))
  | some o =>
    match m.get? o with
    | none => .error (.memUB (.nullDeref p.off))
    | some c =>
      if !c.live then .error (.memUB (.deadObject o c.dur))
      else if p.off < 0 then
        .error (.memUB (.outOfBounds o p.off n c.size))
      else if p.off + (n : Int) > (c.size : Int) then
        .error (.memUB (.outOfBounds o p.off n c.size))
      else if p.off + (n : Int) > (p.bound.getD (c.size : Int)) then
        .error (.memUB (.outOfBounds o p.off n c.size))
      else .ok (o, c, p.off.toNat)

theorem resolve_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (n : Nat) :
    (m.renameAddresses rename).resolve (Ptr.renameAddress rename p) n =
      (m.resolve p n).map (fun r =>
        (r.1, CObj.renameAddress rename r.2.1, r.2.2)) := by
  cases hp : p.obj with
  | none => simp [resolve, hp, Ptr.renameAddress, Except.map]
  | some o =>
    cases hc : m.get? o with
    | none =>
        have hc' : (m.renameAddresses rename).get? o = none := by
          simpa [get?, renameAddresses] using
            congrArg (Option.map (CObj.renameAddress rename)) hc
        simp [resolve, hp, hc, hc', Ptr.renameAddress, Except.map]
    | some c =>
        have hc' : (m.renameAddresses rename).get? o =
            some (CObj.renameAddress rename c) := by
          simpa [get?, renameAddresses] using
            congrArg (Option.map (CObj.renameAddress rename)) hc
        simp [resolve, hp, hc, hc', Ptr.renameAddress, CObj.renameAddress,
          CObj.size, List.length_map, Except.map]
        <;> repeat' first | split | simp_all [CObj.renameAddress, CObj.size]
        <;> subst_vars <;> simp_all

/-! ### §6.3.2.1p2 Lvalue conversion — reading bytes out -/

/-- Read `n` bytes of representation. Refuses per `resolve`; does NOT
inspect the bytes, because a `memcpy` of a partly-indeterminate object is
legal (§6.2.6.1p4 permits copying via character type) and only an
INTERPRETATION of those bytes as a value can fail. -/
def loadBytes (m : Mem) (p : Ptr) (n : Nat) : MRes (List CByte) := do
  let (_, c, off) ← m.resolve p n
  return (c.bytes.drop off).take n

theorem loadBytes_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (n : Nat) :
    (m.renameAddresses rename).loadBytes (Ptr.renameAddress rename p) n =
      (m.loadBytes p n).map (List.map (CByte.renameAddress rename)) := by
  unfold loadBytes
  rw [resolve_renameAddresses]
  cases h : m.resolve p n with
  | error e => simp [h, Functor.map, Except.map, Except.bind, Function.comp_def]
  | ok result =>
      cases result with
      | mk o rest =>
          cases rest with
          | mk c off =>
              simp [h, Functor.map, CObj.renameAddress, CObj.size, List.map_take,
                List.map_drop, List.map_map, Except.map, Function.comp_def]

/-- Write a byte string. The length is the caller's `n`. -/
def storeBytes (m : Mem) (p : Ptr) (bs : List CByte) : MRes Mem := do
  let (o, c, off) ← m.resolve p bs.length
  let bytes := (c.bytes.take off) ++ bs ++ (c.bytes.drop (off + bs.length))
  return { m with objs := m.objs.set o { c with bytes := bytes } }

theorem storeBytes_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (bs : List CByte) :
    (m.renameAddresses rename).storeBytes (Ptr.renameAddress rename p)
        (bs.map (CByte.renameAddress rename)) =
      (m.storeBytes p bs).map (Mem.renameAddresses rename) := by
  unfold storeBytes
  rw [resolve_renameAddresses]
  cases h : m.resolve p bs.length with
  | error e => simp [h, Functor.map, Except.map, Except.bind, Function.comp_def]
  | ok result =>
      cases result with
      | mk o rest =>
          cases rest with
          | mk c off =>
              simp [h, Functor.map, Except.map, Except.bind, Function.comp_def,
                Mem.renameAddresses, CObj.renameAddress, List.map_append,
                List.map_take, List.map_drop, List.map_map]

/-! ### §6.2.6.2 Integer representation

Byte order is the profile's `little_endian`, and the extractor's profile gate
checks it before an envelope is accepted. The store/load round trip remains
structurally explicit, but representation order is still a consumed profile
fact (`docs/c-profile.md` §4.3). -/

/-- Little-endian digits, `n` of them. -/
def natToBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, v => UInt8.ofNat (v % 256) :: natToBytes n (v / 256)

/-- The inverse reading. -/
def natOfBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * natOfBytes bs

theorem natOfBytes_natToBytes (n v : Nat) (hv : v < 256 ^ n) :
    natOfBytes (natToBytes n v) = v := by
  induction n generalizing v with
  | zero => simp [natToBytes, natOfBytes] at hv ⊢; omega
  | succ n ih =>
      simp [natToBytes, natOfBytes]
      have hq : v / 256 < 256 ^ n := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).2
        simpa [Nat.pow_succ, Nat.mul_comm] using hv
      rw [ih (v / 256) hq]
      exact Nat.mod_add_div v 256

/-- The bytes of `v` at type `t`. The stored value is the mathematical
integer (`Value.lean`'s invariant), so it is reduced into the type's
unsigned residue first — that is what a representation IS. -/
def encodeInt (t : IntTy) (v : Int) : List CByte :=
  let width := max 1 (t.bits / 8)
  let u := (v % t.modulus + t.modulus) % t.modulus
  (natToBytes width u.toNat).map CByte.conc

/-- Interpret bytes as a value of type `t`. Every byte must be `conc`:
an indeterminate byte or a pointer byte is a non-value representation and
the caller refuses (`loadInt`). -/
def decodeInt (t : IntTy) (bs : List CByte) : Option Int :=
  let step := fun (b : CByte) (acc : Option (List UInt8)) =>
    match b, acc with
    | .conc x, some xs => some (x :: xs)
    | _, _ => none
  match bs.foldr step (some []) with
  | none => none
  | some xs => some (t.wrap (natOfBytes xs))

theorem decodeInt_encodeInt_of_toNat_bound (t : IntTy) (v : Int)
    (hu : (((v % t.modulus + t.modulus) % t.modulus).toNat) <
      256 ^ max 1 (t.bits / 8)) :
    decodeInt t (encodeInt t v) =
      some (t.wrap ((v % t.modulus + t.modulus) % t.modulus)) := by
  let width := max 1 (t.bits / 8)
  let u : Int := (v % t.modulus + t.modulus) % t.modulus
  have hm : 0 < t.modulus := by
    simp only [IntTy.modulus]
    induction t.bits with
    | zero => simp
    | succ n ih => simp [Int.pow_succ]; omega
  have hne : t.modulus ≠ 0 := by omega
  have hmod : 0 ≤ v % t.modulus := Int.emod_nonneg v hne
  have hu0 : 0 ≤ u := by
    dsimp [u]
    have hadd : 0 ≤ v % t.modulus + t.modulus := by omega
    exact Int.emod_nonneg _ hne
  have hu_eq : u = v % t.modulus := by
    dsimp [u]
    rw [Int.add_emod_right, Int.emod_emod]
  have hfold :
      (List.map CByte.conc (natToBytes width u.toNat)).foldr
          (fun (b : CByte) (acc : Option (List UInt8)) =>
            match b, acc with
            | .conc x, some xs => some (x :: xs)
            | _, _ => none) (some []) =
        some (natToBytes width u.toNat) := by
    induction natToBytes width u.toNat with
    | nil => rfl
    | cons b bs ih => simp [ih]
  simp only [encodeInt, decodeInt, width, u, hfold]
  rw [natOfBytes_natToBytes width u.toNat]
  · rw [hu_eq]
    simp [IntTy.wrap, hmod, Int.toNat_of_nonneg hmod]
  · simpa [width, u] using hu

theorem normalized_toNat_lt_byte_power (t : IntTy) (v : Int) (width : Nat)
    (hmw : t.modulus ≤ (256 : Int) ^ width) :
    ((v % t.modulus + t.modulus) % t.modulus).toNat < 256 ^ width := by
  have hm : 0 < t.modulus := by
    simp only [IntTy.modulus]
    induction t.bits with
    | zero => simp
    | succ n ih => simp [Int.pow_succ]; omega
  have hne : t.modulus ≠ 0 := by omega
  have hmod0 : 0 ≤ v % t.modulus := Int.emod_nonneg v hne
  have hmodlt : v % t.modulus < t.modulus := Int.emod_lt v hne
  have hu : (v % t.modulus + t.modulus) % t.modulus = v % t.modulus := by
    rw [Int.add_emod_right, Int.emod_emod]
  rw [hu]
  apply (Int.toNat_lt hmod0).2
  have hpow : ((256 ^ width : Nat) : Int) = (256 : Int) ^ width := by
    induction width with
    | zero => simp
    | succ n ih => simp [Nat.pow_succ, Int.pow_succ, ih]
  rw [hpow]
  omega

theorem decodeInt_encodeInt_profile (t : IntTy) (v : Int)
    (ht : t = IntTy.char_ ∨ t = IntTy.uchar ∨ t = IntTy.bool_ ∨
      t = IntTy.short_ ∨ t = IntTy.ushort ∨ t = IntTy.int_ ∨
      t = IntTy.uint ∨ t = IntTy.long_ ∨ t = IntTy.ulong ∨
      t = IntTy.int128_ ∨ t = IntTy.uint128) :
    decodeInt t (encodeInt t v) = some (t.wrap v) := by
  have hwidth : (((v % t.modulus + t.modulus) % t.modulus).toNat) <
      256 ^ max 1 (t.bits / 8) := by
    apply normalized_toNat_lt_byte_power t v (max 1 (t.bits / 8))
    rcases ht with h | h | h | h | h | h | h | h | h | h | h <;>
      subst t <;> simp [IntTy.modulus] <;> decide
  simpa [IntTy.wrap, Int.add_emod_right, Int.emod_emod] using
    decodeInt_encodeInt_of_toNat_bound t v hwidth

theorem encodeInt_renameAddresses (resolve : ObjId → Nat) (t : IntTy) (v : Int) :
    (encodeInt t v).map (CByte.renameAddress resolve) = encodeInt t v := by
  simp [encodeInt, CByte.renameAddress]

theorem decodeInt_renameAddresses_conc
    (resolve : ObjId → Nat) (t : IntTy) (bs : List UInt8) :
    decodeInt t ((bs.map CByte.conc).map (CByte.renameAddress resolve)) =
      decodeInt t (bs.map CByte.conc) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp [decodeInt, CByte.renameAddress, ih, Function.comp_def]

theorem decodeInt_renameAddresses
    (resolve : ObjId → Nat) (t : IntTy) (bs : List CByte) :
    decodeInt t (bs.map (CByte.renameAddress resolve)) = decodeInt t bs := by
  let step := fun (b : CByte) (acc : Option (List UInt8)) =>
    match b, acc with
    | .conc x, some xs => some (x :: xs)
    | _, _ => none
  have hfold : ∀ xs : List CByte,
      (xs.map (CByte.renameAddress resolve)).foldr step (some []) =
        xs.foldr step (some []) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons b xs ih =>
        cases b <;> simp [List.map, List.foldr, CByte.renameAddress, ih, step]
  simp [decodeInt, step, hfold]

theorem decodeInt_renameAddresses_conc_of_some
    (resolve : ObjId → Nat) (t : IntTy) (bs : List UInt8) (v : Int)
    (h : decodeInt t (bs.map CByte.conc) = some v) :
    decodeInt t ((bs.map CByte.conc).map (CByte.renameAddress resolve)) =
      some v := by
  rw [decodeInt_renameAddresses_conc]
  exact h


/-- One byte of an object representation as observed through a character
lvalue.  Character accesses are allowed to inspect every object
representation, including pointer representations (§6.5.1p7).  The
pointer token is the model's ABI representation, so its byte order is the
profile's little-endian order used by integer encodings. -/
def characterByte : CByte → Option UInt8
  | .conc b => some b
  | .ptrByte p k => some (UInt8.ofNat (((Ptr.exposedAddress p).toNat / (256 ^ k)) % 256))
  | .ptrIntByte p k => some (UInt8.ofNat (((Ptr.exposedAddress p).toNat / (256 ^ k)) % 256))
  | .funByte id => none
  | .indet => none

def loadCharacter (m : Mem) (p : Ptr) (t : IntTy) : MRes CVal := do
  let (o, c, off) ← m.resolve p 1
  match (c.bytes.drop off).head?.bind characterByte with
  | some b => pure (.int t (t.wrap b.toNat))
  | none =>
      if (c.bytes.drop off).any (· == CByte.indet) then
        .error (.memUB (match c.dur with
          | .allocated => .indetAllocated o off
          | _ => .indetAutomatic o off))
      else .error (.memUB (.nonValueRepresentation o off))

theorem loadCharacter_renameAddresses_of_conc
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (t : IntTy)
    (o : ObjId) (c : CObj) (off : Nat) (b : UInt8)
    (hr : m.resolve p 1 = .ok (o, c, off))
    (hbytes : List.take 1 (List.drop off c.bytes) = [CByte.conc b]) :
    (m.renameAddresses rename).loadCharacter (Ptr.renameAddress rename p) t =
      .ok (.int t (t.wrap b.toNat)) := by
  simp only [loadCharacter, resolve_renameAddresses, hr]
  dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
    Except.pure, Except.map]
  have hmapped :
      List.take 1 (List.drop off (CObj.renameAddress rename c).bytes) =
        [CByte.conc b] := by
    simp only [CObj.renameAddress]
    simpa [List.map_take, List.map_drop] using congrArg
      (List.map (CByte.renameAddress rename)) hbytes
  have hhead :
      (List.drop off (CObj.renameAddress rename c).bytes).head? = some (CByte.conc b) := by
    have hh := congrArg List.head? hmapped
    simpa [List.head?_take] using hh
  rw [hhead]
  rfl

theorem decodeInt_indet (t : IntTy) (bs : List CByte)
    (h : CByte.indet ∈ bs) : decodeInt t bs = none := by
  let step := fun (b : CByte) (acc : Option (List UInt8)) =>
    match b, acc with
    | .conc x, some xs => some (x :: xs)
    | _, _ => none
  have hfold : bs.foldr step (some []) = none := by
    induction bs with
    | nil => simp at h
    | cons b bs ih =>
      simp only [List.mem_cons] at h
      simp only [List.foldr]
      cases b with
      | conc x =>
          simp only [step]
          cases h with
          | inl hneq => cases hneq
          | inr htail => rw [ih htail]
      | ptrByte p k => simp [step]
      | ptrIntByte p k => simp [step]
      | funByte id => simp [step]
      | indet => simp [step]
  simp [decodeInt, step, hfold]

def encodeFloat32 (f : Float32.Model) : List CByte :=
  (natToBytes 4 (f.toBits.toNat)).map CByte.conc

def encodeFloat64 (f : Float.Model) : List CByte :=
  (natToBytes 8 f.toBits.toNat).map CByte.conc

def decodeFloat32 (bs : List CByte) : Option Float32.Model :=
  if bs.any (fun b => match b with | .conc _ => false | _ => true) then none
  else some (Float32.Model.ofBits (UInt32.ofNat (natOfBytes (bs.map (fun b => match b with | .conc x => x | _ => 0)))))

def decodeFloat64 (bs : List CByte) : Option Float.Model :=
  if bs.any (fun b => match b with | .conc _ => false | _ => true) then none
  else some (Float.Model.ofBits (UInt64.ofNat (natOfBytes (bs.map (fun b => match b with | .conc x => x | _ => 0)))))

theorem decodeFloat32_renameAddresses (rename : ObjId → Nat) (bs : List CByte) :
    decodeFloat32 (bs.map (CByte.renameAddress rename)) = decodeFloat32 bs := by
  have hb : ∀ b : CByte,
      (match CByte.renameAddress rename b with | .conc _ => false | _ => true) =
        (match b with | .conc _ => false | _ => true) := by
    intro b
    cases b <;> rfl
  have hany :
      (bs.map (CByte.renameAddress rename)).any
          (fun b => match b with | .conc _ => false | _ => true) =
        bs.any (fun b => match b with | .conc _ => false | _ => true) := by
    rw [List.any_map]
    apply List.any_congr rfl
    exact hb
  have hbytes :
      (bs.map (CByte.renameAddress rename)).map
          (fun b => match b with | .conc x => x | _ => 0) =
        bs.map (fun b => match b with | .conc x => x | _ => 0) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro b hbmem
    cases b <;> rfl
  simp [decodeFloat32, hany, hbytes]

theorem decodeFloat64_renameAddresses (rename : ObjId → Nat) (bs : List CByte) :
    decodeFloat64 (bs.map (CByte.renameAddress rename)) = decodeFloat64 bs := by
  have hb : ∀ b : CByte,
      (match CByte.renameAddress rename b with | .conc _ => false | _ => true) =
        (match b with | .conc _ => false | _ => true) := by
    intro b
    cases b <;> rfl
  have hany :
      (bs.map (CByte.renameAddress rename)).any
          (fun b => match b with | .conc _ => false | _ => true) =
        bs.any (fun b => match b with | .conc _ => false | _ => true) := by
    rw [List.any_map]
    apply List.any_congr rfl
    exact hb
  have hbytes :
      (bs.map (CByte.renameAddress rename)).map
          (fun b => match b with | .conc x => x | _ => 0) =
        bs.map (fun b => match b with | .conc x => x | _ => 0) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro b hbmem
    cases b <;> rfl
  simp [decodeFloat64, hany, hbytes]

def loadFloat32 (m : Mem) (p : Ptr) : MRes CVal := do
  let bs ← m.loadBytes p 4
  match decodeFloat32 bs with
  | some f => pure (.float32 f)
  | none => .error (.memUB (.nonValueRepresentation (Option.getD p.obj 0) p.off.toNat))

def loadFloat64 (m : Mem) (p : Ptr) : MRes CVal := do
  let bs ← m.loadBytes p 8
  match decodeFloat64 bs with
  | some f => pure (.float64 f)
  | none => .error (.memUB (.nonValueRepresentation (Option.getD p.obj 0) p.off.toNat))

theorem loadFloat32_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) :
    (m.renameAddresses rename).loadFloat32 (Ptr.renameAddress rename p) =
      (m.loadFloat32 p).map (CVal.renameAddress rename) := by
  simp only [loadFloat32, loadBytes_renameAddresses]
  cases h : m.loadBytes p 4 with
  | error e =>
      dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
        Except.pure, Except.map]
  | ok bs =>
      dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
        Except.pure, Except.map]
      cases hdec : decodeFloat32 bs with
      | none => rw [decodeFloat32_renameAddresses, hdec]; rfl
      | some f => rw [decodeFloat32_renameAddresses, hdec]; rfl

theorem loadFloat64_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) :
    (m.renameAddresses rename).loadFloat64 (Ptr.renameAddress rename p) =
      (m.loadFloat64 p).map (CVal.renameAddress rename) := by
  simp only [loadFloat64, loadBytes_renameAddresses]
  cases h : m.loadBytes p 8 with
  | error e =>
      dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
        Except.pure, Except.map]
  | ok bs =>
      dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
        Except.pure, Except.map]
      cases hdec : decodeFloat64 bs with
      | none => rw [decodeFloat64_renameAddresses, hdec]; rfl
      | some f => rw [decodeFloat64_renameAddresses, hdec]; rfl

def storeFloat32 (m : Mem) (p : Ptr) (f : Float32.Model) : MRes Mem :=
  m.storeBytes p (encodeFloat32 f)

def storeFloat64 (m : Mem) (p : Ptr) (f : Float.Model) : MRes Mem :=
  m.storeBytes p (encodeFloat64 f)

/-! ### The typed accessors -/

/-- Which indeterminate-read fault a duration raises. `J.2(11)` names
AUTOMATIC storage; `J.2(185)` is `malloc`'s own entry. Keeping them apart
is the annex's own distinction, not a refinement of it. -/
def indetFault (dur : Duration) (o : ObjId) (off : Nat) : MemFault :=
  match dur with
  | .allocated => .indetAllocated o off
  | _ => .indetAutomatic o off

/-- The character-type exception in C23 §6.5.1p7.  This first memory
access slice compares the parser-carried type spellings exactly; the
declaration-identity normalizer supplies aliases before an object is
allocated, while an unrecognised spelling remains a loud mismatch. -/
structure AliasModel where
  /-- Whether an lvalue access type may inspect bytes carrying `eff`.
  Languages with a borrow or provenance discipline can supply another
  instance without changing the byte store. -/
  compatible : CType → CType → Bool
  /-- Structured parser evidence for the access type.  The legacy spelling
  arguments remain for envelopes produced before the QualType bridge. -/
  compatibleUsed : Option QualType → CType → CType → Bool :=
    fun _ used eff => compatible used eff

def isCharacterType : QualType → Bool
  | .qualified _ _ base => isCharacterType base
  | .cBuiltinKind .char | .cBuiltinKind .signedChar | .cBuiltinKind .unsignedChar => true
  | _ => false

def cAliasCompatible : CType → CType → Bool := fun used eff =>
    let unqual : CType → CType
      | "const char" | "volatile char" => "char"
      | "const signed char" | "volatile signed char" => "signed char"
      | "const unsigned char" | "volatile unsigned char" => "unsigned char"
      | "const short" | "volatile short" => "short"
      | "const unsigned short" | "volatile unsigned short" => "unsigned short"
      | "const int" | "volatile int" => "int"
      | "const unsigned int" | "volatile unsigned int" => "unsigned int"
      | "const long" | "volatile long" => "long"
      | "const unsigned long" | "volatile unsigned long" => "unsigned long"
      | "const long long" | "volatile long long" => "long long"
      | "const unsigned long long" | "volatile unsigned long long" => "unsigned long long"
      | "const _Bool" | "volatile _Bool" => "_Bool"
      | t => t
    let used' := unqual used
    let eff' := unqual eff
    let scalar := match eff' with
      | "char" | "signed char" | "unsigned char" | "short" |
          "unsigned short" | "int" | "unsigned int" | "long" |
          "unsigned long" | "long long" | "unsigned long long" | "_Bool" => true
      | _ => false
    scalar == false || used' == eff' || used' == "char" ||
      used' == "signed char" || used' == "unsigned char"

def cAliasCompatibleStructured : QualType → QualType → Bool := fun used eff =>
  isCharacterType used || used.unqualified == eff.unqualified

def cAliasModel : AliasModel where
  compatible := cAliasCompatible
  compatibleUsed := fun usedStructured used eff =>
    match usedStructured with
    | some structured => isCharacterType structured || cAliasCompatible used eff
    | none => cAliasCompatible used eff

def checkEffective (alias : AliasModel) (o : ObjId) (c : CObj) (off : Nat)
    (used : CType) (usedStructured : Option QualType := none) : MRes Unit :=
  match c.effTy with
  | none => .ok ()
  | some eff =>
      if alias.compatibleUsed usedStructured used eff then .ok ()
      else .error (.memUB (.effectiveType o off used eff))

def checkEffectiveAt (m : Mem) (alias : AliasModel) (o : ObjId) (c : CObj) (off : Nat)
    (used : CType) (usedStructured : Option QualType := none) : MRes Unit :=
  match m.structuredType? o, usedStructured with
  | some effective, some usedType =>
      if cAliasCompatibleStructured usedType effective then .ok ()
      else .error (.memUB (.effectiveType o off used (c.effTy.getD used)))
  | _, _ => checkEffective alias o c off used usedStructured

theorem checkEffectiveAt_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (alias : AliasModel) (o : ObjId)
    (c : CObj) (off : Nat) (used : CType) (usedStructured : Option QualType := none) :
    checkEffectiveAt (m.renameAddresses rename) alias o
        (CObj.renameAddress rename c) off used usedStructured =
      checkEffectiveAt m alias o c off used usedStructured := by
  simp [checkEffectiveAt, checkEffective, structuredType?, renameAddresses,
    CObj.renameAddress]

/-- The integer interpretation after structural resolution. -/
def loadIntResolved (t : IntTy) (o : ObjId) (c : CObj) (off : Nat) : MRes CVal :=
  let width := max 1 (t.bits / 8)
  let bs := (c.bytes.drop off).take width
  match decodeInt t bs with
  | some v => .ok (.int t v)
  | none =>
      if bs.any (· == CByte.indet) then
        .error (.memUB (indetFault c.dur o off))
      else
        .error (.memUB (.nonValueRepresentation o off))

theorem loadIntResolved_renameAddresses
    (rename : ObjId → Nat) (t : IntTy) (o : ObjId) (c : CObj) (off : Nat) :
    loadIntResolved t o (CObj.renameAddress rename c) off =
      (loadIntResolved t o c off).map (CVal.renameAddress rename) := by
  simp only [loadIntResolved, Except.map]
  have hbytes' :
      List.take (max 1 (t.bits / 8))
          (List.drop off (List.map (CByte.renameAddress rename) c.bytes)) =
        (List.take (max 1 (t.bits / 8)) (List.drop off c.bytes)).map
          (CByte.renameAddress rename) := by
    simp [List.map_take, List.map_drop, List.map_map]
  have hdecode :
      decodeInt t
          ((List.take (max 1 (t.bits / 8)) (List.drop off c.bytes)).map
            (CByte.renameAddress rename)) =
        decodeInt t (List.take (max 1 (t.bits / 8)) (List.drop off c.bytes)) := by
    exact decodeInt_renameAddresses rename t _
  have hany :
      (List.map (CByte.renameAddress rename)
        (List.take (max 1 (t.bits / 8)) (List.drop off c.bytes))).any
          (· == CByte.indet) =
        (List.take (max 1 (t.bits / 8)) (List.drop off c.bytes)).any
          (· == CByte.indet) := by
    rw [List.any_map]
    apply List.any_congr rfl
    intro b
    cases b <;> rfl
  simp only [CObj.renameAddress, hbytes']
  cases h : decodeInt t
      (List.take (max 1 (t.bits / 8)) (List.drop off c.bytes)) with
  | none =>
      rw [hdecode, h, hany]
      by_cases hi : ∃ x, x ∈ List.take (max 1 (t.bits / 8))
          (List.drop off c.bytes) ∧ (x == CByte.indet) = true <;>
        simp [hi]
  | some v =>
      rw [hdecode, h]
      simp

/-- Read an integer. C23 §6.3.2.1p2 (lvalue conversion) with
§6.2.6.1p5: three outcomes, and two of them refuse.

* all bytes `conc` → the value they represent;
* any `indet` byte → **`J.2(11)`/`J.2(185)`**, by storage duration;
* any pointer byte → **`J.2(12)`**, a non-value representation read by a
  non-character lvalue.

The corpus has exactly one site where the third could fire and one where
the second could; neither is detectable by any sanitizer on either
development host, which is why the byte lattice is here at all. -/
def loadInt (m : Mem) (p : Ptr) (t : IntTy) : MRes CVal := do
  let width := max 1 (t.bits / 8)
  let (o, c, off) ← m.resolve p width
  loadIntResolved t o c off

theorem loadInt_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (t : IntTy) :
    (m.renameAddresses rename).loadInt (Ptr.renameAddress rename p) t =
      (m.loadInt p t).map (CVal.renameAddress rename) := by
  simp only [loadInt]
  rw [resolve_renameAddresses]
  cases h : m.resolve p (max 1 (t.bits / 8)) with
  | error e =>
      simp only [h, Except.map, Except.instMonad, Except.bind, Except.pure]
      rfl
  | ok r =>
      cases r with
      | mk o rest =>
          cases rest with
          | mk c off =>
              simp only [h, Except.map, Except.instMonad, Except.bind, Except.pure]
              dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
                Except.pure, Except.map]
              exact loadIntResolved_renameAddresses rename t o c off

/-- Integer lvalue access with the §6.5.1p6-p7 effective-type check. -/
def loadIntChecked (m : Mem) (alias : AliasModel) (p : Ptr) (t : IntTy) (used : CType)
    (usedStructured : Option QualType := none) : MRes CVal := do
  let width := max 1 (t.bits / 8)
  let (o, c, off) ← m.resolve p width
  checkEffectiveAt m alias o c off used usedStructured
  loadIntResolved t o c off

theorem loadIntChecked_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (alias : AliasModel) (p : Ptr) (t : IntTy)
    (used : CType) (usedStructured : Option QualType := none) :
    (m.renameAddresses rename).loadIntChecked alias (Ptr.renameAddress rename p) t
        used usedStructured =
      (m.loadIntChecked alias p t used usedStructured).map
        (CVal.renameAddress rename) := by
  simp only [loadIntChecked]
  rw [resolve_renameAddresses]
  cases h : m.resolve p (max 1 (t.bits / 8)) with
  | error e =>
      simp only [h, Except.map, Except.instMonad, Except.bind, Except.pure]
      rfl
  | ok r =>
      cases r with
      | mk o rest =>
          cases rest with
          | mk c off =>
              simp only [h, Except.map, Except.instMonad, Except.bind, Except.pure]
              dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
                Except.pure, Except.map]
              simp only [checkEffectiveAt_renameAddresses]
              cases hEff : m.checkEffectiveAt alias o c off used usedStructured with
              | error e => simp [hEff]
              | ok u =>
                  simp only [hEff, Except.bind, Except.map, Except.pure]
                  exact loadIntResolved_renameAddresses rename t o c off

/-- Write an integer. -/
def storeInt (m : Mem) (p : Ptr) (t : IntTy) (v : Int) : MRes Mem :=
  m.storeBytes p (encodeInt t v)

/-- Integer store with effective-type establishment for allocated storage. -/
def storeIntChecked (m : Mem) (alias : AliasModel) (p : Ptr) (t : IntTy) (used : CType) (v : Int)
    (usedStructured : Option QualType := none) : MRes Mem := do
  let bs := encodeInt t v
  let (o, c, off) ← m.resolve p bs.length
  checkEffectiveAt m alias o c off used usedStructured
  let bytes := (c.bytes.take off) ++ bs ++ (c.bytes.drop (off + bs.length))
  -- Aggregate and declaration-backed objects have their effective type in
  -- the parser-native side table.  An allocated object with no declaration
  -- acquires the type of each non-character store under C17 §6.5p6.  Keep
  -- the legacy field as the fallback for envelopes without structured rows.
  let effTy := if (m.structuredType? o).isSome then c.effTy else some used
  return { m with objs := m.objs.set o { c with bytes := bytes, effTy := effTy } }

theorem storeIntChecked_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (alias : AliasModel) (p : Ptr) (t : IntTy)
    (used : CType) (v : Int) (usedStructured : Option QualType := none) :
    (m.renameAddresses rename).storeIntChecked alias (Ptr.renameAddress rename p) t used v
        usedStructured =
      (m.storeIntChecked alias p t used v usedStructured).map
        (Mem.renameAddresses rename) := by
  simp only [storeIntChecked]
  rw [resolve_renameAddresses]
  cases h : m.resolve p (encodeInt t v).length with
  | error e =>
      simp only [h, Except.map, Except.instMonad, Except.bind, Except.pure]
      rfl
  | ok r =>
      cases r with
      | mk o rest =>
          cases rest with
          | mk c off =>
              simp only [h, Except.map, Except.instMonad, Except.bind, Except.pure]
              dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
                Except.pure, Except.map]
              simp only [checkEffectiveAt_renameAddresses]
              cases hEff : m.checkEffectiveAt alias o c off used usedStructured with
              | error e => simp [hEff]
              | ok u =>
                  simp only [hEff, Except.bind, Except.map, Except.pure]
                  have henc :
                      (encodeInt t v).map (CByte.renameAddress rename) = encodeInt t v :=
                    encodeInt_renameAddresses rename t v
                  have hmap : ∀ xs : List UInt8,
                      (xs.map CByte.conc).map (CByte.renameAddress rename) =
                        xs.map CByte.conc := by
                    intro xs
                    induction xs <;> simp [Function.comp_def, CByte.renameAddress, *]
                  have hconc : ∀ xs : List UInt8,
                      xs.map CByte.conc = xs.map (fun x => CByte.conc x) := by
                    intro xs
                    rfl
                  simp [Mem.renameAddresses, CObj.renameAddress, encodeInt,
                    CByte.renameAddress, List.map_append, List.map_take, List.map_drop,
                    List.map_map, List.map_set, structuredType?, Function.comp_def, henc, hmap,
                    hconc]
                  rfl

theorem storeIntChecked_loadIntChecked_rename
    {m m' : Mem} (rename : ObjId → Nat) (alias : AliasModel) (p : Ptr)
    (t : IntTy) (used : CType) (v r : Int)
    (usedStructured : Option QualType := none)
    (hs : m.storeIntChecked alias p t used v usedStructured = .ok m')
    (hl : m'.loadIntChecked alias p t used usedStructured = .ok (.int t r)) :
    ((m.renameAddresses rename).storeIntChecked alias (Ptr.renameAddress rename p)
        t used v usedStructured >>= fun m'' =>
      m''.loadIntChecked alias (Ptr.renameAddress rename p) t used usedStructured) =
      (.ok (.int t r) : MRes CVal) := by
  dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
    Except.pure, Except.map]
  simp only [storeIntChecked_renameAddresses, hs, Except.map, Except.bind, Except.pure]
  simpa [hl, CVal.renameAddress, Except.map] using
    loadIntChecked_renameAddresses rename m' alias p t used usedStructured

/-- Write a pointer, as `pointer_64`'s eight tagged bytes. Kept whole so
that a partial overwrite makes the remaining bytes UNREADABLE as a
pointer rather than silently valid. -/
def storePtr (m : Mem) (p : Ptr) (q : Ptr) : MRes Mem :=
  m.storeBytes p ((List.range 8).map (CByte.ptrByte q))

/-! Function pointers are identities, not object addresses.  This token
survives storage in a struct field without inventing an ABI representation. -/
def storeFunction (m : Mem) (p : Ptr) (id : DeclarationId) : MRes Mem :=
  m.storeBytes p (List.replicate 8 (CByte.funByte id))

def loadFunction (m : Mem) (p : Ptr) : MRes (Option DeclarationId) := do
  let (_, c, off) ← m.resolve p 1
  match (c.bytes.drop off).head? with
  | some (.funByte id) =>
      let bytes := (c.bytes.drop off).take 8
      if bytes == List.replicate 8 (CByte.funByte id) then
        pure (some id)
      else
        .error (.memUB (.nonValueRepresentation (Option.getD p.obj 0) off))
  | _ => pure none

theorem loadFunction_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) :
    (m.renameAddresses rename).loadFunction (Ptr.renameAddress rename p) =
      (m.loadFunction p).map (fun x => x) := by
  have hlist : ∀ (id : LeanModels.C.DeclarationId) (xs : List CByte) (n : Nat),
      (xs.map (CByte.renameAddress rename) == List.replicate n (CByte.funByte id)) =
        (xs == List.replicate n (CByte.funByte id)) := by
    intro id xs
    induction xs with
    | nil => intro n; cases n <;> rfl
    | cons x xs ih =>
        intro n
        cases n with
        | zero => rfl
        | succ n =>
            simp only [List.map, List.replicate_succ, BEq.beq, List.beq]
            have hx := CByte.renameAddress_beq_funByte rename x id
            have hi := ih n
            have hx' : instBEqCByte.beq (CByte.renameAddress rename x) (CByte.funByte id) =
                instBEqCByte.beq x (CByte.funByte id) := by
              simpa only [BEq.beq] using hx
            have hi' : (List.map (CByte.renameAddress rename) xs).beq
                (List.replicate n (CByte.funByte id)) =
                xs.beq (List.replicate n (CByte.funByte id)) := by
              simpa only [BEq.beq] using hi
            rw [hx', hi']
  simp only [loadFunction]
  rw [resolve_renameAddresses]
  cases h : m.resolve p 1 with
  | error e =>
      dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
        Except.pure, Except.map]
  | ok r =>
      cases r with
      | mk o rest =>
          cases rest with
          | mk c off =>
              dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
                Except.pure, Except.map]
              have hhead :
                  (List.drop off (CObj.renameAddress rename c).bytes).head? =
                    Option.map (CByte.renameAddress rename) (List.drop off c.bytes).head? := by
                simp [CObj.renameAddress]
              have hbytes :
                  List.take 8 (List.drop off (CObj.renameAddress rename c).bytes) =
                    (List.take 8 (List.drop off c.bytes)).map (CByte.renameAddress rename) := by
                simp [CObj.renameAddress, List.map_take, List.map_drop, List.map_map]
              cases hh : (List.drop off c.bytes).head? with
              | none => rw [hhead, hh]; rfl
              | some b =>
                  cases b with
                  | funByte id =>
                      rw [hhead, hh]
                      simp only [Option.map, CByte.renameAddress]
                      rw [hbytes]
                      have hz := hlist id (List.take 8 (List.drop off c.bytes)) 8
                      simp only [List.replicate_succ, List.beq, BEq.beq] at hz ⊢
                      have hzr :
                          (List.map (CByte.renameAddress rename)
                            (List.take 8 (List.drop off c.bytes))).beq
                              (List.replicate 8 (CByte.funByte id)) =
                            (List.take 8 (List.drop off c.bytes)).beq
                              (List.replicate 8 (CByte.funByte id)) := by
                        simpa [BEq.beq, List.replicate_succ] using hz
                      have hzr' :
                          (List.map (CByte.renameAddress rename)
                            (List.take 8 (List.drop off c.bytes))).beq
                              [CByte.funByte id, CByte.funByte id, CByte.funByte id,
                               CByte.funByte id, CByte.funByte id, CByte.funByte id,
                               CByte.funByte id, CByte.funByte id] =
                            (List.take 8 (List.drop off c.bytes)).beq
                              [CByte.funByte id, CByte.funByte id, CByte.funByte id,
                               CByte.funByte id, CByte.funByte id, CByte.funByte id,
                               CByte.funByte id, CByte.funByte id] := by
                        simpa [List.replicate_succ] using hzr
                      simp only [hzr']
                      by_cases ho :
                          (List.take 8 (List.drop off c.bytes)).beq
                              [CByte.funByte id, CByte.funByte id, CByte.funByte id,
                               CByte.funByte id, CByte.funByte id, CByte.funByte id,
                               CByte.funByte id, CByte.funByte id] = true
                      · simp [ho, Ptr.renameAddress_obj]
                      · simp [ho, Ptr.renameAddress_obj]
                  | conc b => rw [hhead, hh]; rfl
                  | ptrByte q k => rw [hhead, hh]; rfl
                  | ptrIntByte q k => rw [hhead, hh]; rfl
                  | indet => rw [hhead, hh]; rfl

/-- Read a pointer: the eight bytes must be one pointer's representation,
in order. Anything else is `J.2(12)` — including a torn pointer, which
no sanitizer on either host detects. -/
theorem CByte.renameAddress_beq_indet
    (rename : ObjId → Nat) (b : CByte) :
    (CByte.renameAddress rename b == CByte.indet) = (b == CByte.indet) := by
  cases b <;> rfl

theorem List.any_renameAddress_indet
    (rename : ObjId → Nat) (bs : List CByte) :
    (bs.map (CByte.renameAddress rename)).any (· == CByte.indet) =
      bs.any (· == CByte.indet) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map, List.any]
      have hb := CByte.renameAddress_beq_indet rename b
      rw [show (CByte.renameAddress rename b == CByte.indet) =
          (b == CByte.indet) by exact hb, ih]

def loadPtr (m : Mem) (p : Ptr) : MRes Ptr := do
  let (o, c, off) ← m.resolve p 8
  let bs := (c.bytes.drop off).take 8
  let expected (q : Ptr) := (List.range 8).map (CByte.ptrByte q)
  match bs.head? with
  | some (.ptrByte q 0) => if bs == expected q then return q
                           else .error (.memUB (.nonValueRepresentation o off))
  | _ =>
      if bs.any (· == CByte.indet) then
        .error (.memUB (indetFault c.dur o off))
      else .error (.memUB (.nonValueRepresentation o off))

theorem loadPtr_renameAddresses_of_indet
    (rename : ObjId → Nat) (m : Mem) (p : Ptr)
    (o : ObjId) (c : CObj) (off : Nat) (bs : List CByte)
    (hr : m.resolve p 8 = .ok (o, c, off))
    (hbytes : List.take 8 (List.drop off c.bytes) = bs)
    (hhead : ∀ q, (bs.map (CByte.renameAddress rename)).head? ≠
      some (CByte.ptrByte q 0))
    (hany : bs.any (· == CByte.indet) = true) :
    (m.renameAddresses rename).loadPtr (Ptr.renameAddress rename p) =
      .error (.memUB (indetFault c.dur o off)) := by
  simp only [loadPtr, resolve_renameAddresses, hr]
  dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
    Except.pure, Except.map]
  have hmapped :
      List.take 8 (List.drop off (CObj.renameAddress rename c).bytes) =
        bs.map (CByte.renameAddress rename) := by
    simp only [CObj.renameAddress]
    simpa [List.map_take, List.map_drop] using congrArg
      (List.map (CByte.renameAddress rename)) hbytes
  rw [hmapped]
  have hany' :
      (bs.map (CByte.renameAddress rename)).any (· == CByte.indet) = true := by
    rw [List.any_renameAddress_indet]
    exact hany
  cases hh : (bs.map (CByte.renameAddress rename)).head? with
  | none =>
      simp [hh, hany', CObj.renameAddress]
  | some b =>
      cases b with
      | ptrByte q k =>
          cases k with
          | zero => exact False.elim (hhead q (by simpa [hh]))
          | succ k => simp [hh, hany', CObj.renameAddress]
      | _ => simp [hh, hany', CObj.renameAddress]

theorem loadPtr_renameAddresses_of_nonValue
    (rename : ObjId → Nat) (m : Mem) (p : Ptr)
    (o : ObjId) (c : CObj) (off : Nat) (bs : List CByte)
    (hr : m.resolve p 8 = .ok (o, c, off))
    (hbytes : List.take 8 (List.drop off c.bytes) = bs)
    (hhead : ∀ q, (bs.map (CByte.renameAddress rename)).head? ≠
      some (CByte.ptrByte q 0))
    (hany : (bs.map (CByte.renameAddress rename)).any
      (· == CByte.indet) ≠ true) :
    (m.renameAddresses rename).loadPtr (Ptr.renameAddress rename p) =
      .error (.memUB (.nonValueRepresentation o off)) := by
  simp only [loadPtr, resolve_renameAddresses, hr]
  dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
    Except.pure, Except.map]
  have hmapped :
      List.take 8 (List.drop off (CObj.renameAddress rename c).bytes) =
        bs.map (CByte.renameAddress rename) := by
    simp only [CObj.renameAddress]
    simpa [List.map_take, List.map_drop] using congrArg
      (List.map (CByte.renameAddress rename)) hbytes
  rw [hmapped]
  cases hh : (bs.map (CByte.renameAddress rename)).head? with
  | none => simp [hh, hany, CObj.renameAddress]
  | some b =>
      cases b with
      | ptrByte q k =>
          cases k with
          | zero => exact False.elim (hhead q (by simpa [hh]))
          | succ k => simp [hh, hany, CObj.renameAddress]
      | _ => simp [hh, hany, CObj.renameAddress]

theorem CByte.renameAddress_ptrByte_range
    (rename : ObjId → Nat) (q : Ptr) :
    ((List.range 8).map (CByte.ptrByte q)).map (CByte.renameAddress rename) =
      (List.range 8).map (CByte.ptrByte (Ptr.renameAddress rename q)) := by
  simp [CByte.renameAddress, Function.comp_def]

theorem CByte.renameAddress_ptrIntByte_range
    (rename : ObjId → Nat) (q : Ptr) :
    ((List.range 8).map (CByte.ptrIntByte q)).map (CByte.renameAddress rename) =
      (List.range 8).map (CByte.ptrIntByte (Ptr.renameAddress rename q)) := by
  simp [CByte.renameAddress, Function.comp_def]

theorem ptrByte_range_beq_self (q : Ptr) :
    ((List.range 8).map (CByte.ptrByte q)).beq
      ((List.range 8).map (CByte.ptrByte q)) = true := by
  have hq : (q == q) = true := by
    cases q with
    | mk obj address off bound =>
      cases obj with
      | none =>
        cases bound with
        | none =>
          change (true && (decide (address = address) &&
            (decide (off = off) && true))) = true
          simp
        | some b =>
          change (true && (decide (address = address) &&
            (decide (off = off) && decide (b = b)))) = true
          simp
      | some o =>
        cases bound with
        | none =>
          change (decide (o = o) && (decide (address = address) &&
            (decide (off = off) && true))) = true
          simp
        | some b =>
          change (decide (o = o) && (decide (address = address) &&
            (decide (off = off) && decide (b = b)))) = true
          simp
  have hb : ∀ (k : Nat), (CByte.ptrByte q k == CByte.ptrByte q k) = true := by
    intro k
    change (q == q && k == k) = true
    simp [hq]
  have hl : ∀ xs : List Nat,
      (xs.map (CByte.ptrByte q)).beq (xs.map (CByte.ptrByte q)) = true := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map, BEq.beq, List.beq]
        have hb' : instBEqCByte.beq (CByte.ptrByte q x)
            (CByte.ptrByte q x) = true := by
          simpa only [BEq.beq] using hb x
        rw [hb', ih]
        simp
  exact hl (List.range 8)

theorem loadPtr_renameAddresses_of_exact
    (rename : ObjId → Nat) (m : Mem) (p q : Ptr)
    (o : ObjId) (c : CObj) (off : Nat)
    (hr : m.resolve p 8 = .ok (o, c, off))
    (hbytes : List.take 8 (List.drop off c.bytes) =
      (List.range 8).map (CByte.ptrByte q)) :
    (m.renameAddresses rename).loadPtr (Ptr.renameAddress rename p) =
      .ok (Ptr.renameAddress rename q) := by
  simp only [loadPtr, resolve_renameAddresses, hr]
  dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
    Except.pure, Except.map]
  have hmapped :
      List.take 8 (List.drop off (CObj.renameAddress rename c).bytes) =
        (List.range 8).map (CByte.ptrByte (Ptr.renameAddress rename q)) := by
    simp only [CObj.renameAddress]
    have hslice :
        (List.map (CByte.renameAddress rename)
          (List.take 8 (List.drop off c.bytes))) =
        (List.range 8).map (CByte.ptrByte (Ptr.renameAddress rename q)) := by
      rw [hbytes]
      exact CByte.renameAddress_ptrByte_range rename q
    simpa [List.map_take, List.map_drop] using hslice
  rw [hmapped]
  have hself := ptrByte_range_beq_self (Ptr.renameAddress rename q)
  have hhead : ((List.range 8).map
      (CByte.ptrByte (Ptr.renameAddress rename q))).head? =
      some (CByte.ptrByte (Ptr.renameAddress rename q) 0) := by
    simp [List.range, List.range.loop]
  rw [hhead]
  simp only [Option.map, CByte.renameAddress]
  have hself' :
      (List.map (CByte.ptrByte (Ptr.renameAddress rename q)) (List.range 8) ==
        List.map (CByte.ptrByte (Ptr.renameAddress rename q)) (List.range 8)) = true := by
    simpa only [BEq.beq] using hself
  rw [if_pos hself']

theorem ptrIntByte_range_beq_self (q : Ptr) :
    ((List.range 8).map (CByte.ptrIntByte q)).beq
      ((List.range 8).map (CByte.ptrIntByte q)) = true := by
  have hq : (q == q) = true := by
    cases q with
    | mk obj address off bound =>
      cases obj with
      | none =>
        cases bound with
        | none =>
          change (true && (decide (address = address) &&
            (decide (off = off) && true))) = true
          simp
        | some b =>
          change (true && (decide (address = address) &&
            (decide (off = off) && decide (b = b)))) = true
          simp
      | some o =>
        cases bound with
        | none =>
          change (decide (o = o) && (decide (address = address) &&
            (decide (off = off) && true))) = true
          simp
        | some b =>
          change (decide (o = o) && (decide (address = address) &&
            (decide (off = off) && decide (b = b)))) = true
          simp
  have hb : ∀ (k : Nat), (CByte.ptrIntByte q k == CByte.ptrIntByte q k) = true := by
    intro k
    change (q == q && k == k) = true
    simp [hq]
  have hl : ∀ xs : List Nat,
      (xs.map (CByte.ptrIntByte q)).beq (xs.map (CByte.ptrIntByte q)) = true := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map, BEq.beq, List.beq]
        have hb' : instBEqCByte.beq (CByte.ptrIntByte q x)
            (CByte.ptrIntByte q x) = true := by
          simpa only [BEq.beq] using hb x
        rw [hb', ih]
        simp
  exact hl (List.range 8)

def storePtrInt (m : Mem) (p : Ptr) (q : Ptr) : MRes Mem :=
  m.storeBytes p ((List.range 8).map (CByte.ptrIntByte q))

theorem storeInt_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (t : IntTy) (v : Int) :
    (m.renameAddresses rename).storeInt (Ptr.renameAddress rename p) t v =
      (m.storeInt p t v).map (Mem.renameAddresses rename) := by
  simpa [storeInt, encodeInt, CByte.renameAddress, Function.comp_def] using
    (storeBytes_renameAddresses rename m p (encodeInt t v))

theorem storeFloat32_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (f : Float32.Model) :
    (m.renameAddresses rename).storeFloat32 (Ptr.renameAddress rename p) f =
      (m.storeFloat32 p f).map (Mem.renameAddresses rename) := by
  simpa [storeFloat32, encodeFloat32, CByte.renameAddress, Function.comp_def] using
    (storeBytes_renameAddresses rename m p (encodeFloat32 f))

theorem storeFloat64_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (f : Float.Model) :
    (m.renameAddresses rename).storeFloat64 (Ptr.renameAddress rename p) f =
      (m.storeFloat64 p f).map (Mem.renameAddresses rename) := by
  simpa [storeFloat64, encodeFloat64, CByte.renameAddress, Function.comp_def] using
    (storeBytes_renameAddresses rename m p (encodeFloat64 f))

theorem storePtr_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p q : Ptr) :
    (m.renameAddresses rename).storePtr (Ptr.renameAddress rename p)
        (Ptr.renameAddress rename q) =
      (m.storePtr p q).map (Mem.renameAddresses rename) := by
  simpa [storePtr, CByte.renameAddress, Ptr.renameAddress_comp, Function.comp_def] using
    (storeBytes_renameAddresses rename m p ((List.range 8).map (CByte.ptrByte q)))

theorem storePtrInt_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p q : Ptr) :
    (m.renameAddresses rename).storePtrInt (Ptr.renameAddress rename p)
        (Ptr.renameAddress rename q) =
      (m.storePtrInt p q).map (Mem.renameAddresses rename) := by
  simpa [storePtrInt, CByte.renameAddress, Ptr.renameAddress_comp, Function.comp_def] using
    (storeBytes_renameAddresses rename m p ((List.range 8).map (CByte.ptrIntByte q)))

theorem storeFunction_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (id : DeclarationId) :
    (m.renameAddresses rename).storeFunction (Ptr.renameAddress rename p) id =
      (m.storeFunction p id).map (Mem.renameAddresses rename) := by
  simpa [storeFunction, CByte.renameAddress, Function.comp_def] using
    (storeBytes_renameAddresses rename m p (List.replicate 8 (CByte.funByte id)))

def loadPtrInt (m : Mem) (p : Ptr) : MRes Ptr := do
  let (o, c, off) ← m.resolve p 8
  let bs := (c.bytes.drop off).take 8
  let expected (q : Ptr) := (List.range 8).map (CByte.ptrIntByte q)
  match bs.head? with
  | some (.ptrIntByte q 0) =>
      if bs == expected q then return q
      else .error (.memUB (.nonValueRepresentation o off))
  | _ =>
      if bs.any (· == CByte.indet) then
        .error (.memUB (indetFault c.dur o off))
      else .error (.memUB (.nonValueRepresentation o off))

theorem loadPtrInt_renameAddresses_of_exact
    (rename : ObjId → Nat) (m : Mem) (p q : Ptr)
    (o : ObjId) (c : CObj) (off : Nat)
    (hr : m.resolve p 8 = .ok (o, c, off))
    (hbytes : List.take 8 (List.drop off c.bytes) =
      (List.range 8).map (CByte.ptrIntByte q)) :
    (m.renameAddresses rename).loadPtrInt (Ptr.renameAddress rename p) =
      .ok (Ptr.renameAddress rename q) := by
  simp only [loadPtrInt, resolve_renameAddresses, hr]
  dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
    Except.pure, Except.map]
  have hmapped :
      List.take 8 (List.drop off (CObj.renameAddress rename c).bytes) =
        (List.range 8).map (CByte.ptrIntByte (Ptr.renameAddress rename q)) := by
    simp only [CObj.renameAddress]
    have hslice :
        (List.map (CByte.renameAddress rename)
          (List.take 8 (List.drop off c.bytes))) =
        (List.range 8).map (CByte.ptrIntByte (Ptr.renameAddress rename q)) := by
      rw [hbytes]
      exact CByte.renameAddress_ptrIntByte_range rename q
    simpa [List.map_take, List.map_drop] using hslice
  rw [hmapped]
  have hself := ptrIntByte_range_beq_self (Ptr.renameAddress rename q)
  have hhead : ((List.range 8).map
      (CByte.ptrIntByte (Ptr.renameAddress rename q))).head? =
      some (CByte.ptrIntByte (Ptr.renameAddress rename q) 0) := by
    simp [List.range, List.range.loop]
  rw [hhead]
  simp only [Option.map, CByte.renameAddress]
  have hself' :
      (List.map (CByte.ptrIntByte (Ptr.renameAddress rename q)) (List.range 8) ==
        List.map (CByte.ptrIntByte (Ptr.renameAddress rename q)) (List.range 8)) = true := by
    simpa only [BEq.beq] using hself
  rw [if_pos hself']

theorem loadPtrInt_renameAddresses_of_indet
    (rename : ObjId → Nat) (m : Mem) (p : Ptr)
    (o : ObjId) (c : CObj) (off : Nat) (bs : List CByte)
    (hr : m.resolve p 8 = .ok (o, c, off))
    (hbytes : List.take 8 (List.drop off c.bytes) = bs)
    (hhead : ∀ q, (bs.map (CByte.renameAddress rename)).head? ≠
      some (CByte.ptrIntByte q 0))
    (hany : bs.any (· == CByte.indet) = true) :
    (m.renameAddresses rename).loadPtrInt (Ptr.renameAddress rename p) =
      .error (.memUB (indetFault c.dur o off)) := by
  simp only [loadPtrInt, resolve_renameAddresses, hr]
  dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
    Except.pure, Except.map]
  have hmapped :
      List.take 8 (List.drop off (CObj.renameAddress rename c).bytes) =
        bs.map (CByte.renameAddress rename) := by
    simp only [CObj.renameAddress]
    simpa [List.map_take, List.map_drop] using congrArg
      (List.map (CByte.renameAddress rename)) hbytes
  rw [hmapped]
  have hany' :
      (bs.map (CByte.renameAddress rename)).any (· == CByte.indet) = true := by
    rw [List.any_renameAddress_indet]
    exact hany
  cases hh : (bs.map (CByte.renameAddress rename)).head? with
  | none =>
      simp [hh, hany', CObj.renameAddress]
  | some b =>
      cases b with
      | ptrIntByte q k =>
          cases k with
          | zero => exact False.elim (hhead q (by simpa [hh]))
          | succ k => simp [hh, hany', CObj.renameAddress]
      | _ => simp [hh, hany', CObj.renameAddress]

theorem loadPtrInt_renameAddresses_of_nonValue
    (rename : ObjId → Nat) (m : Mem) (p : Ptr)
    (o : ObjId) (c : CObj) (off : Nat) (bs : List CByte)
    (hr : m.resolve p 8 = .ok (o, c, off))
    (hbytes : List.take 8 (List.drop off c.bytes) = bs)
    (hhead : ∀ q, (bs.map (CByte.renameAddress rename)).head? ≠
      some (CByte.ptrIntByte q 0))
    (hany : (bs.map (CByte.renameAddress rename)).any
      (· == CByte.indet) ≠ true) :
    (m.renameAddresses rename).loadPtrInt (Ptr.renameAddress rename p) =
      .error (.memUB (.nonValueRepresentation o off)) := by
  simp only [loadPtrInt, resolve_renameAddresses, hr]
  dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind, Pure.pure,
    Except.pure, Except.map]
  have hmapped :
      List.take 8 (List.drop off (CObj.renameAddress rename c).bytes) =
        bs.map (CByte.renameAddress rename) := by
    simp only [CObj.renameAddress]
    simpa [List.map_take, List.map_drop] using congrArg
      (List.map (CByte.renameAddress rename)) hbytes
  rw [hmapped]
  cases hh : (bs.map (CByte.renameAddress rename)).head? with
  | none => simp [hh, hany, CObj.renameAddress]
  | some b =>
      cases b with
      | ptrIntByte q k =>
          cases k with
          | zero => exact False.elim (hhead q (by simpa [hh]))
          | succ k => simp [hh, hany, CObj.renameAddress]
      | _ => simp [hh, hany, CObj.renameAddress]


theorem storeBytes_structuredTypesUnique
    {m m' : Mem} {p : Ptr} {bs : List CByte}
    {o : ObjId} {c : CObj} {off : Nat}
    (hunique : structuredTypesUnique m)
    (hr : m.resolve p bs.length = .ok (o, c, off))
    (h : m.storeBytes p bs = .ok m') : structuredTypesUnique m' := by
  unfold storeBytes at h
  rw [hr] at h
  simp only [Except.bind, pure, Except.pure] at h
  cases h
  exact hunique

theorem storeBytes_structuredTypesUnique_of_ok
    {m m' : Mem} {p : Ptr} {bs : List CByte}
    (hunique : structuredTypesUnique m)
    (h : m.storeBytes p bs = .ok m') : structuredTypesUnique m' := by
  unfold storeBytes at h
  cases hr : m.resolve p bs.length with
  | error e =>
      simp [hr] at h
      cases h
  | ok result =>
    simp [hr] at h
    cases h
    exact hunique

theorem storeBytes_structuredType_lookup
    {m m' : Mem} {p : Ptr} {bs : List CByte} (q : ObjId)
    (h : m.storeBytes p bs = .ok m') :
    m'.structuredType? q = m.structuredType? q := by
  unfold storeBytes at h
  cases hr : m.resolve p bs.length with
  | error e =>
      simp [hr] at h
      cases h
  | ok result =>
    simp [hr] at h
    cases h
    rfl

theorem storeFloat32_structuredTypesUnique
    {m m' : Mem} {p : Ptr} {f : Float32.Model}
    (hunique : structuredTypesUnique m)
    (h : m.storeFloat32 p f = .ok m') : structuredTypesUnique m' := by
  exact storeBytes_structuredTypesUnique_of_ok hunique (by simpa [storeFloat32] using h)

theorem storeFloat64_structuredTypesUnique
    {m m' : Mem} {p : Ptr} {f : Float.Model}
    (hunique : structuredTypesUnique m)
    (h : m.storeFloat64 p f = .ok m') : structuredTypesUnique m' := by
  exact storeBytes_structuredTypesUnique_of_ok hunique (by simpa [storeFloat64] using h)

theorem storeInt_structuredTypesUnique
    {m m' : Mem} {p : Ptr} {t : IntTy} {v : Int}
    (hunique : structuredTypesUnique m)
    (h : m.storeInt p t v = .ok m') : structuredTypesUnique m' := by
  exact storeBytes_structuredTypesUnique_of_ok hunique (by simpa [storeInt] using h)

theorem storePtr_structuredTypesUnique
    {m m' : Mem} {p q : Ptr}
    (hunique : structuredTypesUnique m)
    (h : m.storePtr p q = .ok m') : structuredTypesUnique m' := by
  exact storeBytes_structuredTypesUnique_of_ok hunique (by simpa [storePtr] using h)

theorem storeFunction_structuredTypesUnique
    {m m' : Mem} {p : Ptr} {id : DeclarationId}
    (hunique : structuredTypesUnique m)
    (h : m.storeFunction p id = .ok m') : structuredTypesUnique m' := by
  exact storeBytes_structuredTypesUnique_of_ok hunique (by simpa [storeFunction] using h)

theorem storePtrInt_structuredTypesUnique
    {m m' : Mem} {p q : Ptr}
    (hunique : structuredTypesUnique m)
    (h : m.storePtrInt p q = .ok m') : structuredTypesUnique m' := by
  exact storeBytes_structuredTypesUnique_of_ok hunique (by simpa [storePtrInt] using h)

/-! ## §6.3.2.1p3 / §6.5.3 / §6.5.4 — making and moving pointers

Stated in census order: decay first, because it is 405 of the corpus's
pointer productions to `&`'s 106. -/

/-- **C23 §6.3.2.1p3 — array-to-pointer decay.** An expression of array
type is converted to a pointer to its initial element.

**The corpus's main pointer producer: 405 sites.** It is also why every
one of the 328 subscripts indexes an OBJECT rather than an address. -/
def decay (o : ObjId) : Ptr := Ptr.toObject o

/-- **C23 §6.5.4.2p3 — the address-of operator.** Yields a pointer to its
operand. Measured: 31 automatic, 55 file-scope, 20 subobject.

Definitionally equal to `decay`: §6.5.4.2p3 makes `&*p` and `&a[0]` the
same value as `p` and `a`, and stating them as one definition is what
stops every lemma below from being proved twice. -/
def addrOf (o : ObjId) : Ptr := Ptr.toObject o

/-- **C23 §6.5.3.4 — structure members.** `p->f` is DEFINED as `(*p).f`
(§6.5.3.4p4), so the 226 arrow sites and the 184 dot sites are one
operation with two spellings.

The offset is a parameter: struct layout is implementation-defined
(`J.3.10`), so it belongs to the profile and to the layout inch, not to
this one. -/
def member (p : Ptr) (fieldOff : Nat) : Ptr :=
  { p with off := p.off + (fieldOff : Int) }

@[simp] theorem member_address_irrel (p : Ptr) (fieldOff address : Nat) :
    (member {p with address := address} fieldOff).address = address := by
  simp [member]

def memberRange (p : Ptr) (fieldOff fieldSize : Nat) : Ptr :=
  let start := p.off + (fieldOff : Int)
  { p with off := start, bound := some (start + (fieldSize : Int)) }

@[simp] theorem memberRange_address_irrel (p : Ptr) (fieldOff fieldSize address : Nat) :
    (memberRange {p with address := address} fieldOff fieldSize).address = address := by
  simp [memberRange]

/-- **C23 §6.5.7p9 — pointer arithmetic**, and this is a constraint on
FORMING the pointer, not only on using it: the result must point into the
array or **one past its end**, else undefined (`J.2(43)`).

One-past-the-end is admitted here and refused by `resolve` on any access,
which is exactly §6.5.7p9's own split — the value is legal, the
dereference is not. -/
def offsetPtr (m : Mem) (p : Ptr) (elemSize : Nat) (i : Int) : MRes Ptr :=
  match p.obj with
  | none => .error (.memUB (.nullDeref p.off))
  | some o =>
    match m.get? o with
    | none => .error (.memUB (.nullDeref p.off))
    | some c =>
      let off := p.off + i * (elemSize : Int)
      if off < 0 then
        .error (.memUB (.outOfBounds o off elemSize c.size))
      else if off > (c.size : Int) then
        .error (.memUB (.outOfBounds o off elemSize c.size))
      else if off > (p.bound.getD (c.size : Int)) then
        -- `=` the subobject end is one-past-the-end: legal
        .error (.memUB (.outOfBounds o off elemSize c.size))
      else .ok { p with off := off }

/-- **C23 §6.5.3.2p2 — array subscripting.** `a[i]` is defined to be
`*(a + i)`, so it is `offsetPtr` and nothing else. Stated so the
mirror is visible, not because it computes anything new. -/
def subscript (m : Mem) (p : Ptr) (elemSize : Nat) (i : Int) : MRes Ptr :=
  m.offsetPtr p elemSize i

theorem offsetPtr_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (elemSize : Nat) (i : Int) :
    (m.renameAddresses rename).offsetPtr (Ptr.renameAddress rename p) elemSize i =
      (m.offsetPtr p elemSize i).map (Ptr.renameAddress rename) := by
  cases hp : p.obj with
  | none => simp [offsetPtr, hp, Ptr.renameAddress, Except.map]
  | some o =>
      cases hc : m.get? o with
      | none =>
          have hc' : (m.renameAddresses rename).get? o = none := by
            simpa [get?, renameAddresses] using
              congrArg (Option.map (CObj.renameAddress rename)) hc
          simp [offsetPtr, hp, hc, hc', Ptr.renameAddress, Except.map]
      | some c =>
          have hc' : (m.renameAddresses rename).get? o =
              some (CObj.renameAddress rename c) := by
            simpa [get?, renameAddresses] using
              congrArg (Option.map (CObj.renameAddress rename)) hc
          by_cases h1 : p.off + i * (elemSize : Int) < 0 <;>
            by_cases h2 : (c.size : Int) < p.off + i * (elemSize : Int) <;>
            by_cases h3 : p.bound.getD (c.size : Int) <
              p.off + i * (elemSize : Int)
          all_goals have hsize : c.size = c.bytes.length := rfl
          all_goals simp only [CObj.size] at h2 h3
          all_goals simp [offsetPtr, hp, hc, hc', Ptr.renameAddress,
            CObj.renameAddress, CObj.size, hsize, h1, h2, h3, Except.map]

theorem subscript_renameAddresses
    (rename : ObjId → Nat) (m : Mem) (p : Ptr) (elemSize : Nat) (i : Int) :
    (m.renameAddresses rename).subscript (Ptr.renameAddress rename p) elemSize i =
      (m.subscript p elemSize i).map (Ptr.renameAddress rename) := by
  simpa [subscript] using offsetPtr_renameAddresses rename m p elemSize i

/- Pointer arithmetic checks provenance, object bounds, and subobject bounds;
   the concrete placement is carried through a successful result but is not
   inspected by the checks or by their named refusals. -/
@[simp] theorem offsetPtr_address_irrel (m : Mem) (p : Ptr) (elemSize : Nat)
    (i : Int) (address : Nat) :
    m.offsetPtr {p with address := address} elemSize i =
      (m.offsetPtr p elemSize i).map (fun q => {q with address := address}) := by
  cases hobj : p.obj with
  | none => simp [offsetPtr, Except.map, hobj]
  | some o =>
    cases hget : m.get? o with
    | none => simp [offsetPtr, Except.map, hobj, hget]
    | some c =>
      by_cases h1 : p.off + i * (elemSize : Int) < 0 <;>
        by_cases h2 : (c.size : Int) < p.off + i * (elemSize : Int) <;>
        by_cases h3 : p.bound.getD (c.size : Int) < p.off + i * (elemSize : Int) <;>
        simp [offsetPtr, Except.map, hobj, hget, h1, h2, h3]

@[simp] theorem subscript_address_irrel (m : Mem) (p : Ptr) (elemSize : Nat)
    (i : Int) (address : Nat) :
    m.subscript {p with address := address} elemSize i =
      (m.subscript p elemSize i).map (fun q => {q with address := address}) := by
  simp [subscript, offsetPtr_address_irrel]

/-! ### §6.5.9 / §6.5.10 — comparing pointers, and the asymmetry

Two operators from the same clause family give OPPOSITE verdicts on the
same operands, which is the kind of thing a model gets wrong by being
tidy. -/

/-- **C23 §6.5.10p7 — equality.** Comparing pointers into unrelated
objects is fully DEFINED; they simply compare unequal, except for the
placement-dependent one-past/start case. The memory model has no concrete
addresses, so that case is detected and refused rather than assigned a
false result. -/
def ptrEq (a b : Ptr) : Bool := a.obj == b.obj && a.off == b.off

/-- Address independence for equality: C's equality rule observes
provenance and subobject offset, while the concrete placement is an
implementation choice. -/
@[simp] theorem ptrEq_address_irrel (a b : Ptr) (addressA addressB : Nat) :
    ptrEq {a with address := addressA} {b with address := addressB} = ptrEq a b := by
  simp [ptrEq]

/-- The memory store is addressed by provenance and offset, so changing the
placement annotation alone cannot change whether a range resolves. -/
@[simp] theorem resolve_address_irrel (m : Mem) (p : Ptr) (n : Nat)
    (address : Nat) :
    m.resolve {p with address := address} n = m.resolve p n := by
  simp [resolve]

@[simp] theorem loadBytes_address_irrel (m : Mem) (p : Ptr) (n address : Nat) :
    m.loadBytes {p with address := address} n = m.loadBytes p n := by
  simp [loadBytes, resolve_address_irrel]

@[simp] theorem storeBytes_address_irrel (m : Mem) (p : Ptr) (bs : List CByte)
    (address : Nat) :
    m.storeBytes {p with address := address} bs = m.storeBytes p bs := by
  simp [storeBytes, resolve_address_irrel]

theorem storeBytes_placement {m m' : Mem} {p : Ptr} {bs : List CByte}
    {o : ObjId} {c : CObj} {off : Nat}
    (hr : m.resolve p bs.length = .ok (o, c, off))
    (h : m.storeBytes p bs = .ok m') :
    m'.placements = m.placements := by
  unfold storeBytes at h
  rw [hr] at h
  simp only [Except.bind, pure, Except.pure] at h
  cases h
  rfl

theorem storeBytes_placement_lookup {m m' : Mem} {p : Ptr} {bs : List CByte}
    {o : ObjId} {c : CObj} {off : Nat} (q : ObjId)
    (hr : m.resolve p bs.length = .ok (o, c, off))
    (h : m.storeBytes p bs = .ok m') : m'.placement? q = m.placement? q := by
  have hp : m'.placements = m.placements := storeBytes_placement hr h
  unfold placement?
  simp only [hp]

theorem storeInt_placement {m m' : Mem} {p : Ptr} {t : IntTy} {v : Int}
    {o : ObjId} {c : CObj} {off : Nat}
    (hr : m.resolve p (encodeInt t v).length = .ok (o, c, off))
    (h : m.storeInt p t v = .ok m') : m'.placements = m.placements := by
  apply storeBytes_placement hr
  simpa [storeInt] using h

theorem storeInt_placement_lookup {m m' : Mem} {p : Ptr} {t : IntTy} {v : Int}
    {o : ObjId} {c : CObj} {off : Nat} (q : ObjId)
    (hr : m.resolve p (encodeInt t v).length = .ok (o, c, off))
    (h : m.storeInt p t v = .ok m') : m'.placement? q = m.placement? q := by
  exact storeBytes_placement_lookup q hr (by simpa [storeInt] using h)

theorem storeFloat32_placement {m m' : Mem} {p : Ptr} {f : Float32.Model}
    {o : ObjId} {c : CObj} {off : Nat}
    (hr : m.resolve p (encodeFloat32 f).length = .ok (o, c, off))
    (h : m.storeFloat32 p f = .ok m') : m'.placements = m.placements := by
  apply storeBytes_placement hr
  simpa [storeFloat32] using h

theorem storeFloat32_placement_lookup {m m' : Mem} {p : Ptr} {f : Float32.Model}
    {o : ObjId} {c : CObj} {off : Nat} (q : ObjId)
    (hr : m.resolve p (encodeFloat32 f).length = .ok (o, c, off))
    (h : m.storeFloat32 p f = .ok m') : m'.placement? q = m.placement? q := by
  exact storeBytes_placement_lookup q hr (by simpa [storeFloat32] using h)

theorem storeFloat64_placement {m m' : Mem} {p : Ptr} {f : Float.Model}
    {o : ObjId} {c : CObj} {off : Nat}
    (hr : m.resolve p (encodeFloat64 f).length = .ok (o, c, off))
    (h : m.storeFloat64 p f = .ok m') : m'.placements = m.placements := by
  apply storeBytes_placement hr
  simpa [storeFloat64] using h

theorem storeFloat64_placement_lookup {m m' : Mem} {p : Ptr} {f : Float.Model}
    {o : ObjId} {c : CObj} {off : Nat} (q : ObjId)
    (hr : m.resolve p (encodeFloat64 f).length = .ok (o, c, off))
    (h : m.storeFloat64 p f = .ok m') : m'.placement? q = m.placement? q := by
  exact storeBytes_placement_lookup q hr (by simpa [storeFloat64] using h)

theorem storePtr_placement {m m' : Mem} {p q : Ptr}
    {o : ObjId} {c : CObj} {off : Nat}
    (hr : m.resolve p 8 = .ok (o, c, off))
    (h : m.storePtr p q = .ok m') : m'.placements = m.placements := by
  exact storeBytes_placement (bs := (List.range 8).map (CByte.ptrByte q))
    (by simpa using hr) (by simpa [storePtr] using h)

theorem storePtr_placement_lookup {m m' : Mem} {p q : Ptr}
    {o : ObjId} {c : CObj} {off : Nat} (r : ObjId)
    (hr : m.resolve p 8 = .ok (o, c, off))
    (h : m.storePtr p q = .ok m') : m'.placement? r = m.placement? r := by
  exact storeBytes_placement_lookup r
    (bs := (List.range 8).map (CByte.ptrByte q)) (by simpa using hr)
    (by simpa [storePtr] using h)

theorem storeFunction_placement {m m' : Mem} {p : Ptr} {id : DeclarationId}
    {o : ObjId} {c : CObj} {off : Nat}
    (hr : m.resolve p 8 = .ok (o, c, off))
    (h : m.storeFunction p id = .ok m') : m'.placements = m.placements := by
  exact storeBytes_placement (bs := List.replicate 8 (CByte.funByte id))
    (by simpa using hr) (by simpa [storeFunction] using h)

theorem storeFunction_placement_lookup {m m' : Mem} {p : Ptr} {id : DeclarationId}
    {o : ObjId} {c : CObj} {off : Nat} (q : ObjId)
    (hr : m.resolve p 8 = .ok (o, c, off))
    (h : m.storeFunction p id = .ok m') : m'.placement? q = m.placement? q := by
  exact storeBytes_placement_lookup q
    (bs := List.replicate 8 (CByte.funByte id)) (by simpa using hr)
    (by simpa [storeFunction] using h)

theorem storePtrInt_placement {m m' : Mem} {p q : Ptr}
    {o : ObjId} {c : CObj} {off : Nat}
    (hr : m.resolve p 8 = .ok (o, c, off))
    (h : m.storePtrInt p q = .ok m') : m'.placements = m.placements := by
  exact storeBytes_placement (bs := (List.range 8).map (CByte.ptrIntByte q))
    (by simpa using hr) (by simpa [storePtrInt] using h)

theorem storePtrInt_placement_lookup {m m' : Mem} {p q : Ptr}
    {o : ObjId} {c : CObj} {off : Nat} (r : ObjId)
    (hr : m.resolve p 8 = .ok (o, c, off))
    (h : m.storePtrInt p q = .ok m') : m'.placement? r = m.placement? r := by
  exact storeBytes_placement_lookup r
    (bs := (List.range 8).map (CByte.ptrIntByte q)) (by simpa using hr)
    (by simpa [storePtrInt] using h)

@[simp] theorem loadInt_address_irrel (m : Mem) (p : Ptr) (t : IntTy)
    (address : Nat) :
    m.loadInt {p with address := address} t = m.loadInt p t := by
  simp [loadInt, resolve_address_irrel]

@[simp] theorem loadIntChecked_address_irrel (m : Mem) (alias : AliasModel)
    (p : Ptr) (t : IntTy) (used : CType) (address : Nat) :
    m.loadIntChecked alias {p with address := address} t used =
      m.loadIntChecked alias p t used := by
  simp [loadIntChecked, resolve_address_irrel]

@[simp] theorem storeInt_address_irrel (m : Mem) (p : Ptr) (t : IntTy)
    (v : Int) (address : Nat) :
    m.storeInt {p with address := address} t v = m.storeInt p t v := by
  simp [storeInt, storeBytes_address_irrel]

@[simp] theorem storeIntChecked_address_irrel (m : Mem) (alias : AliasModel)
    (p : Ptr) (t : IntTy) (used : CType) (v : Int) (address : Nat) :
    m.storeIntChecked alias {p with address := address} t used v =
      m.storeIntChecked alias p t used v := by
  simp [storeIntChecked, resolve_address_irrel]

@[simp] theorem loadFloat32_address_irrel (m : Mem) (p : Ptr) (address : Nat) :
    m.loadFloat32 {p with address := address} = m.loadFloat32 p := by
  simp [loadFloat32, loadBytes_address_irrel]

@[simp] theorem loadFloat64_address_irrel (m : Mem) (p : Ptr) (address : Nat) :
    m.loadFloat64 {p with address := address} = m.loadFloat64 p := by
  simp [loadFloat64, loadBytes_address_irrel]

@[simp] theorem storeFloat32_address_irrel (m : Mem) (p : Ptr)
    (f : Float32.Model) (address : Nat) :
    m.storeFloat32 {p with address := address} f = m.storeFloat32 p f := by
  simp [storeFloat32, storeBytes_address_irrel]

@[simp] theorem storeFloat64_address_irrel (m : Mem) (p : Ptr)
    (f : Float.Model) (address : Nat) :
    m.storeFloat64 {p with address := address} f = m.storeFloat64 p f := by
  simp [storeFloat64, storeBytes_address_irrel]

/- Pointer representations are read from abstract bytes; the destination
   pointer's concrete placement is not part of the access decision. -/
@[simp] theorem loadPtr_address_irrel (m : Mem) (p : Ptr) (address : Nat) :
    m.loadPtr {p with address := address} = m.loadPtr p := by
  simp [loadPtr, resolve_address_irrel]

@[simp] theorem loadPtrInt_address_irrel (m : Mem) (p : Ptr) (address : Nat) :
    m.loadPtrInt {p with address := address} = m.loadPtrInt p := by
  simp [loadPtrInt, resolve_address_irrel]

@[simp] theorem loadFunction_address_irrel (m : Mem) (p : Ptr) (address : Nat) :
    m.loadFunction {p with address := address} = m.loadFunction p := by
  simp [loadFunction, resolve_address_irrel]

@[simp] theorem storePtr_address_irrel (m : Mem) (p q : Ptr) (address : Nat) :
    m.storePtr {p with address := address} q = m.storePtr p q := by
  simp [storePtr, storeBytes_address_irrel]

@[simp] theorem storePtrInt_address_irrel (m : Mem) (p q : Ptr) (address : Nat) :
    m.storePtrInt {p with address := address} q = m.storePtrInt p q := by
  simp [storePtrInt, storeBytes_address_irrel]

@[simp] theorem storeFunction_address_irrel (m : Mem) (p : Ptr)
    (id : DeclarationId) (address : Nat) :
    m.storeFunction {p with address := address} id = m.storeFunction p id := by
  simp [storeFunction, storeBytes_address_irrel]

def ptrEqBoundary (m : Mem) (a b : Ptr) : Bool :=
  match a.obj, b.obj with
  | some x, some y =>
      if x == y then false
      else
        let onePast (p : Ptr) (o : ObjId) :=
          match m.get? o with
          | some c => p.off == p.bound.getD (c.size : Int)
          | none => false
        (onePast a x && b.off == 0) || (onePast b y && a.off == 0)
  | _, _ => false

theorem ptrEq_renameAddresses
    (rename : ObjId → Nat) (a b : Ptr) :
    ptrEq (Ptr.renameAddress rename a) (Ptr.renameAddress rename b) =
      ptrEq a b := by
  simp [ptrEq, Ptr.renameAddress]

@[simp] theorem ptrEqBoundary_address_irrel (m : Mem) (a b : Ptr)
    (addressA addressB : Nat) :
    ptrEqBoundary m {a with address := addressA} {b with address := addressB} =
      ptrEqBoundary m a b := by
  simp [ptrEqBoundary]

/-- **C23 §6.5.9p6 — relational.** Comparing pointers into DIFFERENT
objects with `<`, `>`, `<=` or `>=` is UNDEFINED — "in all other cases,
the behavior is undefined" (`J.2(45)`).

**The opposite verdict from `ptrEq` on the same operands.** -/
def ptrLt (a b : Ptr) : MRes Bool :=
  match a.obj, b.obj with
  | some x, some y => if x == y then .ok (a.off < b.off)
                      else .error (.memUB (.relationalAcrossObjects a b))
  | _, _ => .error (.memUB (.relationalAcrossObjects a b))

def renameAddressResult (r : MRes Bool) (addressA addressB : Nat) : MRes Bool :=
  match r with
  | .error (.memUB (.relationalAcrossObjects a b)) =>
      .error (.memUB (.relationalAcrossObjects
        {a with address := addressA} {b with address := addressB}))
  | other => other

/- On the defined same-object path, relational comparison ignores concrete
   placement.  Cross-object refusals retain the offending pointer in their
   diagnostic, so the unrestricted equality is intentionally not claimed. -/
theorem ptrLt_same_object_address_irrel (a b : Ptr) (addressA addressB : Nat)
    (h : ∃ o, a.obj = some o ∧ b.obj = some o) :
    ptrLt {a with address := addressA} {b with address := addressB} =
      .ok (a.off < b.off) := by
  obtain ⟨o, ha, hb⟩ := h
  simp [ptrLt, ha, hb]

/-! ## §7.24.3 Memory management functions

C23 §7.24.3p1: "The lifetime of an allocated object extends from the
allocation until the deallocation." Note the clause NUMBER — C17's 7.24
is `<string.h>`; C23's is `<stdlib.h>`, so a stale citation retargets
silently instead of failing (`docs/c23-spec-mirror.md` §4.3). -/

/-- §7.24.3.6 `malloc`: indeterminate representation, no declared type. -/
def malloc (m : Mem) (size : Nat) : Mem × Ptr :=
  let (m', o) := m.alloc .allocated size none
  (m', Ptr.toObjectBound o size)

def mallocAt (m : Mem) (size address : Nat) : Mem × Ptr :=
  m.allocAt .allocated size none address

/-- §7.24.3.2 `calloc`: all bits zero. -/
def calloc (m : Mem) (n size : Nat) : Mem × Ptr :=
  let (m', o) := m.allocZeroed .allocated (n * size) none
  (m', Ptr.toObjectBound o (n * size))

def callocAt (m : Mem) (n size address : Nat) : Mem × Ptr :=
  m.allocZeroedAt .allocated (n * size) none address

@[simp] theorem malloc_structuredTypesUnique
    (m : Mem) (size : Nat) (h : structuredTypesUnique m) :
    structuredTypesUnique (m.malloc size).1 := by
  simpa [malloc] using alloc_structuredTypesUnique m .allocated size none h

@[simp] theorem malloc_structuredType_lookup
    (m : Mem) (size q : Nat) :
    (m.malloc size).1.structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem calloc_structuredTypesUnique
    (m : Mem) (n size : Nat) (h : structuredTypesUnique m) :
    structuredTypesUnique (m.calloc n size).1 := by
  simpa [calloc] using allocZeroed_structuredTypesUnique m .allocated (n * size) none h

@[simp] theorem calloc_structuredType_lookup
    (m : Mem) (n size q : Nat) :
    (m.calloc n size).1.structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem mallocAt_structuredTypesUnique
    (m : Mem) (size address : Nat) (h : structuredTypesUnique m) :
    structuredTypesUnique (m.mallocAt size address).1 := by
  simpa [mallocAt] using allocAt_structuredTypesUnique m .allocated size none address h

@[simp] theorem mallocAt_structuredType_lookup
    (m : Mem) (size address q : Nat) :
    (m.mallocAt size address).1.structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem callocAt_structuredTypesUnique
    (m : Mem) (n size address : Nat) (h : structuredTypesUnique m) :
    structuredTypesUnique (m.callocAt n size address).1 := by
  simpa [callocAt] using
    allocZeroedAt_structuredTypesUnique m .allocated (n * size) none address h

@[simp] theorem callocAt_structuredType_lookup
    (m : Mem) (n size address q : Nat) :
    (m.callocAt n size address).1.structuredType? q = m.structuredType? q := by
  rfl

@[simp] theorem mallocAt_address (m : Mem) (size address : Nat) :
    (m.mallocAt size address).2.address = address := by
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt]

@[simp] theorem callocAt_address (m : Mem) (n size address : Nat) :
    (m.callocAt n size address).2.address = address := by
  simp [callocAt, allocZeroedAt, Ptr.toObjectBoundAt]

@[simp] theorem mallocAt_provenance (m : Mem) (size address : Nat) :
    (m.mallocAt size address).2.obj =
      some (m.alloc .allocated size none).2 := by
  simp [mallocAt, allocAt, Ptr.toObjectBoundAt]


@[simp] theorem callocAt_provenance (m : Mem) (n size address : Nat) :
    (m.callocAt n size address).2.obj =
      some (m.allocZeroed .allocated (n * size) none).2 := by
  simp [callocAt, allocZeroedAt, Ptr.toObjectBoundAt]


@[simp] theorem mallocAt_placement_irrel (m : Mem) (size address₁ address₂ : Nat) :
    let p₁ := (m.mallocAt size address₁).2
    let p₂ := (m.mallocAt size address₂).2
    p₁.obj = p₂.obj ∧ p₁.off = p₂.off ∧ p₁.bound = p₂.bound := by
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt]

@[simp] theorem callocAt_placement_irrel (m : Mem) (n size address₁ address₂ : Nat) :
    let p₁ := (m.callocAt n size address₁).2
    let p₂ := (m.callocAt n size address₂).2
    p₁.obj = p₂.obj ∧ p₁.off = p₂.off ∧ p₁.bound = p₂.bound := by
  simp [callocAt, allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt]

/-- §7.24.3.3 `free`. Refuses a pointer no allocation returned, or one
already freed (**`J.2(184)`**). A null pointer is accepted and does
nothing, per §7.24.3.3p2. -/
def free (m : Mem) (p : Ptr) : MRes Mem :=
  match p.obj with
  | none => .ok m                                  -- §7.24.3.3p2: free(NULL) is a no-op
  | some o =>
    match m.get? o with
    | some c => if c.dur == .allocated && c.live && p.off == 0
                then .ok (m.kill o)
                else .error (.memUB (.freeUnmatched p))
    | none => .error (.memUB (.freeUnmatched p))

theorem free_structuredTypesUnique
    {m m' : Mem} {p : Ptr} (h : structuredTypesUnique m)
    (hr : m.free p = .ok m') : structuredTypesUnique m' := by
  unfold free at hr
  split at hr
  · cases hr
    exact h
  · split at hr
    · split at hr
      · cases hr
        exact kill_structuredTypesUnique m _ h
      · simp_all
    · simp_all

theorem free_structuredType_lookup
    {m m' : Mem} {p : Ptr} (q : ObjId)
    (hr : m.free p = .ok m') : m'.structuredType? q = m.structuredType? q := by
  unfold free at hr
  split at hr
  · cases hr
    rfl
  · split at hr
    · split at hr
      · cases hr
        rfl
      · simp_all
    · simp_all

@[simp] theorem free_null (m : Mem) :
    m.free Ptr.null = .ok m := by
  simp [free, Ptr.null]

@[simp] theorem free_null_address_irrel (m : Mem) (address : Nat) :
    m.free {Ptr.null with address := address} = .ok m := by
  simp [free, Ptr.null]

@[simp] theorem free_null_placement_lookup (m : Mem) (q : ObjId) :
    (m.free Ptr.null).map (fun m' => m'.placement? q) =
      .ok (m.placement? q) := by
  simp [Except.map]

@[simp] theorem free_null_placementValid (m : Mem)
    (address size alignment : Nat) :
    (m.free Ptr.null).map
        (fun m' => placementValid m' address size alignment) =
      .ok (placementValid m address size alignment) := by
  simp [Except.map]

@[simp] theorem free_null_objects (m : Mem) :
    (m.free Ptr.null).map (fun m' => m'.objs) = .ok m.objs := by
  simp [Except.map]

/- Concrete placement does not participate in C's successful `free` path:
   object identity, lifetime, and base offset determine the result. -/
theorem free_valid_address_irrel (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (address : Nat) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    m.free {p with address := address} = .ok (m.kill o) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  simp [free, hp, hc, hdur, hlive, hoff, hbeq]

theorem free_valid_placements (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map Mem.placements = .ok m.placements := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  change (.ok (m.kill o).placements : MRes (List (ObjId × Nat))) = .ok m.placements
  rw [kill_placements]

theorem free_valid_objects (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.objs) = .ok (m.kill o).objs := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  rfl

theorem free_valid_resolve (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (n : Nat) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.resolve p n) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [resolve, hp, hk]

theorem free_valid_loadBytes (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (n : Nat) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.loadBytes p n) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [loadBytes, resolve, hp, hk]
  rfl

theorem free_valid_storeBytes (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (bs : List CByte) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.storeBytes p bs) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [storeBytes, resolve, hp, hk]
  rfl

theorem free_valid_loadInt (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (t : IntTy) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.loadInt p t) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [loadInt, resolve, hp, hk]
  rfl

theorem free_valid_storeInt (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (t : IntTy) (v : Int) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.storeInt p t v) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [storeInt, storeBytes, resolve, hp, hk]
  rfl

theorem free_valid_loadPtr (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.loadPtr p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [loadPtr, resolve, hp, hk]
  rfl

theorem free_valid_storePtr (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (q : Ptr) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.storePtr p q) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [storePtr, storeBytes, resolve, hp, hk]
  rfl

theorem free_valid_loadFloat32 (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.loadFloat32 p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [loadFloat32, loadBytes, resolve, hp, hk]
  rfl

theorem free_valid_loadFloat64 (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.loadFloat64 p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [loadFloat64, loadBytes, resolve, hp, hk]
  rfl

theorem free_valid_storeFloat32 (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (f : Float32.Model) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.storeFloat32 p f) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [storeFloat32, storeBytes, resolve, hp, hk]
  rfl

theorem free_valid_storeFloat64 (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (f : Float.Model) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.storeFloat64 p f) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [storeFloat64, storeBytes, resolve, hp, hk]
  rfl

theorem free_valid_loadPtrInt (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.loadPtrInt p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [loadPtrInt, resolve, hp, hk]
  rfl

theorem free_valid_storePtrInt (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (q : Ptr) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.storePtrInt p q) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [storePtrInt, storeBytes, resolve, hp, hk]
  rfl

theorem free_valid_loadFunction (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.loadFunction p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [loadFunction, resolve, hp, hk]
  rfl

theorem free_valid_storeFunction (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (id : DeclarationId) (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.storeFunction p id) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [storeFunction, storeBytes, resolve, hp, hk]
  rfl

theorem free_valid_loadIntChecked (m : Mem) (alias : AliasModel)
    (p : Ptr) (o : ObjId) (c : CObj) (t : IntTy) (used : CType)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.loadIntChecked alias p t used) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [loadIntChecked, resolve, hp, hk]
  rfl

theorem free_valid_storeIntChecked (m : Mem) (alias : AliasModel)
    (p : Ptr) (o : ObjId) (c : CObj) (t : IntTy) (used : CType) (v : Int)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.storeIntChecked alias p t used v) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  simp only [Except.map, Except.ok.injEq]
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [storeIntChecked, resolve, hp, hk]
  rfl

theorem free_valid_placement_lookup (m : Mem) (p : Ptr) (o q : ObjId) (c : CObj)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (m.free p).map (fun m' => m'.placement? q) = .ok (m.placement? q) := by
  have h : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [h]
  change (.ok ((m.kill o).placement? q) : MRes (Option Nat)) = .ok (m.placement? q)
  rw [kill_placement_lookup]

theorem free_valid_placementValid (m : Mem) (p : Ptr) (o : ObjId) (c : CObj)
    (address size alignment : Nat)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0)
    (hvalid : placementValid m address size alignment = true) :
    (m.free p).map (fun m' => placementValid m' address size alignment) = .ok true := by
  have hf : m.free p = .ok (m.kill o) := by
    simpa using free_valid_address_irrel m p o c p.address hp hc hdur hlive hoff
  rw [hf]
  simp only [Except.map, Except.ok.injEq]
  exact placementValid_kill m o address size alignment hvalid

/-- §7.24.3.7 `realloc` — **and this is why pointers carry provenance.**

The corpus reallocates the transposition table on the search path
(sunfish.c L453-454), so the old object DIES and a fresh object receives
the copied bytes. Every pointer derived from the old object must stop
working, and here it does: the old id becomes a tombstone and any access
through it raises `J.2(10)`. An `Addr := Nat` model cannot express that
because the new block might reuse the number.

§7.24.3.7p3: a zero size is UNDEFINED in C23 (it was not in C17), and
**Annex J has no entry for it** — so `reallocZero`'s `j2` is `none`. -/
def realloc (m : Mem) (p : Ptr) (size : Nat) : MRes (Mem × Ptr) :=
  if size == 0 then .error (.memUB (.reallocZero p)) else
  match p.obj with
  | none => .ok (m.malloc size)                    -- §7.24.3.7p3: behaves like malloc
  | some o =>
    match m.get? o with
    | some c =>
      if c.dur == .allocated && c.live && p.off == 0 then
        let keep := c.bytes.take size
        let fresh := keep ++ List.replicate (size - keep.length) CByte.indet
        let newO := m.objs.length
        let m' : Mem := { m with
          objs := m.objs ++ [⟨.allocated, true, fresh, none⟩]
          placements := m.placements ++ [(newO, newO)] }
        .ok ((m'.copyStructuredType o newO).kill o,
          Ptr.toObjectBound m.objs.length size)
      else .error (.memUB (.freeUnmatched p))
    | none => .error (.memUB (.freeUnmatched p))

/-- Explicit-placement variant of realloc.  The fresh allocation address is
chosen by the caller; the old object still dies and provenance changes. -/
def reallocAt (m : Mem) (p : Ptr) (size address : Nat) : MRes (Mem × Ptr) :=
  if size == 0 then .error (.memUB (.reallocZero p)) else
  match p.obj with
  | none => .ok (m.mallocAt size address)
  | some o =>
    match m.get? o with
    | some c =>
      if c.dur == .allocated && c.live && p.off == 0 then
        let keep := c.bytes.take size
        let fresh := keep ++ List.replicate (size - keep.length) CByte.indet
        let newO := m.objs.length
        let m' : Mem := { m with
          objs := m.objs ++ [⟨.allocated, true, fresh, none⟩]
          placements := placementSet m.placements newO address }
        .ok ((m'.copyStructuredType o newO).kill o,
          Ptr.toObjectBoundAt m.objs.length address size)
      else .error (.memUB (.freeUnmatched p))
    | none => .error (.memUB (.freeUnmatched p))

/-! ### S3 memory contract

`AddressIndependent` packages the pointwise placement-irrelevance facts used
by the evaluator theorem. Destination placement remains an explicit argument
of `reallocAt` and is therefore not quantified here. -/
structure AddressIndependent (m : Mem) : Prop where
  resolve : ∀ (p : Ptr) (n address : Nat),
    m.resolve {p with address := address} n = m.resolve p n
  loadBytes : ∀ (p : Ptr) (n address : Nat),
    m.loadBytes {p with address := address} n = m.loadBytes p n
  vaValues : ∀ (p : Ptr) (address : Nat),
    m.vaValues {p with address := address} = m.vaValues p
  loadCharacter : ∀ (p : Ptr) (t : IntTy) (address : Nat),
    m.loadCharacter {p with address := address} t = m.loadCharacter p t
  offsetPtr : ∀ (p : Ptr) (elemSize : Nat) (i : Int) (address : Nat),
    m.offsetPtr {p with address := address} elemSize i =
      (m.offsetPtr p elemSize i).map (fun q => {q with address := address})
  subscript : ∀ (p : Ptr) (elemSize : Nat) (i : Int) (address : Nat),
    m.subscript {p with address := address} elemSize i =
      (m.subscript p elemSize i).map (fun q => {q with address := address})
  ptrEq : ∀ (a b : Ptr) (addressA addressB : Nat),
    ptrEq {a with address := addressA} {b with address := addressB} = ptrEq a b
  ptrEqBoundary : ∀ (a b : Ptr) (addressA addressB : Nat),
    ptrEqBoundary m {a with address := addressA} {b with address := addressB} =
      ptrEqBoundary m a b
  ptrLtSameObject : ∀ (a b : Ptr) (addressA addressB : Nat),
    (∃ o, a.obj = some o ∧ b.obj = some o) →
    ptrLt {a with address := addressA} {b with address := addressB} =
      .ok (a.off < b.off)
  storeBytes : ∀ (p : Ptr) (bs : List CByte) (address : Nat),
    m.storeBytes {p with address := address} bs = m.storeBytes p bs
  loadIntChecked : ∀ (alias : AliasModel) (p : Ptr) (t : IntTy)
    (used : CType) (address : Nat),
    m.loadIntChecked alias {p with address := address} t used =
      m.loadIntChecked alias p t used
  storeIntChecked : ∀ (alias : AliasModel) (p : Ptr) (t : IntTy)
    (used : CType) (v : Int) (address : Nat),
    m.storeIntChecked alias {p with address := address} t used v =
      m.storeIntChecked alias p t used v
  storeInt : ∀ (p : Ptr) (t : IntTy) (v : Int) (address : Nat),
    m.storeInt {p with address := address} t v = m.storeInt p t v
  loadInt : ∀ (p : Ptr) (t : IntTy) (address : Nat),
    m.loadInt {p with address := address} t = m.loadInt p t
  loadPtr : ∀ (p : Ptr) (address : Nat),
    m.loadPtr {p with address := address} = m.loadPtr p
  loadPtrInt : ∀ (p : Ptr) (address : Nat),
    m.loadPtrInt {p with address := address} = m.loadPtrInt p
  loadFunction : ∀ (p : Ptr) (address : Nat),
    m.loadFunction {p with address := address} = m.loadFunction p
  loadFloat32 : ∀ (p : Ptr) (address : Nat),
    m.loadFloat32 {p with address := address} = m.loadFloat32 p
  loadFloat64 : ∀ (p : Ptr) (address : Nat),
    m.loadFloat64 {p with address := address} = m.loadFloat64 p
  storePtr : ∀ (p q : Ptr) (address : Nat),
    m.storePtr {p with address := address} q = m.storePtr p q
  storePtrInt : ∀ (p q : Ptr) (address : Nat),
    m.storePtrInt {p with address := address} q = m.storePtrInt p q
  storeFunction : ∀ (p : Ptr) (id : DeclarationId) (address : Nat),
    m.storeFunction {p with address := address} id = m.storeFunction p id
  storeFloat32 : ∀ (p : Ptr) (f : Float32.Model) (address : Nat),
    m.storeFloat32 {p with address := address} f = m.storeFloat32 p f
  storeFloat64 : ∀ (p : Ptr) (f : Float.Model) (address : Nat),
    m.storeFloat64 {p with address := address} f = m.storeFloat64 p f
  vaStart : ∀ (p : Ptr) (args : List CVal) (address : Nat),
    m.vaStart {p with address := address} args = m.vaStart p args
  vaCopy : ∀ (dst src : Ptr) (addressDst addressSrc : Nat),
    m.vaCopy {dst with address := addressDst} {src with address := addressSrc} =
      m.vaCopy dst src
  vaEnd : ∀ (p : Ptr) (address : Nat),
    m.vaEnd {p with address := address} = m.vaEnd p
  vaArg : ∀ (p : Ptr) (address : Nat),
    m.vaArg {p with address := address} = m.vaArg p

theorem addressIndependent_mem (m : Mem) : AddressIndependent m := by
  constructor
  · exact fun p n address => resolve_address_irrel m p n address
  · exact fun p n address => loadBytes_address_irrel m p n address
  · exact fun p address => vaValues_address_irrel m p address
  · exact fun p t address => by
      simp [loadCharacter, resolve_address_irrel]
  · exact fun p elemSize i address =>
      offsetPtr_address_irrel m p elemSize i address
  · exact fun p elemSize i address =>
      subscript_address_irrel m p elemSize i address
  · exact fun a b addressA addressB => ptrEq_address_irrel a b addressA addressB
  · exact fun a b addressA addressB =>
      ptrEqBoundary_address_irrel m a b addressA addressB
  · exact fun a b addressA addressB h =>
      ptrLt_same_object_address_irrel a b addressA addressB h
  · exact fun p bs address => storeBytes_address_irrel m p bs address
  · exact fun alias p t used address =>
      loadIntChecked_address_irrel m alias p t used address
  · exact fun alias p t used v address =>
      storeIntChecked_address_irrel m alias p t used v address
  · exact fun p t v address => storeInt_address_irrel m p t v address
  · exact fun p t address => loadInt_address_irrel m p t address
  · exact fun p address => loadPtr_address_irrel m p address
  · exact fun p address => loadPtrInt_address_irrel m p address
  · exact fun p address => loadFunction_address_irrel m p address
  · exact fun p address => loadFloat32_address_irrel m p address
  · exact fun p address => loadFloat64_address_irrel m p address
  · exact fun p q address => storePtr_address_irrel m p q address
  · exact fun p q address => storePtrInt_address_irrel m p q address
  · exact fun p id address => storeFunction_address_irrel m p id address
  · exact fun p f address => storeFloat32_address_irrel m p f address
  · exact fun p f address => storeFloat64_address_irrel m p f address
  · exact fun p args address => vaStart_address_irrel m p args address
  · exact fun dst src addressDst addressSrc =>
      vaCopy_address_irrel m dst src addressDst addressSrc
  · exact fun p address => vaEnd_address_irrel m p address
  · exact fun p address => vaArg_address_irrel m p address

/-- For a valid allocated object and nonzero size, `reallocAt` returns a fresh
    pointer at exactly the caller-selected concrete placement. -/
theorem reallocAt_valid_address (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map (fun r => r.2.address) = .ok address := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq, allocAt,
    alloc, Ptr.toObjectBoundAt] <;> rfl

theorem reallocAt_valid_pointer_shape (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => (r.2.obj, r.2.address, r.2.off, r.2.bound)) =
      .ok (some m.objs.length, address, 0, some size) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, allocAt, alloc, Ptr.toObjectBoundAt, get?, Except.map]

theorem reallocAt_valid_objects (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map (fun r => r.1.objs) =
      .ok ((m.objs ++ [CObj.mk .allocated true
        (c.bytes.take size ++ List.replicate (size - (c.bytes.take size).length) CByte.indet)
        none]).modify o (fun c => { c with live := false })) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, get?, Except.map]

theorem reallocAt_valid_new_loadBytes (m : Mem) (p : Ptr) (size address n : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hn : n ≤ size)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.loadBytes r.2 n) =
      .ok (.ok (List.take n
        (c.bytes.take size ++ List.replicate (size - (c.bytes.take size).length) CByte.indet))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  have hn' : ¬ size < n := by omega
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  have hne : m.objs.length ≠ o := Nat.ne_of_gt ho
  have hobj : m.objs[o] = c := (List.getElem?_eq_some_iff.mp hc).choose_spec
  have hnew (fresh : CObj) :
      ((m.objs ++ [fresh]).modify o
        (fun c => { c with live := false }))[m.objs.length] = fresh := by
    rw [List.getElem_modify_ne (fun c => { c with live := false })
      (m.objs ++ [fresh]) hne.symm (by simp)]
    simp
  have hlen : min size c.bytes.length + (size - min size c.bytes.length) = size := by
    by_cases hs : size ≤ c.bytes.length
    · simp [Nat.min_eq_left hs]
    · have hslt : c.bytes.length < size := by omega
      have hs' : c.bytes.length ≤ size := Nat.le_of_lt hslt
      rw [Nat.min_eq_right hs']
      exact Nat.add_sub_of_le hs'
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadBytes, resolve, get?, Except.map, hn', ho, hne,
    hobj, hnew, hlen, List.getElem?_append_right, List.getElem?_modify]
  simp [CObj.size, List.length_append, List.length_take, hlen, hn']
  rfl

theorem reallocAt_valid_old_resolve (m : Mem) (p : Ptr) (size address n : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.resolve p n) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, resolve, get?, Except.map,
    List.getElem?_append_left ho]

theorem reallocAt_valid_old_loadBytes (m : Mem) (p : Ptr) (size address n : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.loadBytes p n) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_storeBytes (m : Mem) (p : Ptr) (size address : Nat)
    (bs : List CByte) (o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.storeBytes p bs) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, storeBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_loadInt (m : Mem) (p : Ptr) (size address : Nat)
    (t : IntTy) (o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.loadInt p t) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadInt, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_storeInt (m : Mem) (p : Ptr) (size address : Nat)
    (t : IntTy) (v : Int) (o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.storeInt p t v) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, storeInt, storeBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_loadPtr (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.loadPtr p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadPtr, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_storePtr (m : Mem) (p : Ptr) (size address : Nat)
    (q : Ptr) (o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.storePtr p q) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, storePtr, storeBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_loadFloat32 (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.loadFloat32 p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadFloat32, loadBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_loadFloat64 (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.loadFloat64 p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadFloat64, loadBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_storeFloat32 (m : Mem) (p : Ptr) (size address : Nat)
    (f : Float32.Model) (o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.storeFloat32 p f) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, storeFloat32, storeBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_storeFloat64 (m : Mem) (p : Ptr) (size address : Nat)
    (f : Float.Model) (o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.storeFloat64 p f) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, storeFloat64, storeBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_loadPtrInt (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.loadPtrInt p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadPtrInt, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_storePtrInt (m : Mem) (p : Ptr) (size address : Nat)
    (q : Ptr) (o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.storePtrInt p q) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, storePtrInt, storeBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_loadFunction (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.loadFunction p) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadFunction, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_storeFunction (m : Mem) (p : Ptr) (size address : Nat)
    (id : DeclarationId) (o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.storeFunction p id) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, storeFunction, storeBytes, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_loadIntChecked (m : Mem) (alias : AliasModel)
    (p : Ptr) (size address : Nat) (t : IntTy) (used : CType)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.loadIntChecked alias p t used) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadIntChecked, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_old_storeIntChecked (m : Mem) (alias : AliasModel)
    (p : Ptr) (size address : Nat) (t : IntTy) (used : CType) (v : Int)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.storeIntChecked alias p t used v) =
      .ok (.error (.memUB (.deadObject o c.dur))) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  have ho : o < m.objs.length := (List.getElem?_eq_some_iff.mp hc).choose
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, storeIntChecked, resolve, get?, Except.map,
    List.getElem?_append_left ho]
  rfl

theorem reallocAt_valid_placement (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => (m.objs.length, address) ∈ r.1.placements) = .ok true := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq, kill,
    List.mem_append, Except.map]
  exact placementSet_mem _ _ _

theorem reallocAt_valid_placement_lookup (m : Mem) (p : Ptr) (size address : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address).map
        (fun r => r.1.placement? m.objs.length) = .ok (some address) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq, kill,
    placement?, placementSet, Except.map]
  rw [placementSet_find]
  simp

theorem reallocAt_valid_placement_irrel (m : Mem) (p : Ptr) (size address₁ address₂ : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address₁).map
        (fun r => (r.2.obj, r.2.off, r.2.bound)) =
      (reallocAt m p size address₂).map
        (fun r => (r.2.obj, r.2.off, r.2.bound)) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  simp only [Except.map, Except.ok.injEq]
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt]

theorem reallocAt_valid_resolve_placement_irrel
    (m : Mem) (p : Ptr) (size address₁ address₂ n : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address₁).map
        (fun r => r.1.resolve r.2 n) =
      (reallocAt m p size address₂).map
        (fun r => r.1.resolve r.2 n) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  simp only [Except.map, Except.ok.injEq]
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, resolve, get?, resolve_address_irrel]

theorem reallocAt_valid_loadBytes_placement_irrel
    (m : Mem) (p : Ptr) (size address₁ address₂ n : Nat)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address₁).map
        (fun r => r.1.loadBytes r.2 n) =
      (reallocAt m p size address₂).map
        (fun r => r.1.loadBytes r.2 n) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  simp only [Except.map, Except.ok.injEq]
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadBytes, resolve, get?, resolve_address_irrel]

theorem reallocAt_valid_storeBytes_placement_irrel
    (m : Mem) (p : Ptr) (size address₁ address₂ : Nat) (bs : List CByte)
    (o : ObjId) (c : CObj) (hsize : size ≠ 0) (hp : p.obj = some o)
    (hc : m.get? o = some c) (hdur : c.dur = .allocated)
    (hlive : c.live = true) (hoff : p.off = 0) :
    (reallocAt m p size address₁).map
        (fun r => (r.1.loadBytes r.2 bs.length, r.1.objs)) =
      (reallocAt m p size address₂).map
        (fun r => (r.1.loadBytes r.2 bs.length, r.1.objs)) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  change m.objs[o]? = some c at hc
  simp only [Except.map, Except.ok.injEq]
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq,
    kill, Ptr.toObjectBoundAt, loadBytes, resolve, get?, resolve_address_irrel]

theorem reallocAt_existing_placement (m : Mem) (p : Ptr) (size address : Nat)
    (q : ObjId) (o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true)
    (hoff : p.off = 0) (hq : q ≠ m.objs.length) :
    (reallocAt m p size address).map
        (fun r => r.1.placement? q) = .ok (m.placement? q) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  simp [reallocAt, hsize, hp, hc, hdur, hlive, hoff, hbeq, kill,
    placement?, Except.map]
  change ((placementSet m.placements m.objs.length address).find?
      (fun entry => entry.1 == q)).map Prod.snd =
    (m.placements.find? (fun entry => entry.1 == q)).map Prod.snd
  rw [placementSet_other _ _ _ _ hq]

theorem realloc_existing_placement (m : Mem) (p : Ptr) (size : Nat)
    (q o : ObjId) (c : CObj) (hsize : size ≠ 0)
    (hp : p.obj = some o) (hc : m.get? o = some c)
    (hdur : c.dur = .allocated) (hlive : c.live = true)
    (hoff : p.off = 0) (hq : q ≠ m.objs.length) :
    (realloc m p size).map
        (fun r => r.1.placement? q) = .ok (m.placement? q) := by
  have hbeq : (Duration.allocated == Duration.allocated) = true := by rfl
  simp [realloc, hsize, hp, hc, hdur, hlive, hoff, hbeq, kill,
    placement?, Except.map]
  have hq' : m.objs.length ≠ q := Ne.symm hq
  simp [List.find?_append, hq, hq']

@[simp] theorem reallocAt_zero (m : Mem) (p : Ptr) (address : Nat) :
    reallocAt m p 0 address = .error (.memUB (.reallocZero p)) := by
  simp [reallocAt]

@[simp] theorem reallocAt_null (m : Mem) (size address : Nat) (h : size ≠ 0) :
    reallocAt m Ptr.null size address = .ok (m.mallocAt size address) := by
  simp [reallocAt, Ptr.null, h, mallocAt]

/-! ## Well-formedness

Four properties the interpreter will lean on, each stated about the
operations above and each RUN on the shipped corpus in
`Examples/c/sunfish/memory.lean` — a lemma nobody instantiated is a lemma
nobody checked. -/

/-- `alloc` places the new object where its returned id says it is. -/
@[simp] theorem get?_alloc (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType) :
    (m.alloc dur size ty).1.get? (m.alloc dur size ty).2
      = some ⟨dur, true, List.replicate size .indet, ty⟩ := by
  simp [alloc, get?]

/-- C23 §6.2.4: a freshly created object is INSIDE its lifetime, so every
in-bounds access resolves. This is the base case every frame entry uses. -/
theorem resolve_alloc (m : Mem) (dur : Duration) (size n : Nat) (ty : Option CType)
    (h : n ≤ size) :
    (m.alloc dur size ty).1.resolve (Ptr.toObject (m.alloc dur size ty).2) n
      = .ok ((m.alloc dur size ty).2,
             ⟨dur, true, List.replicate size .indet, ty⟩, 0) := by
  have hn : ¬ size < n := by omega
  simp [resolve, Ptr.toObject, Ptr.toObjectAt, CObj.size, hn]

/-- Explicit placement changes only the concrete address.  Provenance,
    offset, and the one-past bound are independent of that open choice. -/
theorem allocAt_placement_irrel (m : Mem) (dur : Duration) (size : Nat)
    (ty : Option CType) (address₁ address₂ : Nat) :
    let p₁ := (m.allocAt dur size ty address₁).2
    let p₂ := (m.allocAt dur size ty address₂).2
    p₁.obj = p₂.obj ∧ p₁.off = p₂.off ∧ p₁.bound = p₂.bound := by
  simp [allocAt, alloc, Ptr.toObjectBoundAt]

@[simp] theorem allocAt_pointer_shape (m : Mem) (dur : Duration) (size : Nat)
    (ty : Option CType) (address : Nat) :
    (m.allocAt dur size ty address).2 =
      ⟨some (m.objs.length), address, 0, some size⟩ := by
  simp [allocAt, alloc, Ptr.toObjectBoundAt]

/-- The resolver observes provenance, offset, lifetime, and bounds, but not
    the concrete placement chosen for a fresh allocation. -/
@[simp] theorem allocAt_resolve_placement_irrel (m : Mem) (dur : Duration)
    (size : Nat) (ty : Option CType) (address₁ address₂ n : Nat) :
    (m.allocAt dur size ty address₁).1.resolve
        (m.allocAt dur size ty address₁).2 n =
      (m.allocAt dur size ty address₂).1.resolve
        (m.allocAt dur size ty address₂).2 n := by
  change (m.alloc dur size ty).1.resolve
      (Ptr.toObjectBoundAt (m.alloc dur size ty).2 address₁ size) n =
    (m.alloc dur size ty).1.resolve
      (Ptr.toObjectBoundAt (m.alloc dur size ty).2 address₂ size) n
  exact resolve_address_irrel (m.alloc dur size ty).1
    (Ptr.toObjectBoundAt (m.alloc dur size ty).2 address₂ size) n address₁

theorem allocAt_loadBytes_placement_irrel (m : Mem) (dur : Duration)
    (size : Nat) (ty : Option CType) (address₁ address₂ n : Nat) :
    (m.allocAt dur size ty address₁).1.loadBytes
        (m.allocAt dur size ty address₁).2 n =
      (m.allocAt dur size ty address₂).1.loadBytes
        (m.allocAt dur size ty address₂).2 n := by
  simp [allocAt, alloc, Ptr.toObjectBoundAt, loadBytes,
    resolve, get?, resolve_address_irrel]

theorem allocAt_storeBytes_objs_irrel (m : Mem) (dur : Duration)
    (size : Nat) (ty : Option CType) (address₁ address₂ : Nat)
    (bs : List CByte) :
    ((m.allocAt dur size ty address₁).1.storeBytes
      (m.allocAt dur size ty address₁).2 bs).map (fun m' => m'.objs) =
      ((m.allocAt dur size ty address₂).1.storeBytes
        (m.allocAt dur size ty address₂).2 bs).map (fun m' => m'.objs) := by
  by_cases hbs : size < bs.length
  · simp [allocAt, alloc, Ptr.toObjectBoundAt, storeBytes,
      resolve, get?, CObj.size, resolve_address_irrel, Except.map, hbs] <;> rfl
  · simp [allocAt, alloc, Ptr.toObjectBoundAt, storeBytes,
      resolve, get?, CObj.size, resolve_address_irrel, Except.map, hbs] <;> rfl

@[simp] theorem allocZeroedAt_resolve_placement_irrel (m : Mem) (dur : Duration)
    (size : Nat) (ty : Option CType) (address₁ address₂ n : Nat) :
    (m.allocZeroedAt dur size ty address₁).1.resolve
        (m.allocZeroedAt dur size ty address₁).2 n =
      (m.allocZeroedAt dur size ty address₂).1.resolve
        (m.allocZeroedAt dur size ty address₂).2 n := by
  change (m.allocZeroed dur size ty).1.resolve
      (Ptr.toObjectBoundAt (m.allocZeroed dur size ty).2 address₁ size) n =
    (m.allocZeroed dur size ty).1.resolve
      (Ptr.toObjectBoundAt (m.allocZeroed dur size ty).2 address₂ size) n
  exact resolve_address_irrel (m.allocZeroed dur size ty).1
    (Ptr.toObjectBoundAt (m.allocZeroed dur size ty).2 address₂ size) n address₁

theorem allocZeroedAt_loadBytes_placement_irrel (m : Mem) (dur : Duration)
    (size : Nat) (ty : Option CType) (address₁ address₂ n : Nat) :
    (m.allocZeroedAt dur size ty address₁).1.loadBytes
        (m.allocZeroedAt dur size ty address₁).2 n =
      (m.allocZeroedAt dur size ty address₂).1.loadBytes
        (m.allocZeroedAt dur size ty address₂).2 n := by
  simp [allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt, loadBytes,
    resolve, get?, resolve_address_irrel]

theorem allocZeroedAt_storeBytes_objs_irrel (m : Mem) (dur : Duration)
    (size : Nat) (ty : Option CType) (address₁ address₂ : Nat)
    (bs : List CByte) :
    ((m.allocZeroedAt dur size ty address₁).1.storeBytes
      (m.allocZeroedAt dur size ty address₁).2 bs).map (fun m' => m'.objs) =
      ((m.allocZeroedAt dur size ty address₂).1.storeBytes
        (m.allocZeroedAt dur size ty address₂).2 bs).map (fun m' => m'.objs) := by
  by_cases hbs : size < bs.length
  · simp [allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt, storeBytes,
      resolve, get?, CObj.size, resolve_address_irrel, Except.map, hbs] <;> rfl
  · simp [allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt, storeBytes,
      resolve, get?, CObj.size, resolve_address_irrel, Except.map, hbs] <;> rfl

@[simp] theorem mallocAt_resolve_placement_irrel (m : Mem) (size address₁ address₂ n : Nat) :
    (m.mallocAt size address₁).1.resolve (m.mallocAt size address₁).2 n =
      (m.mallocAt size address₂).1.resolve (m.mallocAt size address₂).2 n := by
  simpa [mallocAt] using
    (allocAt_resolve_placement_irrel m .allocated size none address₁ address₂ n)

@[simp] theorem callocAt_resolve_placement_irrel
    (m : Mem) (n size address₁ address₂ offset : Nat) :
    (m.callocAt n size address₁).1.resolve (m.callocAt n size address₁).2 offset =
      (m.callocAt n size address₂).1.resolve (m.callocAt n size address₂).2 offset := by
  simpa [callocAt] using
    (allocZeroedAt_resolve_placement_irrel m .allocated (n * size) none
      address₁ address₂ offset)

@[simp] theorem allocAt_ptr (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (address : Nat) :
    (m.allocAt dur size ty address).2.address = address := by
  simp [allocAt, Ptr.toObjectBoundAt]

@[simp] theorem allocAt_provenance (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (address : Nat) :
    (m.allocAt dur size ty address).2.obj = some (m.alloc dur size ty).2 := by
  simp [allocAt, Ptr.toObjectBoundAt]

theorem allocAt_placement (m : Mem) (dur : Duration) (size : Nat) (ty : Option CType)
    (address : Nat) :
    (m.allocAt dur size ty address).2.obj = some (m.alloc dur size ty).2 ∧
      ((m.alloc dur size ty).2, address) ∈ (m.allocAt dur size ty address).1.placements := by
  change (some m.objs.length = some m.objs.length) ∧
    (m.objs.length, address) ∈
      placementSet (m.placements ++ [(m.objs.length, m.objs.length)])
        m.objs.length address
  exact ⟨rfl, placementSet_mem _ _ _⟩

theorem allocAt_placement_lookup (m : Mem) (dur : Duration) (size : Nat)
    (ty : Option CType) (address : Nat) :
    (m.allocAt dur size ty address).1.placement?
        (m.alloc dur size ty).2 = some address := by
  change ((placementSet (m.placements ++ [(m.objs.length, m.objs.length)])
      m.objs.length address).find? (fun entry => entry.1 == m.objs.length)).map
        Prod.snd = some address
  rw [placementSet_find]
  rfl

theorem allocAt_existing_placement (m : Mem) (dur : Duration) (size : Nat)
    (ty : Option CType) (address : Nat) (q : ObjId)
    (hq : q ≠ m.objs.length) :
    (m.allocAt dur size ty address).1.placement? q = m.placement? q := by
  change ((placementSet (m.placements ++ [(m.objs.length, m.objs.length)])
      m.objs.length address).find? (fun entry => entry.1 == q)).map Prod.snd =
    (m.placements.find? (fun entry => entry.1 == q)).map Prod.snd
  rw [placementSet_other _ _ _ _ hq]
  have hq' : m.objs.length ≠ q := Ne.symm hq
  simp [List.find?_append, hq, hq']

theorem allocZeroedAt_placement (m : Mem) (dur : Duration) (size : Nat)
    (ty : Option CType) (address : Nat) :
    (m.allocZeroedAt dur size ty address).2.obj =
        some (m.allocZeroed dur size ty).2 ∧
      ((m.allocZeroed dur size ty).2, address) ∈
        (m.allocZeroedAt dur size ty address).1.placements := by
  change (some m.objs.length = some m.objs.length) ∧
    (m.objs.length, address) ∈
      placementSet (m.placements ++ [(m.objs.length, m.objs.length)])
        m.objs.length address
  exact ⟨rfl, placementSet_mem _ _ _⟩

theorem allocZeroedAt_placement_irrel (m : Mem) (dur : Duration) (size : Nat)
    (ty : Option CType) (address₁ address₂ : Nat) :
    let p₁ := (m.allocZeroedAt dur size ty address₁).2
    let p₂ := (m.allocZeroedAt dur size ty address₂).2
    p₁.obj = p₂.obj ∧ p₁.off = p₂.off ∧ p₁.bound = p₂.bound := by
  simp [allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt]

@[simp] theorem allocZeroedAt_pointer_shape (m : Mem) (dur : Duration) (size : Nat)
    (ty : Option CType) (address : Nat) :
    (m.allocZeroedAt dur size ty address).2 =
      ⟨some (m.objs.length), address, 0, some size⟩ := by
  simp [allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt]

theorem allocZeroedAt_placement_lookup (m : Mem) (dur : Duration) (size : Nat)
    (ty : Option CType) (address : Nat) :
    (m.allocZeroedAt dur size ty address).1.placement?
        (m.allocZeroed dur size ty).2 = some address := by
  change ((placementSet (m.placements ++ [(m.objs.length, m.objs.length)])
      m.objs.length address).find? (fun entry => entry.1 == m.objs.length)).map
        Prod.snd = some address
  rw [placementSet_find]
  rfl

theorem mallocAt_placement_lookup (m : Mem) (size address : Nat) :
    (m.mallocAt size address).1.placement?
        (m.alloc .allocated size none).2 = some address := by
  simpa [mallocAt] using
    (allocAt_placement_lookup m .allocated size none address)

theorem callocAt_placement_lookup (m : Mem) (n size address : Nat) :
    (m.callocAt n size address).1.placement?
        (m.allocZeroed .allocated (n * size) none).2 = some address := by
  simpa [callocAt] using
    (allocZeroedAt_placement_lookup m .allocated (n * size) none address)

theorem mallocAt_loadBytes_placement_irrel
    (m : Mem) (size address₁ address₂ n : Nat) :
    (m.mallocAt size address₁).1.loadBytes (m.mallocAt size address₁).2 n =
      (m.mallocAt size address₂).1.loadBytes (m.mallocAt size address₂).2 n := by
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt, loadBytes,
    resolve, get?, resolve_address_irrel]

theorem callocAt_loadBytes_placement_irrel
    (m : Mem) (n size address₁ address₂ offset : Nat) :
    (m.callocAt n size address₁).1.loadBytes
        (m.callocAt n size address₁).2 offset =
      (m.callocAt n size address₂).1.loadBytes
        (m.callocAt n size address₂).2 offset := by
  simp [callocAt, allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt,
    loadBytes, resolve, get?, resolve_address_irrel]

theorem mallocAt_storeBytes_objs_irrel
    (m : Mem) (size address₁ address₂ : Nat) (bs : List CByte) :
    ((m.mallocAt size address₁).1.storeBytes (m.mallocAt size address₁).2 bs).map
        (fun m' => m'.objs) =
      ((m.mallocAt size address₂).1.storeBytes (m.mallocAt size address₂).2 bs).map
        (fun m' => m'.objs) := by
  by_cases hbs : size < bs.length
  · simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt, storeBytes,
      resolve, get?, CObj.size, resolve_address_irrel, Except.map, hbs] <;> rfl
  · simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt, storeBytes,
      resolve, get?, CObj.size, resolve_address_irrel, Except.map, hbs] <;> rfl

theorem callocAt_storeBytes_objs_irrel
    (m : Mem) (n size address₁ address₂ : Nat) (bs : List CByte) :
    ((m.callocAt n size address₁).1.storeBytes
      (m.callocAt n size address₁).2 bs).map (fun m' => m'.objs) =
      ((m.callocAt n size address₂).1.storeBytes
        (m.callocAt n size address₂).2 bs).map (fun m' => m'.objs) := by
  by_cases hbs : (n : Int) * size < bs.length
  · simp [callocAt, allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt,
      storeBytes, resolve, get?, CObj.size, resolve_address_irrel,
      Except.map, hbs] <;> rfl
  · simp [callocAt, allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt,
      storeBytes, resolve, get?, CObj.size, resolve_address_irrel,
      Except.map, hbs] <;> rfl

theorem reallocAt_null_placement_lookup (m : Mem) (size address : Nat) (h : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.placement? m.objs.length) = .ok (some address) := by
  rw [reallocAt_null m size address h]
  simp only [Except.map, Except.ok.injEq]
  simpa [mallocAt, alloc] using
    (allocAt_placement_lookup m .allocated size none address)

@[simp] theorem reallocAt_null_address (m : Mem) (size address : Nat) (h : size ≠ 0) :
    (reallocAt m Ptr.null size address).map (fun r => r.2.address) = .ok address := by
  rw [reallocAt_null m size address h]
  simp only [Except.map, Except.ok.injEq]
  simp [mallocAt, allocAt, Ptr.toObjectBoundAt]

@[simp] theorem reallocAt_null_provenance (m : Mem) (size address : Nat) (h : size ≠ 0) :
    (reallocAt m Ptr.null size address).map (fun r => r.2.obj) =
      .ok (some m.objs.length) := by
  rw [reallocAt_null m size address h]
  simp only [Except.map, Except.ok.injEq]
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt]

@[simp] theorem reallocAt_null_offset_bound (m : Mem) (size address : Nat) (h : size ≠ 0) :
    (reallocAt m Ptr.null size address).map (fun r => (r.2.off, r.2.bound)) =
      .ok (0, some size) := by
  rw [reallocAt_null m size address h]
  simp only [Except.map, Except.ok.injEq]
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt]

theorem reallocAt_null_pointer_shape (m : Mem) (size address : Nat) (h : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => (r.2.obj, r.2.address, r.2.off, r.2.bound)) =
      .ok (some m.objs.length, address, 0, some size) := by
  rw [reallocAt_null m size address h]
  simp only [Except.map, Except.ok.injEq]
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt]

theorem reallocAt_null_objects (m : Mem) (size address : Nat) (h : size ≠ 0) :
    (reallocAt m Ptr.null size address).map (fun r => r.1.objs) =
      .ok (m.mallocAt size address).1.objs := by
  rw [reallocAt_null m size address h]
  rfl

theorem reallocAt_null_loadBytes (m : Mem) (size address n : Nat)
    (hsize : size ≠ 0) (hn : n ≤ size) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.loadBytes r.2 n) =
      .ok (.ok (List.replicate n CByte.indet)) := by
  rw [reallocAt_null m size address hsize]
  have hn' : ¬ size < n := by omega
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt,
    loadBytes, resolve, get?, Except.map, hn']
  simp [CObj.size, hn']
  change (.ok (List.take n (List.drop 0 (List.replicate size CByte.indet))) : MRes (List CByte)) =
    .ok (List.replicate n CByte.indet)
  simp [hn]

theorem reallocAt_null_loadIntChecked_full (m : Mem) (alias : AliasModel)
    (size address : Nat) (t : IntTy) (used : CType)
    (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.loadIntChecked alias r.2 t used) =
      .ok ((m.mallocAt size address).1.loadIntChecked alias
        (m.mallocAt size address).2 t used) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeBytes (m : Mem) (size address : Nat)
    (bs : List CByte) (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => (r.1.storeBytes r.2 bs).map (fun m' => m'.objs)) =
      .ok (((m.mallocAt size address).1.storeBytes
        (m.mallocAt size address).2 bs).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeBytes_full (m : Mem) (size address : Nat)
    (bs : List CByte) (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.storeBytes r.2 bs) =
      .ok ((m.mallocAt size address).1.storeBytes
        (m.mallocAt size address).2 bs) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeIntChecked (m : Mem) (alias : AliasModel)
    (size address : Nat) (t : IntTy) (used : CType) (v : Int)
    (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => (r.1.storeIntChecked alias r.2 t used v).map
          (fun m' => m'.objs)) =
      .ok (((m.mallocAt size address).1.storeIntChecked alias
        (m.mallocAt size address).2 t used v).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeIntChecked_full (m : Mem) (alias : AliasModel)
    (size address : Nat) (t : IntTy) (used : CType) (v : Int)
    (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.storeIntChecked alias r.2 t used v) =
      .ok ((m.mallocAt size address).1.storeIntChecked alias
        (m.mallocAt size address).2 t used v) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storePtr (m : Mem) (size address : Nat) (q : Ptr)
    (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => (r.1.storePtr r.2 q).map (fun m' => m'.objs)) =
      .ok (((m.mallocAt size address).1.storePtr
        (m.mallocAt size address).2 q).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storePtr_full (m : Mem) (size address : Nat) (q : Ptr)
    (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.storePtr r.2 q) =
      .ok ((m.mallocAt size address).1.storePtr
        (m.mallocAt size address).2 q) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storePtrInt (m : Mem) (size address : Nat) (q : Ptr)
    (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => (r.1.storePtrInt r.2 q).map (fun m' => m'.objs)) =
      .ok (((m.mallocAt size address).1.storePtrInt
        (m.mallocAt size address).2 q).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storePtrInt_full (m : Mem) (size address : Nat) (q : Ptr)
    (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.storePtrInt r.2 q) =
      .ok ((m.mallocAt size address).1.storePtrInt
        (m.mallocAt size address).2 q) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeFunction (m : Mem) (size address : Nat)
    (id : DeclarationId) (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => (r.1.storeFunction r.2 id).map (fun m' => m'.objs)) =
      .ok (((m.mallocAt size address).1.storeFunction
        (m.mallocAt size address).2 id).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeFloat32 (m : Mem) (size address : Nat)
    (f : Float32.Model) (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => (r.1.storeFloat32 r.2 f).map (fun m' => m'.objs)) =
      .ok (((m.mallocAt size address).1.storeFloat32
        (m.mallocAt size address).2 f).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeFloat32_full (m : Mem) (size address : Nat)
    (f : Float32.Model) (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.storeFloat32 r.2 f) =
      .ok ((m.mallocAt size address).1.storeFloat32
        (m.mallocAt size address).2 f) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeFloat64 (m : Mem) (size address : Nat)
    (f : Float.Model) (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => (r.1.storeFloat64 r.2 f).map (fun m' => m'.objs)) =
      .ok (((m.mallocAt size address).1.storeFloat64
        (m.mallocAt size address).2 f).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeFunction_full (m : Mem) (size address : Nat)
    (id : DeclarationId) (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.storeFunction r.2 id) =
      .ok ((m.mallocAt size address).1.storeFunction
        (m.mallocAt size address).2 id) := by
  rw [reallocAt_null m size address hsize]
  rfl

theorem reallocAt_null_storeFloat64_full (m : Mem) (size address : Nat)
    (f : Float.Model) (hsize : size ≠ 0) :
    (reallocAt m Ptr.null size address).map
        (fun r => r.1.storeFloat64 r.2 f) =
      .ok ((m.mallocAt size address).1.storeFloat64
        (m.mallocAt size address).2 f) := by
  rw [reallocAt_null m size address hsize]
  rfl

@[simp] theorem mallocAt_pointer_shape (m : Mem) (size address : Nat) :
    (m.mallocAt size address).2 =
      ⟨some (m.objs.length), address, 0, some size⟩ := by
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt]

@[simp] theorem callocAt_pointer_shape (m : Mem) (n size address : Nat) :
    (m.callocAt n size address).2 =
      ⟨some (m.objs.length), address, 0, some (n * size)⟩ := by
  simp [callocAt, allocZeroedAt, allocZeroed, Ptr.toObjectBoundAt]

@[simp] theorem reallocAt_null_placement_irrel (m : Mem) (size address₁ address₂ : Nat)
    (h : size ≠ 0) :
    (reallocAt m Ptr.null size address₁).map
        (fun r => (r.2.obj, r.2.off, r.2.bound)) =
      (reallocAt m Ptr.null size address₂).map
        (fun r => (r.2.obj, r.2.off, r.2.bound)) := by
  rw [reallocAt_null m size address₁ h, reallocAt_null m size address₂ h]
  simp only [Except.map, Except.ok.injEq]
  have hs := mallocAt_placement_irrel m size address₁ address₂
  rcases hs with ⟨ho, hoff, hbound⟩
  simp [ho, hoff, hbound]

@[simp] theorem reallocAt_null_resolve_placement_irrel
    (m : Mem) (size address₁ address₂ n : Nat) (h : size ≠ 0) :
    (reallocAt m Ptr.null size address₁).map
        (fun r => r.1.resolve r.2 n) =
      (reallocAt m Ptr.null size address₂).map
        (fun r => r.1.resolve r.2 n) := by
  rw [reallocAt_null m size address₁ h, reallocAt_null m size address₂ h]
  simp only [Except.map, Except.ok.injEq]
  exact mallocAt_resolve_placement_irrel m size address₁ address₂ n

theorem reallocAt_null_loadBytes_placement_irrel
    (m : Mem) (size address₁ address₂ n : Nat) (h : size ≠ 0) :
    (reallocAt m Ptr.null size address₁).map
        (fun r => r.1.loadBytes r.2 n) =
      (reallocAt m Ptr.null size address₂).map
        (fun r => r.1.loadBytes r.2 n) := by
  rw [reallocAt_null m size address₁ h, reallocAt_null m size address₂ h]
  simp only [Except.map, Except.ok.injEq]
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt, loadBytes,
    resolve, get?, resolve_address_irrel]

theorem reallocAt_null_storeBytes_placement_irrel
    (m : Mem) (size address₁ address₂ : Nat) (bs : List CByte)
    (h : size ≠ 0) :
    (reallocAt m Ptr.null size address₁).map
        (fun r => (r.1.loadBytes r.2 bs.length, r.1.objs)) =
      (reallocAt m Ptr.null size address₂).map
        (fun r => (r.1.loadBytes r.2 bs.length, r.1.objs)) := by
  rw [reallocAt_null m size address₁ h, reallocAt_null m size address₂ h]
  simp only [Except.map, Except.ok.injEq]
  simp [mallocAt, allocAt, alloc, Ptr.toObjectBoundAt, loadBytes,
    resolve, get?, resolve_address_irrel]

theorem reallocAt_null_storePtr_objs_irrel
    (m : Mem) (size address₁ address₂ : Nat) (q : Ptr)
    (h : size ≠ 0) :
    (reallocAt m Ptr.null size address₁).map
        (fun r => (r.1.storePtr r.2 q).map (fun m' => m'.objs)) =
      (reallocAt m Ptr.null size address₂).map
        (fun r => (r.1.storePtr r.2 q).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address₁ h, reallocAt_null m size address₂ h]
  simp only [Except.map]
  congr 1
  simpa only [storePtr, Except.map] using
    (mallocAt_storeBytes_objs_irrel m size address₁ address₂
      ((List.range 8).map (CByte.ptrByte q)))

theorem reallocAt_null_storePtrInt_objs_irrel
    (m : Mem) (size address₁ address₂ : Nat) (q : Ptr)
    (h : size ≠ 0) :
    (reallocAt m Ptr.null size address₁).map
        (fun r => (r.1.storePtrInt r.2 q).map (fun m' => m'.objs)) =
      (reallocAt m Ptr.null size address₂).map
        (fun r => (r.1.storePtrInt r.2 q).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address₁ h, reallocAt_null m size address₂ h]
  simp only [Except.map]
  congr 1
  simpa only [storePtrInt, Except.map] using
    (mallocAt_storeBytes_objs_irrel m size address₁ address₂
      ((List.range 8).map (CByte.ptrIntByte q)))

theorem reallocAt_null_storeFunction_objs_irrel
    (m : Mem) (size address₁ address₂ : Nat) (id : DeclarationId)
    (h : size ≠ 0) :
    (reallocAt m Ptr.null size address₁).map
        (fun r => (r.1.storeFunction r.2 id).map (fun m' => m'.objs)) =
      (reallocAt m Ptr.null size address₂).map
        (fun r => (r.1.storeFunction r.2 id).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address₁ h, reallocAt_null m size address₂ h]
  simp only [Except.map]
  congr 1
  simpa only [storeFunction, Except.map] using
    (mallocAt_storeBytes_objs_irrel m size address₁ address₂
      (List.replicate 8 (CByte.funByte id)))

theorem reallocAt_null_storeBytes_objs_irrel
    (m : Mem) (size address₁ address₂ : Nat) (bs : List CByte)
    (h : size ≠ 0) :
    (reallocAt m Ptr.null size address₁).map
        (fun r => (r.1.storeBytes r.2 bs).map (fun m' => m'.objs)) =
      (reallocAt m Ptr.null size address₂).map
        (fun r => (r.1.storeBytes r.2 bs).map (fun m' => m'.objs)) := by
  rw [reallocAt_null m size address₁ h, reallocAt_null m size address₂ h]
  simp only [Except.map, Except.ok.injEq]
  exact mallocAt_storeBytes_objs_irrel m size address₁ address₂ bs

theorem allocZeroedAt_existing_placement (m : Mem) (dur : Duration) (size : Nat)
    (ty : Option CType) (address : Nat) (q : ObjId)
    (hq : q ≠ m.objs.length) :
    (m.allocZeroedAt dur size ty address).1.placement? q = m.placement? q := by
  change ((placementSet (m.placements ++ [(m.objs.length, m.objs.length)])
      m.objs.length address).find? (fun entry => entry.1 == q)).map Prod.snd =
    (m.placements.find? (fun entry => entry.1 == q)).map Prod.snd
  rw [placementSet_other _ _ _ _ hq]
  have hq' : m.objs.length ≠ q := Ne.symm hq
  simp [List.find?_append, hq, hq']

theorem mallocAt_existing_placement (m : Mem) (size address : Nat) (q : ObjId)
    (hq : q ≠ m.objs.length) :
    (m.mallocAt size address).1.placement? q = m.placement? q := by
  simpa [mallocAt] using
    (allocAt_existing_placement m .allocated size none address q hq)

theorem callocAt_existing_placement (m : Mem) (n size address : Nat) (q : ObjId)
    (hq : q ≠ m.objs.length) :
    (m.callocAt n size address).1.placement? q = m.placement? q := by
  simpa [callocAt] using
    (allocZeroedAt_existing_placement m .allocated (n * size) none address q hq)

/-- INVERSION for `resolve`: everything a successful access establishes.

Stated once because `resolve` is the single place C's three structural
undefined behaviors are decided (§6.5.4.2p4, §6.2.4p2, §6.5.7p9), so
every later lemma wants exactly these facts and none should re-derive
them. -/
theorem resolve_ok {m : Mem} {p : Ptr} {n : Nat} {o : ObjId} {c : CObj} {off : Nat}
    (h : m.resolve p n = .ok (o, c, off)) :
    p.obj = some o ∧ m.get? o = some c ∧ c.live = true
      ∧ off = p.off.toNat ∧ 0 ≤ p.off ∧ off + n ≤ c.bytes.length
      ∧ ((off + n : Nat) : Int) ≤ p.bound.getD (c.bytes.length : Int) := by
  unfold resolve at h
  cases hobj : p.obj with
  | none => rw [hobj] at h; simp only [] at h; exact absurd h (by simp)
  | some o' =>
    rw [hobj] at h
    simp only [] at h
    cases hget : m.get? o' with
    | none => rw [hget] at h; simp only [] at h; exact absurd h (by simp)
    | some c' =>
      rw [hget] at h
      simp only [] at h
      by_cases hlive : c'.live = true
      · rw [if_neg (by simp [hlive])] at h
        by_cases hneg : p.off < 0
        · rw [if_pos (by simp [hneg])] at h; exact absurd h (by simp)
        · rw [if_neg (by simp [hneg])] at h
          by_cases hsize : p.off + (n : Int) > (c'.size : Int)
          · rw [if_pos (by simp [hsize])] at h; exact absurd h (by simp)
          · rw [if_neg (by simp [hsize])] at h
            by_cases hbound : p.off + (n : Int) > p.bound.getD (c'.size : Int)
            · rw [if_pos (by simp [hbound])] at h; exact absurd h (by simp)
            · rw [if_neg (by simp [hbound])] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨h1, h2, h3⟩ := h
              subst h1; subst h2; subst h3
              have hlo : 0 ≤ p.off := by omega
              refine ⟨rfl, hget, hlive, rfl, hlo, ?_, ?_⟩
              · have he : (p.off.toNat : Int) = p.off := Int.toNat_of_nonneg hlo
                have hhi : p.off + (n : Int) ≤ (c'.size : Int) := by omega
                simp only [CObj.size] at hhi
                omega
              · have hbound' : p.off + (n : Int) ≤ p.bound.getD (c'.size : Int) := by
                  omega
                have he : (p.off.toNat : Int) = p.off := Int.toNat_of_nonneg hlo
                simp only [CObj.size] at hbound' ⊢
                omega
      · rw [if_pos (by simp [hlive])] at h; exact absurd h (by simp)

/-- Writing an object leaves it where it was. -/
@[simp] theorem get?_set_self (m : Mem) (o : ObjId) (c : CObj) (h : o < m.objs.length) :
    ({m with objs := m.objs.set o c}).get? o = some c := by
  simp [get?, h]

/-- C23 §6.2.4p2: once an object's lifetime ends, EVERY access through a
pointer to it refuses — `J.2(9)`/`J.2(10)`. The object is still in the
store, which is exactly what makes the refusal possible instead of a
reused slot silently answering. -/
theorem resolve_kill (m : Mem) (o : ObjId) (c : CObj) (p : Ptr) (n : Nat)
    (hp : p.obj = some o) (hc : m.get? o = some c) :
    (m.kill o).resolve p n = .error (.memUB (.deadObject o c.dur)) := by
  have hk : (m.kill o).get? o = some { c with live := false } := by
    simp only [kill, get?] at hc ⊢
    rw [List.getElem?_modify]
    simp [hc]
  simp [resolve, hp, hk]

@[simp] theorem resolve_kill_address_irrel (m : Mem) (o : ObjId) (c : CObj)
    (p : Ptr) (n address : Nat) (hp : p.obj = some o) (hc : m.get? o = some c) :
    (m.kill o).resolve {p with address := address} n =
      (m.kill o).resolve p n := by
  simp [resolve_address_irrel]

/-- **The round trip.** What `storeBytes` wrote, `loadBytes` reads back —
so the byte lattice is a memory and not a filter.

The store's success is a HYPOTHESIS, never a conclusion: a store that
refused has no out-memory to speak about, which is the same discipline
§4.3's drain amendment applies to worlds. -/
theorem loadBytes_storeBytes {m m' : Mem} {p : Ptr} {bs : List CByte}
    {o : ObjId} {c : CObj} {off : Nat}
    (hr : m.resolve p bs.length = .ok (o, c, off))
    (h : m.storeBytes p bs = .ok m') :
    m'.loadBytes p bs.length = .ok bs := by
  obtain ⟨hobj, hget, hlive, hoff, hlo, hhi, hbound⟩ := resolve_ok hr
  subst hoff
  simp only [storeBytes, hr, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at h
  subst h
  have hidx : o < m.objs.length := by
    simp only [get?] at hget
    match Nat.lt_or_ge o m.objs.length with
    | .inl hlt => exact hlt
    | .inr hge => rw [List.getElem?_eq_none hge] at hget; simp at hget
  have he : (p.off.toNat : Int) = p.off := Int.toNat_of_nonneg hlo
  have htk : (c.bytes.take p.off.toNat).length = p.off.toNat := by simp; omega
  have hsize : ¬ p.off + (bs.length : Int) > (c.bytes.length : Int) := by
    omega
  have hnewSize :
      min p.off.toNat c.bytes.length + bs.length +
        (c.bytes.length - (p.off.toNat + bs.length)) = c.bytes.length := by
    omega
  simp only [loadBytes, resolve, hobj, get?_set_self _ _ _ hidx, bind, Except.bind, pure, Except.pure]
  simp only [CObj.size, List.length_append, List.length_take, List.length_drop]
  rw [hnewSize]
  rw [if_neg (by simp [hlive]), if_neg (by omega), if_neg hsize, if_neg ?bnd]
  case bnd =>
    intro hc
    omega
  simp only [Except.ok.injEq]
  rw [List.append_assoc, List.drop_left' htk, List.take_left' rfl]

theorem loadBytes_rename_storeBytes_rename
    {m m' : Mem} {p : Ptr} {bs : List CByte}
    {o : ObjId} {c : CObj} {off : Nat}
    (rename : ObjId → Nat)
    (hr : m.resolve p bs.length = .ok (o, c, off))
    (h : m.storeBytes p bs = .ok m') :
    (m'.renameAddresses rename).loadBytes (Ptr.renameAddress rename p) bs.length =
      .ok (bs.map (CByte.renameAddress rename)) := by
  have hr' : (m.renameAddresses rename).resolve (Ptr.renameAddress rename p)
      (bs.map (CByte.renameAddress rename)).length =
      .ok (o, CObj.renameAddress rename c, off) := by
    rw [List.length_map, resolve_renameAddresses, hr]
    rfl
  have h' : (m.renameAddresses rename).storeBytes (Ptr.renameAddress rename p)
      (bs.map (CByte.renameAddress rename)) =
      .ok (m'.renameAddresses rename) := by
    rw [storeBytes_renameAddresses, h]
    rfl
  simpa [List.length_map] using loadBytes_storeBytes hr' h'

/-! ### Axiom audit

The standing requirement: every theorem prints its axioms, and no
`sorry` or `native_decide` appears anywhere in the tier. -/

#print axioms get?_alloc
#print axioms resolve_alloc
#print axioms resolve_ok
#print axioms get?_set_self
#print axioms resolve_kill
#print axioms loadBytes_storeBytes

end Mem

/-! ## §3.4 — `Halt`, the base outside `ρ`

Per `docs/family-architecture.md` §3.4: the outcomes that **no construct
in any modelled language may catch** live in the monad's BASE, not in
`ExceptT`'s error. Inside `ρ`, "no catch reaches a refusal" is a
per-language, per-construct PROOF OBLIGATION — and C cannot discharge it
cheaply: this corpus alone has `setjmp` 2, `longjmp` 2 and 5 `jmp_buf`
objects, plus signal handlers in the language at large. Uncatchability
belongs to the definition.

So `timeout` and `unsupported` are here, and the two catchable-in-
principle refusal causes (`ub`, `libc`) stay in `Refusal`. -/

/-! ## §3.4 — ADOPTED from `Core`: `Loud`, and the guard that came with it

The HOLD recorded here is RELEASED. `LeanModels/Core/Outcome.lean` now
carries a payload that SUBSUMES this lane's: `Loud.unsupported (cause :
RefusalCause π) (message) (snapshot : Option σ)`, with **both of this
lane's structural guards lifted into Core** — the `BEq` instance ignores
the snapshot, and `Loud.observable` has nowhere to put a `σ`. So adoption
is a substitution at `σ := Mem`, not a rewrite, and the guards are now
enforced for every tier instead of re-argued by each.

**Core's taxonomy is strictly richer, and the extra class is one this
lane already owes.** `RefusalCause` has four constructors where this
tier had three, and the fourth is `orderDependence` — exactly the verdict
Thomas's `∀ order` ruling needs for a program whose observable depends on
argument evaluation order (`docs/c23-spec-mirror.md` §5). The mapping:

| this tier's cause | `RefusalCause` | why |
| --- | --- | --- |
| `ub` | `.undefined` | "never retires: it is the product" |
| `unsupported` | `.unsupported` | retires by climbing a rung |
| `libc` | `.environment` | retires by widening the slice |
| *(owed)* | `.orderDependence` | the J.1(16) domain, 7 sites |

`π := Unit`: this tier's prose already carries the detail, so there is no
structured payload to add. If the order-dependence verdict later wants to
name its 7 sites, `π` is where that goes. -/

/-- The refusal detail this tier carries. `Unit` — the message is the
detail — until the order-dependence verdict needs to name a site. -/
abbrev CDetail := Unit

/-- This tier's three causes, in the family's vocabulary. -/
abbrev Cause := RefusalCause CDetail

namespace Refusal

/-- Which of the family's classes this refusal belongs to. **UB never
retires: it is the product.** -/
def cause : Refusal → Cause
  | .valueUB _ | .memUB _ => .undefined ()
  | .libc _ => .environment ()
  | .aborted => .environment ()

/-- The Annex J.2 index, where the refusal is UB and the annex has one. -/
def j2 : Refusal → Option String
  | .memUB f => f.j2
  | .valueUB u =>
      match u with
      | .signedOverflow .. => some "J.2(35)"
      | .divideByZero _ => some "J.2(41)"
      | .divideOverflow => some "J.2(35)"
      | .floatingToIntegralOutOfRange _ => some "J.2(16)"
      | .shiftCountTooLarge .. | .shiftCountNegative _ => some "J.2(48)"
      | .shiftNegativeOperand _ | .shiftOverflow .. => some "J.2(49)"
      | .vaArgTypeMismatch .. => none
  | .libc _ => none
  | .aborted => none

end Refusal

/-! ## The verdict a scoreboard sees

`docs/c23-goal.md` §3's four verdicts. Kept as this tier's own type
rather than folded into `Loud.observable`, because the scoreboard needs
the REFUSAL VALUE (to read its J.2 index), which a `String × String`
observable deliberately discards. It is still the third place the
snapshot guard holds: there is nowhere to put a `Mem` here either. -/

/-- What a run produced, with the causes kept apart. -/
inductive Outcome (α : Type) where
  | ok (value : α)
  /-- The program called `abort()` (§7.22.4.1): a terminal outcome, distinct
  from an exit status, undefined behavior, and an out-of-tier refusal. -/
  | aborted
  /-- A refusal that rode in `ExceptT`: cause `undefined` or `environment`. -/
  | refused (r : Refusal)
  /-- Cause `unsupported` — out of tier. The snapshot is deliberately NOT
  carried across this boundary. -/
  | unsupported (what : String)
  /-- Fuel exhaustion. Never conflated with a refusal. -/
  | timeout
deriving Repr, Inhabited, BEq

/-- The cause of an outcome, where it has one. -/
def Outcome.cause? : Outcome α → Option Cause
  | .ok _ => none
  | .aborted => none
  | .refused r => some r.cause
  | .unsupported _ => some (.unsupported ())
  | .timeout => none

end LeanModels.C.C23
