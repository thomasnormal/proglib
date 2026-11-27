import LeanModels.C.Ast

/-!
# F2 shared byte store

This is the first S2 slice. Storage is parameterised by the language's tag,
allocation metadata, effective-type state, hook choice, and fault type. The
operations expose byte footprints and return a refusal when a request is
outside the current store. C23/Memory remains the legacy evaluator store
until the language instance and its replay rows are complete.
-/

namespace LeanModels.C.F2

abbrev AllocId := Nat

structure Provenance (Tag : Type) where
  allocation : AllocId
  tag : Tag
deriving Repr, BEq, DecidableEq

inductive Byte (Tag : Type) where
  | uninitialized
  | value (bits : UInt8) (provenance : Option (Provenance Tag))
      (fragment : Option Nat)
deriving Repr, BEq

structure Pointer (Tag : Type) where
  provenance : Option (Provenance Tag)
  address : Nat
deriving Repr, BEq

def pointerByte (address fragment : Nat) : UInt8 :=
  UInt8.ofNat ((address / (256 ^ fragment)) % 256)

theorem pointerByte_contract (address fragment : Nat) :
    pointerByte address fragment =
        UInt8.ofNat ((address / (256 ^ fragment)) % 256) ∧
      (pointerByte address fragment).toNat =
        (address / (256 ^ fragment)) % 256 := by
  simp [pointerByte]

theorem pointerByte_zero_fragment (address : Nat) :
    pointerByte address 0 = UInt8.ofNat (address % 256) := by
  simp [pointerByte]

theorem pointerByte_zero_address (fragment : Nat) :
    pointerByte 0 fragment = 0 := by
  simp [pointerByte]

theorem pointerByte_lt_256 (address fragment : Nat) :
    (pointerByte address fragment).toNat < 256 := by
  have h := UInt8.toNat_lt (pointerByte address fragment)
  omega

def renamePointer (resolve : AllocId → Nat) (pointer : Pointer Tag) : Pointer Tag :=
  { pointer with
    address := match pointer.provenance with
      | none => pointer.address
      | some provenance => resolve provenance.allocation }

def renameByte (resolve : AllocId → Nat) : Byte Tag → Byte Tag
  | .uninitialized => .uninitialized
  | .value bits provenance fragment =>
      match provenance, fragment with
      | some provenance, some fragment =>
          .value (pointerByte (resolve provenance.allocation) fragment)
            (some provenance) (some fragment)
      | _, _ => .value bits provenance fragment

def byteFragment : Byte Tag → Option Nat
  | .uninitialized => none
  | .value _ _ fragment => fragment

def byteProvenance : Byte Tag → Option (Provenance Tag)
  | .uninitialized => none
  | .value _ provenance _ => provenance

theorem renamePointer_provenance (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    (renamePointer resolve pointer).provenance = pointer.provenance := by
  rfl

theorem renamePointer_address (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    (renamePointer resolve pointer).address =
      match pointer.provenance with
      | none => pointer.address
      | some provenance => resolve provenance.allocation := by
  rfl

theorem renamePointer_contract (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    (renamePointer resolve pointer).provenance = pointer.provenance ∧
      (renamePointer resolve pointer).address =
        match pointer.provenance with
        | none => pointer.address
        | some provenance => resolve provenance.allocation := by
  exact ⟨renamePointer_provenance resolve pointer,
    renamePointer_address resolve pointer⟩

theorem renamePointer_idempotent (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    renamePointer resolve (renamePointer resolve pointer) = renamePointer resolve pointer := by
  cases pointer with
  | mk provenance address => cases provenance <;> rfl

theorem renamePointer_comp (first second : AllocId → Nat) (pointer : Pointer Tag) :
    renamePointer second (renamePointer first pointer) = renamePointer second pointer := by
  cases pointer with
  | mk provenance address => cases provenance <;> rfl

theorem renamePointer_renaming_contract
    (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    (renamePointer resolve pointer).provenance = pointer.provenance ∧
      ((renamePointer resolve pointer).address =
        match pointer.provenance with
        | none => pointer.address
        | some provenance => resolve provenance.allocation) ∧
      renamePointer resolve (renamePointer resolve pointer) =
        renamePointer resolve pointer := by
  constructor
  · exact renamePointer_provenance resolve pointer
  constructor
  · exact renamePointer_address resolve pointer
  · exact renamePointer_idempotent resolve pointer

theorem renameByte_preserves_fragment (resolve : AllocId → Nat) (byte : Byte Tag) :
    byteFragment (renameByte resolve byte) = byteFragment byte := by
  cases byte with
  | uninitialized => rfl
  | value bits provenance fragment => cases provenance <;> cases fragment <;> rfl

theorem renameByte_preserves_provenance (resolve : AllocId → Nat) (byte : Byte Tag) :
    byteProvenance (renameByte resolve byte) = byteProvenance byte := by
  cases byte with
  | uninitialized => rfl
  | value bits provenance fragment => cases provenance <;> cases fragment <;> rfl

theorem renameByte_pointer_fragment
    (resolve : AllocId → Nat) (bits : UInt8)
    (provenance : Provenance Tag) (fragment : Nat) :
    renameByte resolve (.value bits (some provenance) (some fragment)) =
      .value (pointerByte (resolve provenance.allocation) fragment)
        (some provenance) (some fragment) := by
  rfl

theorem renameByte_contract (resolve : AllocId → Nat) (byte : Byte Tag) :
    byteFragment (renameByte resolve byte) = byteFragment byte ∧
      byteProvenance (renameByte resolve byte) = byteProvenance byte ∧
      (∀ (bits : UInt8) (provenance : Provenance Tag) (fragment : Nat),
        renameByte resolve (.value bits (some provenance) (some fragment)) =
          .value (pointerByte (resolve provenance.allocation) fragment)
            (some provenance) (some fragment)) := by
  exact ⟨renameByte_preserves_fragment resolve byte,
    renameByte_preserves_provenance resolve byte,
    fun bits provenance fragment => renameByte_pointer_fragment resolve bits provenance fragment⟩

inductive Value (Tag : Type) where
  | scalar (bytes : List UInt8)
  | pointer (pointer : Pointer Tag)
  | aggregate (members : List (Value Tag))
deriving Repr

def encodePointer (pointer : Pointer Tag) : List (Byte Tag) :=
  (List.range 8).map (fun fragment =>
    .value (pointerByte pointer.address fragment)
      pointer.provenance (some fragment))

theorem encodePointer_contract (pointer : Pointer Tag) :
    (encodePointer pointer).length = 8 ∧
      (encodePointer pointer).map byteFragment =
        (List.range 8).map some ∧
      (encodePointer pointer).map byteProvenance =
        (List.range 8).map (fun _ => pointer.provenance) := by
  simp [encodePointer, byteFragment, byteProvenance]

theorem encodePointer_first_fragment (pointer : Pointer Tag) :
    (encodePointer pointer).head? =
      some (.value (pointerByte pointer.address 0) pointer.provenance (some 0)) := by
  have hrange : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  simp [encodePointer, hrange]

def encodeValue : Value Tag → List (Byte Tag)
  | .scalar bytes => bytes.map (fun byte => .value byte none none)
  | .pointer pointer => encodePointer pointer
  | .aggregate members => members.flatMap encodeValue

def renameValue (resolve : AllocId → Nat) : Value Tag → Value Tag
  | .scalar bytes => .scalar bytes
  | .pointer pointer => .pointer (renamePointer resolve pointer)
  | .aggregate members => .aggregate (members.map (renameValue resolve))

theorem renameValue_idempotent (resolve : AllocId → Nat) (value : Value Tag) :
    renameValue resolve (renameValue resolve value) = renameValue resolve value := by
  refine Value.rec
    (motive_1 := fun value =>
      renameValue resolve (renameValue resolve value) = renameValue resolve value)
    (motive_2 := fun members =>
      (members.map (renameValue resolve)).map (renameValue resolve) =
        members.map (renameValue resolve))
    (scalar := ?_) (pointer := ?_) (aggregate := ?_) (nil := ?_) (cons := ?_) value
  · intro bytes
    simp [renameValue]
  · intro pointer
    simp [renameValue, renamePointer_idempotent]
  · intro members ih
    simp [renameValue, ih]
  · simp
  · intro head tail headIh tailIh
    simp only [List.map_cons]
    rw [headIh, tailIh]

theorem renameValue_comp
    (first second : AllocId → Nat) (value : Value Tag) :
    renameValue second (renameValue first value) = renameValue second value := by
  refine Value.rec
    (motive_1 := fun value =>
      renameValue second (renameValue first value) = renameValue second value)
    (motive_2 := fun members =>
      (members.map (renameValue first)).map (renameValue second) =
        members.map (renameValue second))
    (scalar := ?_) (pointer := ?_) (aggregate := ?_) (nil := ?_) (cons := ?_) value
  · intro bytes
    simp [renameValue]
  · intro pointer
    simp [renameValue, renamePointer_comp]
  · intro members ih
    simp [renameValue, ih]
  · simp
  · intro head tail headIh tailIh
    simp only [List.map_cons]
    rw [headIh, tailIh]

theorem encodeValue_rename (resolve : AllocId → Nat) (value : Value Tag) :
    encodeValue (renameValue resolve value) =
      (encodeValue value).map (renameByte resolve) := by
  refine Value.rec
    (motive_1 := fun value =>
      encodeValue (renameValue resolve value) =
        (encodeValue value).map (renameByte resolve))
    (motive_2 := fun members =>
      (members.map (renameValue resolve)).flatMap encodeValue =
        (members.flatMap encodeValue).map (renameByte resolve))
    (scalar := ?_) (pointer := ?_) (aggregate := ?_) (nil := ?_) (cons := ?_) value
  · intro bytes
    simp [encodeValue, renameValue, renameByte]
  · intro pointer
    cases pointer with
    | mk provenance address =>
        cases provenance <;>
          simp [encodeValue, renameValue, encodePointer, renamePointer,
            renameByte, pointerByte]
  · intro members ih
    simp [encodeValue, renameValue, ih]
  · simp
  · intro head tail headIh tailIh
    simp only [List.map_cons, List.flatMap_cons, List.map_append]
    rw [headIh, tailIh]

theorem encodeValue_rename_contract
    (resolve : AllocId → Nat) (value : Value Tag) :
    encodeValue (renameValue resolve value) =
        (encodeValue value).map (renameByte resolve) ∧
      (encodeValue (renameValue resolve value)).length =
        (encodeValue value).length := by
  exact ⟨encodeValue_rename resolve value,
    by simp [encodeValue_rename resolve value]⟩

theorem encodeValue_contract (value : Value Tag) :
    match value with
    | .scalar bytes =>
        encodeValue value = bytes.map (fun byte => .value byte none none)
    | .pointer pointer =>
        encodeValue value = encodePointer pointer ∧
          (encodeValue value).length = 8
    | .aggregate members =>
        encodeValue value = members.flatMap encodeValue := by
  cases value with
  | scalar bytes => simp [encodeValue]
  | pointer pointer => simp [encodeValue, encodePointer]
  | aggregate members => simp [encodeValue]

theorem renameValue_contract (resolve : AllocId → Nat) (value : Value Tag) :
    encodeValue (renameValue resolve value) =
        (encodeValue value).map (renameByte resolve) ∧
      (match value, renameValue resolve value with
      | .scalar _, .scalar _ => True
      | .pointer _, .pointer _ => True
      | .aggregate _, .aggregate _ => True
      | _, _ => False) := by
  constructor
  · exact encodeValue_rename resolve value
  · cases value <;> simp [renameValue]

def copyEncoded (bytes : List (Byte Tag)) : List (Byte Tag) := bytes.map id

def provenanceEqual [BEq Tag] : Option (Provenance Tag) →
    Option (Provenance Tag) → Bool
  | none, none => true
  | some left, some right => left.allocation == right.allocation && left.tag == right.tag
  | _, _ => false

theorem provenanceEqual_contract [BEq Tag]
    (left right : Option (Provenance Tag)) :
    match left, right with
    | none, none => provenanceEqual left right = true
    | some left, some right =>
        provenanceEqual (some left) (some right) =
          (left.allocation == right.allocation && left.tag == right.tag)
    | _, _ => provenanceEqual left right = false := by
  cases left <;> cases right <;> rfl

def decodePointer [BEq Tag] (bytes : List (Byte Tag)) : Option (Pointer Tag) := do
  if bytes.length != 8 then none
  let first ← bytes.head?
  let provenance ← match first with
    | .value _ provenance (some 0) => some provenance
    | _ => none
  let fragments := bytes.zipIdx.all fun entry =>
    match entry.1, entry.2 with
    | .value _ p (some fragment), index =>
        provenanceEqual p provenance && fragment == index
    | _, _ => false
  if !fragments then none
  let address := bytes.foldl (fun value byte =>
    match byte with
    | .value bits _ (some fragment) => value + bits.toNat * (256 ^ fragment)
    | _ => value) 0
  some { provenance := provenance, address := address }

theorem copyEncoded_preserves (bytes : List (Byte Tag)) :
    copyEncoded bytes = bytes := by
  simp [copyEncoded]

theorem copyEncoded_contract (bytes : List (Byte Tag)) :
    copyEncoded bytes = bytes ∧
      (copyEncoded bytes).length = bytes.length := by
  exact ⟨copyEncoded_preserves bytes, by simp [copyEncoded]⟩

theorem decodePointer_wrong_length_refusal [BEq Tag]
    (bytes : List (Byte Tag)) (hlength : bytes.length ≠ 8) :
    decodePointer bytes = none := by
  simp [decodePointer, hlength]

theorem decodePointer_first_fragment_refusal [BEq Tag]
    (first : Byte Tag) (rest : List (Byte Tag))
    (hfirst : ∀ bits provenance, first ≠ .value bits provenance (some 0)) :
    decodePointer (first :: rest) = none := by
  simp [decodePointer, hfirst]

theorem decodePointer_success_contract [BEq Tag]
    (bytes : List (Byte Tag)) (result : Pointer Tag)
    (hresult : decodePointer bytes = some result) :
    bytes.length = 8 ∧
      ∃ bits provenance,
        bytes.head? = some (.value bits provenance (some 0)) := by
  have hlength : bytes.length = 8 := by
    by_cases hlength : bytes.length = 8
    · exact hlength
    · simp [decodePointer, hlength] at hresult
  constructor
  · exact hlength
  · cases bytes with
    | nil => simp at hlength
    | cons first rest =>
        cases first with
        | uninitialized => simp [decodePointer] at hresult
        | value bits provenance fragment =>
            cases fragment with
            | none => simp [decodePointer] at hresult
            | some fragment =>
                cases fragment with
                | zero => exact ⟨bits, provenance, rfl⟩
                | succ fragment => simp [decodePointer] at hresult

theorem encodePointer_rename (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    encodePointer (renamePointer resolve pointer) =
      (encodePointer pointer).map (renameByte resolve) := by
  cases pointer with
  | mk provenance address =>
      cases provenance <;> simp [encodePointer, renamePointer, renameByte, pointerByte]

theorem encodePointer_rename_contract
    (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    encodePointer (renamePointer resolve pointer) =
        (encodePointer pointer).map (renameByte resolve) ∧
      (encodePointer (renamePointer resolve pointer)).length = 8 := by
  exact ⟨encodePointer_rename resolve pointer,
    by simp [encodePointer]⟩

structure Allocation (Tag State : Type) where
  live : Bool
  address : Option Nat
  bytes : List (Byte Tag)
  state : State
deriving Repr, BEq

inductive HookChoice where
  | default
  | placement (site : Nat)
  | unspecified (site : Nat)
deriving Repr, BEq

inductive EffectiveTypeState (TypeId : Type) where
  | untyped
  | typed (type : TypeId)
  | padding
  | indeterminate
deriving Repr, BEq

structure LocationState (TypeId : Type) where
  effectiveType : EffectiveTypeState TypeId
  initialized : Bool
deriving Repr, BEq

abbrev LocationStore (TypeId : Type) :=
  List (AllocId × Nat × LocationState TypeId)

structure AllocationMetadata (Tag State TypeId : Type) where
  allocation : Allocation Tag State
  locations : List (LocationState TypeId)
deriving Repr, BEq

def listSet (values : List α) (offset : Nat) (value : α) : List α :=
  match values, offset with
  | [], _ => []
  | _ :: rest, 0 => value :: rest
  | head :: rest, n + 1 => head :: listSet rest n value

theorem listSet_length (values : List α) (offset : Nat) (value : α) :
    (listSet values offset value).length = values.length := by
  induction values generalizing offset with
  | nil => rfl
  | cons head rest ih =>
      cases offset <;> simp [listSet, ih]

theorem listSet_updates_at (values : List α) (offset : Nat) (value : α)
    (hwithin : offset < values.length) :
    (listSet values offset value)[offset]? = some value := by
  induction values generalizing offset with
  | nil => simp at hwithin
  | cons head rest ih =>
      cases offset with
      | zero => simp [listSet]
      | succ offset =>
          simp only [listSet, List.length_cons, Nat.succ_lt_succ_iff] at hwithin ⊢
          simpa using ih offset hwithin

theorem listSet_preserves_at_of_ne (values : List α) (offset : Nat) (value : α)
    (index : Nat) (hwithin : index < values.length) (hne : index ≠ offset) :
    (listSet values offset value)[index]? = values[index]? := by
  induction values generalizing offset index with
  | nil => simp at hwithin
  | cons head rest ih =>
      cases offset <;> cases index <;> simp_all [listSet, ih]

theorem listSet_out_of_bounds (values : List α) (offset : Nat) (value : α)
    (hout : values.length ≤ offset) :
    listSet values offset value = values := by
  induction values generalizing offset with
  | nil => rfl
  | cons head rest ih =>
      cases offset with
      | zero => simp at hout
      | succ offset =>
          simp only [listSet]
          congr 1
          apply ih
          exact Nat.le_of_succ_le_succ hout

structure Region where
  allocation : AllocId
  offset : Nat
  width : Nat
deriving Repr, BEq

inductive AccessKind where
  | read | write | metadata
deriving Repr, BEq

structure Footprint where
  accesses : List (AccessKind × Region)
deriving Repr, BEq

def footprintAgrees (left right : Footprint) : Prop := left = right

def footprint (kind : AccessKind) (region : Region) : Footprint :=
  { accesses := [(kind, region)] }

theorem footprint_contract (kind : AccessKind) (region : Region) :
    footprint kind region = { accesses := [(kind, region)] } ∧
      (footprint kind region).accesses.length = 1 := by
  exact ⟨rfl, by simp [footprint]⟩

def setLocation (locations : LocationStore TypeId) (allocation offset : Nat)
    (state : LocationState TypeId) : Option (LocationStore TypeId) :=
  if locations.any (fun entry => entry.1 == allocation && entry.2.1 == offset) then
    some (locations.map (fun entry =>
      if entry.1 == allocation && entry.2.1 == offset then
        (allocation, offset, state)
      else entry))
  else none

theorem setLocation_length (locations : LocationStore TypeId)
    (allocation offset : Nat) (state : LocationState TypeId)
    (result : LocationStore TypeId)
    (hresult : setLocation locations allocation offset state = some result) :
    result.length = locations.length := by
  simp [setLocation] at hresult
  rw [← hresult.2, List.length_map]

theorem setLocation_guard_refusal (locations : LocationStore TypeId)
    (allocation offset : Nat) (state : LocationState TypeId)
    (hguard : locations.any (fun entry =>
      entry.1 == allocation && entry.2.1 == offset) = false) :
    setLocation locations allocation offset state = none := by
  simp [setLocation, hguard]

theorem setLocation_success_shape (locations : LocationStore TypeId)
    (allocation offset : Nat) (state : LocationState TypeId)
    (result : LocationStore TypeId)
    (hresult : setLocation locations allocation offset state = some result) :
    result = locations.map (fun entry =>
      if entry.1 == allocation && entry.2.1 == offset then
        (allocation, offset, state)
      else entry) := by
  simp [setLocation] at hresult
  simpa using hresult.2.symm

theorem setLocation_contract
    (locations : LocationStore TypeId) (allocation offset : Nat)
    (state : LocationState TypeId) (result : LocationStore TypeId) :
    setLocation locations allocation offset state = some result ↔
      locations.any (fun entry => entry.1 == allocation && entry.2.1 == offset) = true ∧
      result = locations.map (fun entry =>
        if entry.1 == allocation && entry.2.1 == offset then
          (allocation, offset, state)
        else entry) := by
  by_cases hguard : locations.any
      (fun entry => entry.1 == allocation && entry.2.1 == offset) = true
  · unfold setLocation
    rw [if_pos hguard]
    constructor
    · intro h
      exact ⟨hguard, (Option.some.inj h).symm⟩
    · rintro ⟨_, hresult⟩
      exact congrArg some hresult.symm
  · have hguard' : locations.any
        (fun entry => entry.1 == allocation && entry.2.1 == offset) = false := by
      exact Bool.eq_false_iff.mpr hguard
    simp [setLocation, hguard']

theorem setLocation_failure_contract
    (locations : LocationStore TypeId) (allocation offset : Nat)
    (state : LocationState TypeId) :
    setLocation locations allocation offset state = none ↔
      locations.any (fun entry => entry.1 == allocation && entry.2.1 == offset) = false := by
  by_cases hguard : locations.any
      (fun entry => entry.1 == allocation && entry.2.1 == offset) = true
  · have hguard' : locations.any
        (fun entry => entry.1 == allocation && entry.2.1 == offset) ≠ false := by
      simpa using hguard
    simp [setLocation, hguard, hguard']
  · have hfalse : locations.any
        (fun entry => entry.1 == allocation && entry.2.1 == offset) = false := by
      exact Bool.eq_false_iff.mpr hguard
    simp [setLocation, hfalse]

structure Store (Tag State : Type) where
  allocations : List (AllocId × Allocation Tag State)
  nextId : AllocId
deriving Repr, BEq

def renameAllocation (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) : AllocId × Allocation Tag State :=
  let allocation := entry.2
  (entry.1,
    { allocation with
      address := allocation.address.map (fun _ => resolve entry.1)
      bytes := allocation.bytes.map (renameByte resolve) })

def renameAllocationValue (resolve : AllocId → Nat) (id : AllocId)
    (allocation : Allocation Tag State) : Allocation Tag State :=
  { allocation with
    address := allocation.address.map (fun _ => resolve id)
    bytes := allocation.bytes.map (renameByte resolve) }

theorem renameAllocationValue_contract (resolve : AllocId → Nat)
    (id : AllocId) (allocation : Allocation Tag State) :
    (renameAllocationValue resolve id allocation).live = allocation.live ∧
      (renameAllocationValue resolve id allocation).state = allocation.state ∧
      (renameAllocationValue resolve id allocation).address =
        allocation.address.map (fun _ => resolve id) ∧
      (renameAllocationValue resolve id allocation).bytes =
        allocation.bytes.map (renameByte resolve) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem renameAllocation_value (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).2 =
      renameAllocationValue resolve entry.1 entry.2 := by
  rfl

theorem renameAllocation_fields (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).2.address =
        entry.2.address.map (fun _ => resolve entry.1) ∧
      (renameAllocation resolve entry).2.bytes =
        entry.2.bytes.map (renameByte resolve) := by
  exact ⟨rfl, rfl⟩

theorem renameByte_idempotent (resolve : AllocId → Nat) (byte : Byte Tag) :
    renameByte resolve (renameByte resolve byte) = renameByte resolve byte := by
  cases byte with
  | uninitialized => rfl
  | value bits provenance fragment =>
      cases provenance <;> cases fragment <;> rfl

theorem renameByte_comp (first second : AllocId → Nat) (byte : Byte Tag) :
    renameByte second (renameByte first byte) = renameByte second byte := by
  cases byte with
  | uninitialized => rfl
  | value bits provenance fragment =>
      cases provenance <;> cases fragment <;> rfl

theorem renameByte_renaming_contract
    (resolve : AllocId → Nat) (byte : Byte Tag) :
    byteFragment (renameByte resolve byte) = byteFragment byte ∧
      byteProvenance (renameByte resolve byte) = byteProvenance byte ∧
      renameByte resolve (renameByte resolve byte) = renameByte resolve byte := by
  exact ⟨renameByte_preserves_fragment resolve byte,
    renameByte_preserves_provenance resolve byte,
    renameByte_idempotent resolve byte⟩

theorem renameByte_composition_contract
    (first second : AllocId → Nat) (byte : Byte Tag) :
    renameByte second (renameByte first byte) = renameByte second byte ∧
      byteFragment (renameByte second (renameByte first byte)) = byteFragment byte ∧
      byteProvenance (renameByte second (renameByte first byte)) = byteProvenance byte := by
  exact ⟨renameByte_comp first second byte,
    by rw [renameByte_comp]; exact renameByte_preserves_fragment second byte,
    by rw [renameByte_comp]; exact renameByte_preserves_provenance second byte⟩

theorem optionResolve_idempotent (resolve : AllocId → Nat)
    (address : Option Nat) :
    Option.map (fun _ => resolve 0) (Option.map (fun _ => resolve 0) address) =
      address.map (fun _ => resolve 0) := by
  cases address <;> rfl

theorem optionResolve_comp (first second : AllocId → Nat)
    (id : AllocId) (address : Option Nat) :
    Option.map (fun _ => second id) (Option.map (fun _ => first id) address) =
      address.map (fun _ => second id) := by
  cases address <;> rfl

theorem optionResolve_comp_direct (first second : AllocId → Nat)
    (id : AllocId) (address : Option Nat) :
    Option.map ((fun x => second id) ∘ (fun x => first id)) address =
      Option.map (fun _ => second id) address := by
  cases address <;> rfl

def renameStore (resolve : AllocId → Nat) (store : Store Tag State) : Store Tag State :=
  { store with allocations := store.allocations.map (renameAllocation resolve) }

theorem renameStore_nextId
    (resolve : AllocId → Nat) (store : Store Tag State) :
    (renameStore resolve store).nextId = store.nextId := by
  rfl

theorem renameStore_allocation_count
    (resolve : AllocId → Nat) (store : Store Tag State) :
    (renameStore resolve store).allocations.length = store.allocations.length := by
  simp [renameStore]

theorem renameAllocation_byte_count
    (resolve : AllocId → Nat) (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).2.bytes.length = entry.2.bytes.length := by
  simp [renameAllocation]

def storesCorrespond (resolve : AllocId → Nat)
    (source target : Store Tag State) : Prop :=
  target = renameStore resolve source

theorem renameAllocation_preserves_id (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).1 = entry.1 := by
  rfl

theorem renameAllocation_preserves_liveness (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).2.live = entry.2.live := by
  rfl

theorem renameAllocation_preserves_state (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).2.state = entry.2.state := by
  rfl

theorem renameAllocation_contract (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).1 = entry.1 ∧
      (renameAllocation resolve entry).2.live = entry.2.live ∧
      (renameAllocation resolve entry).2.state = entry.2.state ∧
      (renameAllocation resolve entry).2.address =
        entry.2.address.map (fun _ => resolve entry.1) ∧
      (renameAllocation resolve entry).2.bytes =
        entry.2.bytes.map (renameByte resolve) := by
  exact ⟨renameAllocation_preserves_id resolve entry,
    renameAllocation_preserves_liveness resolve entry,
    renameAllocation_preserves_state resolve entry,
    renameAllocation_fields resolve entry |>.1,
    renameAllocation_fields resolve entry |>.2⟩

theorem renameAllocation_size_contract (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).2.bytes.length = entry.2.bytes.length ∧
      (renameAllocation resolve entry).2.live = entry.2.live ∧
      (renameAllocation resolve entry).2.state = entry.2.state := by
  exact ⟨renameAllocation_byte_count resolve entry,
    renameAllocation_preserves_liveness resolve entry,
    renameAllocation_preserves_state resolve entry⟩

theorem renameStore_idempotent (resolve : AllocId → Nat) (store : Store Tag State) :
    renameStore resolve (renameStore resolve store) = renameStore resolve store := by
  cases store with
  | mk allocations nextId =>
      simp [renameStore, renameAllocation, renameByte_idempotent,
        optionResolve_idempotent, optionResolve_comp_direct]

theorem renameStore_contract (resolve : AllocId → Nat) (store : Store Tag State) :
    (renameStore resolve store).nextId = store.nextId ∧
      (renameStore resolve store).allocations.length = store.allocations.length ∧
      renameStore resolve (renameStore resolve store) = renameStore resolve store := by
  exact ⟨renameStore_nextId resolve store,
    renameStore_allocation_count resolve store,
    renameStore_idempotent resolve store⟩

theorem renameStore_comp (first second : AllocId → Nat) (store : Store Tag State) :
    renameStore second (renameStore first store) = renameStore second store := by
  cases store with
  | mk allocations nextId =>
      simp [renameStore, renameAllocation, renameByte_comp,
        optionResolve_comp, optionResolve_comp_direct]

theorem renameStore_composition_contract
    (first second : AllocId → Nat) (store : Store Tag State) :
    renameStore second (renameStore first store) = renameStore second store ∧
      (renameStore second (renameStore first store)).nextId = store.nextId ∧
      (renameStore second (renameStore first store)).allocations.length =
        store.allocations.length := by
  exact ⟨renameStore_comp first second store,
    by simp [renameStore],
    by simp [renameStore]⟩

theorem storesCorrespond_refl (resolve : AllocId → Nat) (store : Store Tag State) :
    storesCorrespond resolve (renameStore resolve store) (renameStore resolve store) := by
  simp [storesCorrespond, renameStore_idempotent]

theorem storesCorrespond_contract
    (resolve : AllocId → Nat) (source : Store Tag State) :
    storesCorrespond resolve source (renameStore resolve source) ∧
      storesCorrespond resolve (renameStore resolve source)
        (renameStore resolve (renameStore resolve source)) := by
  constructor
  · rfl
  · simp [storesCorrespond, renameStore_idempotent]

def renameRegion (_resolve : AllocId → Nat) (region : Region) : Region := region

def renameFootprint (resolve : AllocId → Nat) (footprint : Footprint) : Footprint :=
  { accesses := footprint.accesses.map (fun access =>
      (access.1, renameRegion resolve access.2)) }

theorem renameRegion_identity (resolve : AllocId → Nat) (region : Region) :
    renameRegion resolve region = region := by
  rfl

theorem renameRegion_contract (first second : AllocId → Nat) (region : Region) :
    renameRegion first region = region ∧
      renameRegion second (renameRegion first region) = renameRegion second region := by
  exact ⟨renameRegion_identity first region,
    by simpa [renameRegion_identity] using renameRegion_identity second region⟩

theorem renameFootprint_identity (resolve : AllocId → Nat) (footprint : Footprint) :
    renameFootprint resolve footprint = footprint := by
  simp [renameFootprint, renameRegion]

theorem renameFootprint_comp (first second : AllocId → Nat) (footprint : Footprint) :
    renameFootprint second (renameFootprint first footprint) =
      renameFootprint second footprint := by
  simp [renameFootprint, renameRegion]

theorem renameFootprint_access_count (resolve : AllocId → Nat)
    (footprint : Footprint) :
    (renameFootprint resolve footprint).accesses.length = footprint.accesses.length := by
  simp [renameFootprint]

theorem renameFootprint_contract (resolve : AllocId → Nat)
    (footprint : Footprint) :
    (renameFootprint resolve footprint).accesses =
        footprint.accesses.map (fun access =>
          (access.1, renameRegion resolve access.2)) ∧
      (renameFootprint resolve footprint).accesses.length =
        footprint.accesses.length ∧
      renameFootprint resolve (renameFootprint resolve footprint) =
        renameFootprint resolve footprint := by
  exact ⟨rfl, renameFootprint_access_count resolve footprint,
    renameFootprint_comp resolve resolve footprint⟩

structure HookRequest where
  choice : HookChoice
  footprint : Footprint
deriving Repr

def renameHookRequest (resolve : AllocId → Nat) (request : HookRequest) : HookRequest :=
  { request with footprint := renameFootprint resolve request.footprint }

theorem renameHookRequest_identity (resolve : AllocId → Nat) (request : HookRequest) :
    renameHookRequest resolve request = request := by
  simp [renameHookRequest, renameFootprint_identity]

theorem renameHookRequest_footprint
    (resolve : AllocId → Nat) (request : HookRequest) :
    (renameHookRequest resolve request).footprint =
      renameFootprint resolve request.footprint := by
  rfl

theorem renameHookRequest_access_count
    (resolve : AllocId → Nat) (request : HookRequest) :
    (renameHookRequest resolve request).footprint.accesses.length =
      request.footprint.accesses.length := by
  rw [renameHookRequest_footprint]
  exact renameFootprint_access_count resolve request.footprint

theorem renameHookRequest_choice
    (resolve : AllocId → Nat) (request : HookRequest) :
    (renameHookRequest resolve request).choice = request.choice := by
  rfl

theorem renameHookRequest_contract
    (resolve : AllocId → Nat) (request : HookRequest) :
    (renameHookRequest resolve request).choice = request.choice ∧
      (renameHookRequest resolve request).footprint =
        renameFootprint resolve request.footprint ∧
      (renameHookRequest resolve request).footprint.accesses.length =
        request.footprint.accesses.length := by
  exact ⟨renameHookRequest_choice resolve request,
    renameHookRequest_footprint resolve request,
    renameHookRequest_access_count resolve request⟩

structure Fault (F : Type) where
  value : F
deriving Repr

inductive Result (Tag State F A : Type) where
  | ok (value : A) (store : Store Tag State) (footprint : Footprint)
  | fault (error : Fault F) (store : Store Tag State) (footprint : Footprint)
  | refused (reason : String) (store : Store Tag State) (footprint : Footprint)
deriving Repr

def renameResult {Tag State F : Type} (resolve : AllocId → Nat) :
    Result Tag State F (Byte Tag) → Result Tag State F (Byte Tag)
  | .ok value store footprint =>
      .ok (renameByte resolve value) (renameStore resolve store)
        (renameFootprint resolve footprint)
  | .fault error store footprint =>
      .fault error (renameStore resolve store) (renameFootprint resolve footprint)
  | .refused reason store footprint =>
      .refused reason (renameStore resolve store) (renameFootprint resolve footprint)

theorem renameResult_success_shape {Tag State F : Type}
    (resolve : AllocId → Nat) (value : Byte Tag)
    (store : Store Tag State) (footprint : Footprint) :
    renameResult (F := F) resolve (.ok value store footprint) =
      (.ok (renameByte resolve value) (renameStore resolve store)
        (renameFootprint resolve footprint) : Result Tag State F (Byte Tag)) := by
  rfl

theorem renameResult_comp {Tag State F : Type} (first second : AllocId → Nat)
    (result : Result Tag State F (Byte Tag)) :
    renameResult (Tag := Tag) (State := State) (F := F) second
        (renameResult (Tag := Tag) (State := State) (F := F) first result) =
      renameResult (Tag := Tag) (State := State) (F := F) second result := by
  cases result with
  | ok value store footprint =>
      simp only [renameResult]
      rw [renameByte_comp, renameStore_comp, renameFootprint_comp]
  | fault error store footprint =>
      simp only [renameResult]
      rw [renameStore_comp, renameFootprint_comp]
  | refused reason store footprint =>
      simp only [renameResult]
      rw [renameStore_comp, renameFootprint_comp]

theorem renameResult_idempotent {Tag State F : Type}
    (resolve : AllocId → Nat) (result : Result Tag State F (Byte Tag)) :
    renameResult resolve (renameResult resolve result) = renameResult resolve result := by
  cases result with
  | ok value store footprint =>
      simp only [renameResult]
      rw [renameByte_idempotent, renameStore_idempotent, renameFootprint_comp]
  | fault error store footprint =>
      simp only [renameResult]
      rw [renameStore_idempotent, renameFootprint_comp]
  | refused reason store footprint =>
      simp only [renameResult]
      rw [renameStore_idempotent, renameFootprint_comp]

theorem renameResult_kind_preserved {Tag State F : Type} (resolve : AllocId → Nat)
    (result : Result Tag State F (Byte Tag)) :
    match result, renameResult resolve result with
    | .ok .., .ok .. => True
    | .fault .., .fault .. => True
    | .refused .., .refused .. => True
    | _, _ => False := by
  cases result <;> simp [renameResult]

theorem renameResult_refusal_reason {Tag State F : Type} (resolve : AllocId → Nat)
    (reason : String) (store : Store Tag State) (footprint : Footprint) :
    renameResult (Tag := Tag) (State := State) (F := F) resolve
        (.refused reason store footprint) =
      (.refused reason (renameStore resolve store) (renameFootprint resolve footprint) :
        Result Tag State F (Byte Tag)) := by
  rfl

theorem renameResult_fault_error {Tag State F : Type} (resolve : AllocId → Nat)
    (error : Fault F) (store : Store Tag State) (footprint : Footprint) :
    renameResult (Tag := Tag) (State := State) (F := F) resolve
        (.fault error store footprint) =
      (.fault error (renameStore resolve store) (renameFootprint resolve footprint) :
        Result Tag State F (Byte Tag)) := by
  rfl

theorem renameResult_footprint_access_count {Tag State F : Type}
    (resolve : AllocId → Nat) (result : Result Tag State F (Byte Tag)) :
    match result, renameResult resolve result with
    | .ok _ _ source, .ok _ _ target => target.accesses.length = source.accesses.length
    | .fault _ _ source, .fault _ _ target => target.accesses.length = source.accesses.length
    | .refused _ _ source, .refused _ _ target => target.accesses.length = source.accesses.length
    | _, _ => True := by
  cases result <;> simp [renameResult, renameFootprint]

theorem renameResult_contract {Tag State F : Type}
    (resolve : AllocId → Nat) (result : Result Tag State F (Byte Tag)) :
    match result, renameResult resolve result with
    | .ok value store footprint, .ok renamedValue renamedStore renamedFootprint =>
        renamedValue = renameByte resolve value ∧
          renamedStore = renameStore resolve store ∧
          renamedFootprint = renameFootprint resolve footprint
    | .fault error store footprint, .fault renamedError renamedStore renamedFootprint =>
        renamedError = error ∧
          renamedStore = renameStore resolve store ∧
          renamedFootprint = renameFootprint resolve footprint
    | .refused reason store footprint, .refused renamedReason renamedStore renamedFootprint =>
        renamedReason = reason ∧
          renamedStore = renameStore resolve store ∧
          renamedFootprint = renameFootprint resolve footprint
    | _, _ => False := by
  cases result <;> simp [renameResult]

theorem renameResult_shape_contract {Tag State F : Type}
    (resolve : AllocId → Nat) (result : Result Tag State F (Byte Tag)) :
    match result with
    | .ok value store footprint =>
        renameResult resolve result =
          .ok (renameByte resolve value) (renameStore resolve store)
            (renameFootprint resolve footprint)
    | .fault error store footprint =>
        renameResult resolve result =
          .fault error (renameStore resolve store)
            (renameFootprint resolve footprint)
    | .refused reason store footprint =>
        renameResult resolve result =
          .refused reason (renameStore resolve store)
            (renameFootprint resolve footprint) := by
  cases result <;> rfl

theorem renameResult_composition_contract {Tag State F : Type}
    (first second : AllocId → Nat) (result : Result Tag State F (Byte Tag)) :
    renameResult second (renameResult first result) = renameResult second result := by
  exact renameResult_comp first second result

def lookup (store : Store Tag State) (id : AllocId) : Option (Allocation Tag State) :=
  store.allocations.find? (fun entry => entry.1 == id) |>.map (·.2)

theorem lookup_result_contract
    (store : Store Tag State) (id : AllocId)
    (result : Option (Allocation Tag State))
    (hresult : lookup store id = result) :
    (∃ entry,
      store.allocations.find? (fun candidate => candidate.1 == id) = some entry ∧
      result = some entry.2) ∨
    (store.allocations.find? (fun candidate => candidate.1 == id) = none ∧
      result = none) := by
  cases hfind : store.allocations.find? (fun candidate => candidate.1 == id) with
  | some entry =>
      left
      refine ⟨entry, rfl, ?_⟩
      simpa [lookup, hfind] using hresult.symm
  | none =>
      right
      refine ⟨rfl, ?_⟩
      simpa [lookup, hfind] using hresult.symm

theorem lookup_renameStore (resolve : AllocId → Nat)
    (store : Store Tag State) (id : AllocId) :
    lookup (renameStore resolve store) id =
      (lookup store id).map (renameAllocationValue resolve id) := by
  cases store with
  | mk allocations nextId =>
      induction allocations with
      | nil => rfl
      | cons entry rest ih =>
          cases entry with
          | mk entryId allocation =>
              by_cases h : entryId == id
              · have hid : entryId = id := by simpa using h
                simp [lookup, renameStore, renameAllocation, renameAllocationValue,
                  h, hid]
              · simpa [lookup, renameStore, renameAllocation, renameAllocationValue,
                  Function.comp_def, h] using ih

theorem lookup_renameStore_none (resolve : AllocId → Nat)
    (store : Store Tag State) (id : AllocId)
    (hlookup : lookup store id = none) :
    lookup (renameStore resolve store) id = none := by
  rw [lookup_renameStore]
  simp [hlookup]

theorem lookup_renameStore_contract (resolve : AllocId → Nat)
    (store : Store Tag State) (id : AllocId) :
    lookup (renameStore resolve store) id =
        (lookup store id).map (renameAllocationValue resolve id) ∧
      (lookup store id = none → lookup (renameStore resolve store) id = none) := by
  constructor
  · exact lookup_renameStore resolve store id
  · intro hlookup
    exact lookup_renameStore_none resolve store id hlookup

theorem lookup_renameStore_some
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (allocation : Allocation Tag State)
    (hlookup : lookup store id = some allocation) :
    lookup (renameStore resolve store) id =
      some (renameAllocationValue resolve id allocation) := by
  rw [lookup_renameStore, hlookup]
  rfl

theorem lookup_renameStore_some_contract
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (allocation : Allocation Tag State)
    (hlookup : lookup store id = some allocation) :
    lookup (renameStore resolve store) id =
      some (renameAllocationValue resolve id allocation) ∧
      (renameAllocationValue resolve id allocation).live = allocation.live ∧
      (renameAllocationValue resolve id allocation).state = allocation.state := by
  constructor
  · exact lookup_renameStore_some resolve store id allocation hlookup
  · exact ⟨rfl, rfl⟩

theorem lookup_renameStore_composition
    (first second : AllocId → Nat) (store : Store Tag State) (id : AllocId) :
    lookup (renameStore second (renameStore first store)) id =
      (lookup store id).map
        (renameAllocationValue second id) := by
  rw [renameStore_comp]
  exact lookup_renameStore second store id

def bytesWf (id : AllocId) : List (Byte Tag) → Prop
  | [] => True
  | .uninitialized :: rest => bytesWf id rest
  | .value _ none _ :: rest => bytesWf id rest
  | .value _ (some provenance) _ :: rest =>
      provenance.allocation == id ∧ bytesWf id rest

def AllocationMetadata.wellFormed (metadata : AllocationMetadata Tag State TypeId)
    (id : AllocId) : Prop :=
  bytesWf id metadata.allocation.bytes ∧
    metadata.locations.length = metadata.allocation.bytes.length

def storeMetadataByte (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) :
    Option (AllocationMetadata Tag State TypeId × Footprint) :=
  if offset ≥ metadata.allocation.bytes.length then none
  else
    let allocation := { metadata.allocation with
      bytes := listSet metadata.allocation.bytes offset byte }
    some ({ metadata with allocation := allocation },
      footprint .write { allocation := 0, offset := offset, width := 1 })

theorem storeMetadataByte_empty_none
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (hbytes : metadata.allocation.bytes = []) :
    storeMetadataByte metadata offset byte = none := by
  simp [storeMetadataByte, hbytes]

theorem storeMetadataByte_outOfBounds
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag)
    (hout : metadata.allocation.bytes.length ≤ offset) :
    storeMetadataByte metadata offset byte = none := by
  simp [storeMetadataByte, hout]

theorem storeMetadataByte_failure_contract
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) :
    storeMetadataByte metadata offset byte = none ↔
      metadata.allocation.bytes.length ≤ offset := by
  by_cases hout : metadata.allocation.bytes.length ≤ offset
  · simp [storeMetadataByte, hout]
  · simp [storeMetadataByte, hout]

theorem storeMetadataByte_preserves_locations
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : storeMetadataByte metadata offset byte = some result) :
    result.1.locations = metadata.locations := by
  simp [storeMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rw [← hEq]

theorem storeMetadataByte_success_shape
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : storeMetadataByte metadata offset byte = some result) :
    result.1.allocation.bytes = listSet metadata.allocation.bytes offset byte ∧
      result.1.locations = metadata.locations ∧
      result.2 = footprint .write { allocation := 0, offset := offset, width := 1 } := by
  simp [storeMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rcases hEq with rfl
  exact ⟨rfl, rfl, rfl⟩

theorem storeMetadataByte_preserves_byte_length
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : storeMetadataByte metadata offset byte = some result) :
    result.1.allocation.bytes.length = metadata.allocation.bytes.length := by
  simp [storeMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rw [← hEq]
  exact listSet_length metadata.allocation.bytes offset _

theorem storeMetadataByte_preserves_payload
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : storeMetadataByte metadata offset byte = some result) :
    result.1.allocation.live = metadata.allocation.live ∧
      result.1.allocation.address = metadata.allocation.address ∧
      result.1.allocation.state = metadata.allocation.state := by
  simp [storeMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rcases hEq with rfl
  exact ⟨rfl, rfl, rfl⟩

theorem storeMetadataByte_preserves_wellFormed
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : storeMetadataByte metadata offset byte = some result)
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length) :
    result.1.wellFormed 0 := by
  simp [storeMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rcases hEq with rfl
  unfold AllocationMetadata.wellFormed
  exact ⟨hbytes, by simpa [listSet_length] using hlocations⟩

theorem storeMetadataByte_contract
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : storeMetadataByte metadata offset byte = some result)
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length) :
    result.1.allocation.bytes = listSet metadata.allocation.bytes offset byte ∧
      result.1.locations = metadata.locations ∧
      result.2 = footprint .write { allocation := 0, offset := offset, width := 1 } ∧
      result.1.allocation.live = metadata.allocation.live ∧
      result.1.allocation.address = metadata.allocation.address ∧
      result.1.allocation.state = metadata.allocation.state ∧
      result.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
      result.1.wellFormed 0 := by
  rcases storeMetadataByte_success_shape metadata offset byte result hresult with
    ⟨hbytes', hlocations', hfootprint⟩
  rcases storeMetadataByte_preserves_payload metadata offset byte result hresult with
    ⟨hlive, haddress, hstate⟩
  exact ⟨hbytes', hlocations', hfootprint, hlive, haddress, hstate,
    storeMetadataByte_preserves_byte_length metadata offset byte result hresult,
    storeMetadataByte_preserves_wellFormed metadata offset byte result hresult
      hbytes hlocations⟩

def typedStoreMetadataByte (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag) :
    Option (AllocationMetadata Tag State TypeId × Footprint) :=
  if offset ≥ metadata.allocation.bytes.length then none
  else
    let allocation := { metadata.allocation with
      bytes := listSet metadata.allocation.bytes offset byte }
    let locations := listSet metadata.locations offset
      { effectiveType := .typed typeId, initialized := true }
    some ({ allocation := allocation, locations := locations },
      footprint .write { allocation := 0, offset := offset, width := 1 })

theorem typedStoreMetadataByte_empty_none
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (hbytes : metadata.allocation.bytes = []) :
    typedStoreMetadataByte metadata offset typeId byte = none := by
  simp [typedStoreMetadataByte, hbytes]

theorem typedStoreMetadataByte_outOfBounds
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (hout : metadata.allocation.bytes.length ≤ offset) :
    typedStoreMetadataByte metadata offset typeId byte = none := by
  simp [typedStoreMetadataByte, hout]

theorem typedStoreMetadataByte_failure_contract
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag) :
    typedStoreMetadataByte metadata offset typeId byte = none ↔
      metadata.allocation.bytes.length ≤ offset := by
  by_cases hout : metadata.allocation.bytes.length ≤ offset
  · simp [typedStoreMetadataByte, hout]
  · simp [typedStoreMetadataByte, hout]

theorem typedStoreMetadataByte_preserves_length
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : typedStoreMetadataByte metadata offset typeId byte = some result) :
    result.1.locations.length = metadata.locations.length := by
  simp [typedStoreMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rw [← hEq]
  exact listSet_length metadata.locations offset _

theorem typedStoreMetadataByte_preserves_byte_length
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : typedStoreMetadataByte metadata offset typeId byte = some result) :
    result.1.allocation.bytes.length = metadata.allocation.bytes.length := by
  simp [typedStoreMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rw [← hEq]
  exact listSet_length metadata.allocation.bytes offset _

theorem typedStoreMetadataByte_success_shape
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : typedStoreMetadataByte metadata offset typeId byte = some result) :
    result.1.allocation.bytes = listSet metadata.allocation.bytes offset byte ∧
      result.1.locations = listSet metadata.locations offset
        { effectiveType := .typed typeId, initialized := true } ∧
      result.2 = footprint .write { allocation := 0, offset := offset, width := 1 } := by
  simp [typedStoreMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rcases hEq with rfl
  exact ⟨rfl, rfl, rfl⟩

theorem typedStoreMetadataByte_footprint
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : typedStoreMetadataByte metadata offset typeId byte = some result) :
    result.2 = footprint .write { allocation := 0, offset := offset, width := 1 } := by
  simp [typedStoreMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  exact congrArg (fun pair => pair.2) hEq.symm

theorem typedStoreMetadataByte_preserves_payload
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : typedStoreMetadataByte metadata offset typeId byte = some result) :
    result.1.allocation.live = metadata.allocation.live ∧
      result.1.allocation.address = metadata.allocation.address ∧
      result.1.allocation.state = metadata.allocation.state := by
  simp [typedStoreMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rcases hEq with rfl
  exact ⟨rfl, rfl, rfl⟩

theorem typedStoreMetadataByte_preserves_wellFormed
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : typedStoreMetadataByte metadata offset typeId byte = some result)
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length) :
    result.1.wellFormed 0 := by
  simp [typedStoreMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rcases hEq with rfl
  unfold AllocationMetadata.wellFormed
  exact ⟨hbytes, by simpa [listSet_length] using hlocations⟩

theorem typedStoreMetadataByte_contract
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : typedStoreMetadataByte metadata offset typeId byte = some result)
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length) :
    result.1.allocation.bytes = listSet metadata.allocation.bytes offset byte ∧
      result.1.locations = listSet metadata.locations offset
        { effectiveType := .typed typeId, initialized := true } ∧
      result.2 = footprint .write { allocation := 0, offset := offset, width := 1 } ∧
      result.1.allocation.live = metadata.allocation.live ∧
      result.1.allocation.address = metadata.allocation.address ∧
      result.1.allocation.state = metadata.allocation.state ∧
      result.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
      result.1.locations.length = metadata.locations.length ∧
      result.1.wellFormed 0 := by
  rcases typedStoreMetadataByte_success_shape metadata offset typeId byte result hresult with
    ⟨hbytes', hlocations', hfootprint⟩
  rcases typedStoreMetadataByte_preserves_payload metadata offset typeId byte result hresult with
    ⟨hlive, haddress, hstate⟩
  exact ⟨hbytes', hlocations', hfootprint, hlive, haddress, hstate,
    typedStoreMetadataByte_preserves_byte_length metadata offset typeId byte result hresult,
    typedStoreMetadataByte_preserves_length metadata offset typeId byte result hresult,
    typedStoreMetadataByte_preserves_wellFormed metadata offset typeId byte result
      hresult hbytes hlocations⟩

def renameMetadata (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    AllocationMetadata Tag State TypeId :=
  { metadata with
    allocation := { metadata.allocation with
      address := metadata.allocation.address.map (fun _ => resolve id)
      bytes := metadata.allocation.bytes.map (renameByte resolve) } }

theorem renameMetadata_preserves_locations (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).locations = metadata.locations := by
  rfl

theorem renameMetadata_preserves_byte_length (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).allocation.bytes.length =
      metadata.allocation.bytes.length := by
  simp [renameMetadata]

theorem renameMetadata_preserves_location_length (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).locations.length = metadata.locations.length := by
  rfl

theorem renameMetadata_preserves_liveness (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).allocation.live = metadata.allocation.live := by
  rfl

theorem renameMetadata_preserves_state (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).allocation.state = metadata.allocation.state := by
  rfl

theorem renameMetadata_bytes_shape (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).allocation.bytes =
      metadata.allocation.bytes.map (renameByte resolve) := by
  rfl

theorem renameMetadata_address_shape (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).allocation.address =
      metadata.allocation.address.map (fun _ => resolve id) := by
  rfl

theorem renameMetadata_address_presence (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).allocation.address.isSome =
      metadata.allocation.address.isSome := by
  simp [renameMetadata]

theorem renameMetadata_comp (first second : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    renameMetadata second id (renameMetadata first id metadata) =
      renameMetadata second id metadata := by
  cases metadata with
  | mk allocation locations =>
      cases allocation with
      | mk live address bytes state =>
          simp only [renameMetadata, Option.map_map]
          congr 2
          rw [List.map_map]
          apply List.map_congr_left
          intro value hvalue
          exact renameByte_comp first second value

theorem renameMetadata_contract (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).locations = metadata.locations ∧
      (renameMetadata resolve id metadata).allocation.live =
        metadata.allocation.live ∧
      (renameMetadata resolve id metadata).allocation.state =
        metadata.allocation.state ∧
      (renameMetadata resolve id metadata).allocation.address =
        metadata.allocation.address.map (fun _ => resolve id) ∧
      (renameMetadata resolve id metadata).allocation.bytes =
        metadata.allocation.bytes.map (renameByte resolve) ∧
      (renameMetadata resolve id metadata).allocation.bytes.length =
        metadata.allocation.bytes.length ∧
      (renameMetadata resolve id (renameMetadata resolve id metadata)) =
        renameMetadata resolve id metadata := by
  exact ⟨renameMetadata_preserves_locations resolve id metadata,
    renameMetadata_preserves_liveness resolve id metadata,
    renameMetadata_preserves_state resolve id metadata,
    renameMetadata_address_shape resolve id metadata,
    renameMetadata_bytes_shape resolve id metadata,
    renameMetadata_preserves_byte_length resolve id metadata,
    renameMetadata_comp resolve resolve id metadata⟩

theorem renameMetadata_composition_contract
    (first second : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    renameMetadata second id (renameMetadata first id metadata) =
        renameMetadata second id metadata ∧
      (renameMetadata second id (renameMetadata first id metadata)).allocation.bytes.length =
        metadata.allocation.bytes.length := by
  exact ⟨renameMetadata_comp first second id metadata,
    by simp [renameMetadata]⟩

def pairedTypedStoreMetadataByte [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag) :
    Option ((AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint)) := do
  let sourceResult ← typedStoreMetadataByte metadata offset typeId byte
  let targetResult ← typedStoreMetadataByte (renameMetadata resolve id metadata)
    offset typeId (renameByte resolve byte)
  if targetResult.1 == renameMetadata resolve id sourceResult.1 &&
      targetResult.2 == sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedTypedStoreMetadataByte_empty_none
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (hbytes : metadata.allocation.bytes = []) :
    pairedTypedStoreMetadataByte resolve id metadata offset typeId byte = none := by
  simp [pairedTypedStoreMetadataByte, typedStoreMetadataByte,
    renameMetadata, hbytes]

theorem pairedTypedStoreMetadataByte_decompose
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedTypedStoreMetadataByte resolve id metadata offset typeId byte =
      some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
          exact ⟨sourceResult, targetResult, hresult.2.symm⟩

theorem pairedTypedStoreMetadataByte_sound
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedTypedStoreMetadataByte resolve id metadata offset typeId byte =
      some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      typedStoreMetadataByte metadata offset typeId byte = some sourceResult ∧
      typedStoreMetadataByte (renameMetadata resolve id metadata) offset typeId
        (renameByte resolve byte) = some targetResult ∧
      (targetResult.1 == renameMetadata resolve id sourceResult.1) = true ∧
      (targetResult.2 == sourceResult.2) = true := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
          rcases hresult with ⟨hcondition, hpair⟩
          exact ⟨sourceResult, targetResult, hpair.symm,
            by simpa using hs, by simpa using ht,
            hcondition.1, hcondition.2⟩

theorem pairedTypedStoreMetadataByte_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (hrefusal : typedStoreMetadataByte metadata offset typeId byte = none ∨
      typedStoreMetadataByte (renameMetadata resolve id metadata) offset typeId
        (renameByte resolve byte) = none) :
    pairedTypedStoreMetadataByte resolve id metadata offset typeId byte = none := by
  cases hrefusal with
  | inl hsource => simp [pairedTypedStoreMetadataByte, hsource]
  | inr htarget => simp [pairedTypedStoreMetadataByte, htarget]

theorem pairedTypedStoreMetadataByte_refusal_source
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (hsource : typedStoreMetadataByte metadata offset typeId byte = none) :
    pairedTypedStoreMetadataByte resolve id metadata offset typeId byte = none := by
  simp [pairedTypedStoreMetadataByte, hsource]

theorem pairedTypedStoreMetadataByte_refusal_target
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (htarget : typedStoreMetadataByte (renameMetadata resolve id metadata)
      offset typeId (renameByte resolve byte) = none) :
    pairedTypedStoreMetadataByte resolve id metadata offset typeId byte = none := by
  simp [pairedTypedStoreMetadataByte, htarget]

theorem pairedTypedStoreMetadataByte_guard_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (sourceResult targetResult : AllocationMetadata Tag State TypeId × Footprint)
    (hsource : typedStoreMetadataByte metadata offset typeId byte = some sourceResult)
    (htarget : typedStoreMetadataByte (renameMetadata resolve id metadata) offset typeId
      (renameByte resolve byte) = some targetResult)
    (hguard : (targetResult.1 == renameMetadata resolve id sourceResult.1 &&
      targetResult.2 == sourceResult.2) = false) :
    pairedTypedStoreMetadataByte resolve id metadata offset typeId byte = none := by
  have hguard' :
      (targetResult.1 == renameMetadata resolve id sourceResult.1 &&
        targetResult.2 == sourceResult.2) ≠ true := by
    intro htrue
    rw [htrue] at hguard
    simp at hguard
  simp [pairedTypedStoreMetadataByte, hsource, htarget]
  grind

theorem pairedTypedStoreMetadataByte_footprints
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedTypedStoreMetadataByte resolve id metadata offset typeId byte =
      some result) :
    result.1.2 = footprint .write { allocation := 0, offset := offset, width := 1 } ∧
      result.2.2 = footprint .write { allocation := 0, offset := offset, width := 1 } := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := hresult.2
          rcases hpair with rfl
          exact ⟨typedStoreMetadataByte_footprint _ _ _ _ _ hs,
            typedStoreMetadataByte_footprint _ _ _ _ _ ht⟩

theorem pairedTypedStoreMetadataByte_correspondence
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedTypedStoreMetadataByte resolve id metadata offset typeId byte =
      some result) :
    (result.2.1 == renameMetadata resolve id result.1.1) = true ∧
      (result.2.2 == result.1.2) = true := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := hresult.2
          rcases hpair with rfl
          exact ⟨hresult.1.1, hresult.1.2⟩

theorem pairedTypedStoreMetadataByte_preserves_lengths
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedTypedStoreMetadataByte resolve id metadata offset typeId byte =
      some result) :
    result.1.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
      result.1.1.locations.length = metadata.locations.length ∧
      result.2.1.allocation.bytes.length =
        (renameMetadata resolve id metadata).allocation.bytes.length ∧
      result.2.1.locations.length =
        (renameMetadata resolve id metadata).locations.length := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := hresult.2
          rcases hpair with rfl
          exact ⟨typedStoreMetadataByte_preserves_byte_length _ _ _ _ _ hs,
            typedStoreMetadataByte_preserves_length _ _ _ _ _ hs,
            typedStoreMetadataByte_preserves_byte_length _ _ _ _ _ ht,
            typedStoreMetadataByte_preserves_length _ _ _ _ _ ht⟩

theorem pairedTypedStoreMetadataByte_preserves_payload
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedTypedStoreMetadataByte resolve id metadata offset typeId byte =
      some result) :
    result.1.1.allocation.live = metadata.allocation.live ∧
      result.1.1.allocation.address = metadata.allocation.address ∧
      result.1.1.allocation.state = metadata.allocation.state ∧
      result.2.1.allocation.live =
        (renameMetadata resolve id metadata).allocation.live ∧
      result.2.1.allocation.address =
        (renameMetadata resolve id metadata).allocation.address ∧
      result.2.1.allocation.state =
        (renameMetadata resolve id metadata).allocation.state := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := hresult.2
          rcases hpair with rfl
          obtain ⟨hslive, hsaddress, hsstate⟩ :=
            typedStoreMetadataByte_preserves_payload _ _ _ _ _ hs
          obtain ⟨htlive, htaddress, htstate⟩ :=
            typedStoreMetadataByte_preserves_payload _ _ _ _ _ ht
          exact ⟨hslive, hsaddress, hsstate, htlive, htaddress, htstate⟩

theorem pairedTypedStoreMetadataByte_preserves_wellFormed
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedTypedStoreMetadataByte resolve id metadata offset typeId byte =
      some result)
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hbytesTarget : bytesWf 0 (listSet
      (renameMetadata resolve id metadata).allocation.bytes offset
      (renameByte resolve byte)))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length)
    (hlocationsTarget :
      (renameMetadata resolve id metadata).locations.length =
        (renameMetadata resolve id metadata).allocation.bytes.length) :
    result.1.1.wellFormed 0 ∧ result.2.1.wellFormed 0 := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedStoreMetadataByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := hresult.2
          rcases hpair with rfl
          exact ⟨typedStoreMetadataByte_preserves_wellFormed _ _ _ _ _ hs
              hbytes hlocations,
            typedStoreMetadataByte_preserves_wellFormed _ _ _ _ _ ht
              hbytesTarget hlocationsTarget⟩

def typedLoadMetadataByte [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) : Option (Byte Tag × Footprint) := do
  let byte ← metadata.allocation.bytes[offset]?
  let location ← metadata.locations[offset]?
  match location.effectiveType with
  | .typed storedType =>
      if storedType == typeId then
        some (byte, footprint .read { allocation := 0, offset := offset, width := 1 })
      else none
  | .untyped => none
  | .padding | .indeterminate => none

theorem typedLoadMetadataByte_empty_none
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (hbytes : metadata.allocation.bytes = []) :
    typedLoadMetadataByte metadata offset typeId = none := by
  simp [typedLoadMetadataByte, hbytes]

theorem typedLoadMetadataByte_outOfBounds
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId)
    (hbyte : metadata.allocation.bytes[offset]? = none) :
    typedLoadMetadataByte metadata offset typeId = none := by
  simp [typedLoadMetadataByte, hbyte]

theorem typedLoadMetadataByte_untyped_refusal
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .untyped, initialized := true }) :
    typedLoadMetadataByte metadata offset typeId = none := by
  simp [typedLoadMetadataByte, hbyte, hlocation]

theorem typedLoadMetadataByte_padding_refusal
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .padding, initialized := true }) :
    typedLoadMetadataByte metadata offset typeId = none := by
  simp [typedLoadMetadataByte, hbyte, hlocation]

theorem typedLoadMetadataByte_indeterminate_refusal
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .indeterminate, initialized := false }) :
    typedLoadMetadataByte metadata offset typeId = none := by
  simp [typedLoadMetadataByte, hbyte, hlocation]

theorem typedLoadMetadataByte_type_mismatch_refusal
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId storedType : TypeId) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .typed storedType, initialized := true })
    (hmismatch : (storedType == typeId) = false) :
    typedLoadMetadataByte metadata offset typeId = none := by
  simp [typedLoadMetadataByte, hbyte, hlocation, hmismatch]

theorem typedLoadMetadataByte_failure_contract
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) :
    typedLoadMetadataByte metadata offset typeId = none ↔
      metadata.allocation.bytes[offset]? = none ∨
      metadata.locations[offset]? = none ∨
      (∃ byte location,
        metadata.allocation.bytes[offset]? = some byte ∧
        metadata.locations[offset]? = some location ∧
        match location.effectiveType with
        | .typed storedType => (storedType == typeId) = false
        | .untyped | .padding | .indeterminate => True) := by
  constructor
  · intro hnone
    cases hbyte : metadata.allocation.bytes[offset]? with
    | none => exact Or.inl rfl
    | some byte =>
        cases hlocation : metadata.locations[offset]? with
        | none => exact Or.inr (Or.inl rfl)
        | some location =>
            right
            right
            refine ⟨byte, location, rfl, rfl, ?_⟩
            cases heffective : location.effectiveType with
            | typed storedType =>
                cases hmatch : storedType == typeId with
                | false => exact hmatch
                | true => simp [typedLoadMetadataByte, hbyte, hlocation,
                    heffective, hmatch] at hnone
            | untyped => trivial
            | padding => trivial
            | indeterminate => trivial
  · intro hfailure
    rcases hfailure with hbyte | hlocation | ⟨byte, location, hbyte, hlocation, heffective⟩
    · simp [typedLoadMetadataByte, hbyte]
    · simp [typedLoadMetadataByte, hlocation]
    · cases heffective' : location.effectiveType with
      | typed storedType =>
          have hmismatch : (storedType == typeId) = false := by
            simpa [heffective'] using heffective
          simp [typedLoadMetadataByte, hbyte, hlocation, heffective', hmismatch]
      | untyped => simp [typedLoadMetadataByte, hbyte, hlocation, heffective']
      | padding => simp [typedLoadMetadataByte, hbyte, hlocation, heffective']
      | indeterminate => simp [typedLoadMetadataByte, hbyte, hlocation, heffective']

def pairedTypedLoadMetadataByte [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) :
    Option ((Byte Tag × Footprint) × (Byte Tag × Footprint)) := do
  let sourceResult ← typedLoadMetadataByte metadata offset typeId
  let targetResult ← typedLoadMetadataByte (renameMetadata resolve id metadata)
    offset typeId
  if targetResult.1 == renameByte resolve sourceResult.1 &&
      targetResult.2 == sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedTypedLoadMetadataByte_empty_none
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (hbytes : metadata.allocation.bytes = []) :
    pairedTypedLoadMetadataByte resolve id metadata offset typeId = none := by
  simp [pairedTypedLoadMetadataByte, typedLoadMetadataByte,
    renameMetadata, hbytes]

theorem pairedTypedLoadMetadataByte_decompose
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedTypedLoadMetadataByte resolve id metadata offset typeId =
      some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : typedLoadMetadataByte metadata offset typeId with
  | none => simp [pairedTypedLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedLoadMetadataByte (renameMetadata resolve id metadata)
          offset typeId with
      | none => simp [pairedTypedLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedLoadMetadataByte, hs, ht] at hresult
          exact ⟨sourceResult, targetResult, hresult.2.symm⟩

theorem pairedTypedLoadMetadataByte_sound
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedTypedLoadMetadataByte resolve id metadata offset typeId =
      some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      typedLoadMetadataByte metadata offset typeId = some sourceResult ∧
      typedLoadMetadataByte (renameMetadata resolve id metadata) offset typeId = some targetResult ∧
      (targetResult.1 == renameByte resolve sourceResult.1) = true ∧
      (targetResult.2 == sourceResult.2) = true := by
  cases hs : typedLoadMetadataByte metadata offset typeId with
  | none => simp [pairedTypedLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedLoadMetadataByte (renameMetadata resolve id metadata)
          offset typeId with
      | none => simp [pairedTypedLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedLoadMetadataByte, hs, ht] at hresult
          rcases hresult with ⟨hcondition, hpair⟩
          exact ⟨sourceResult, targetResult, hpair.symm,
            by simpa using hs, by simpa using ht,
            hcondition.1, hcondition.2⟩

theorem pairedTypedLoadMetadataByte_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (hrefusal : typedLoadMetadataByte metadata offset typeId = none ∨
      typedLoadMetadataByte (renameMetadata resolve id metadata) offset typeId = none) :
    pairedTypedLoadMetadataByte resolve id metadata offset typeId = none := by
  cases hrefusal with
  | inl hsource => simp [pairedTypedLoadMetadataByte, hsource]
  | inr htarget => simp [pairedTypedLoadMetadataByte, htarget]

theorem pairedTypedLoadMetadataByte_refusal_source
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (hsource : typedLoadMetadataByte metadata offset typeId = none) :
    pairedTypedLoadMetadataByte resolve id metadata offset typeId = none := by
  simp [pairedTypedLoadMetadataByte, hsource]

theorem pairedTypedLoadMetadataByte_refusal_target
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (htarget : typedLoadMetadataByte (renameMetadata resolve id metadata)
      offset typeId = none) :
    pairedTypedLoadMetadataByte resolve id metadata offset typeId = none := by
  simp [pairedTypedLoadMetadataByte, htarget]

theorem pairedTypedLoadMetadataByte_failure_contract
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) :
    pairedTypedLoadMetadataByte resolve id metadata offset typeId = none ↔
      typedLoadMetadataByte metadata offset typeId = none ∨
      typedLoadMetadataByte (renameMetadata resolve id metadata) offset typeId = none ∨
      (∃ sourceResult targetResult,
        typedLoadMetadataByte metadata offset typeId = some sourceResult ∧
        typedLoadMetadataByte (renameMetadata resolve id metadata) offset typeId = some targetResult ∧
        ((targetResult.1 == renameByte resolve sourceResult.1) = false ∨
          (targetResult.2 == sourceResult.2) = false)) := by
  constructor
  · intro hnone
    cases hs : typedLoadMetadataByte metadata offset typeId with
    | none => exact Or.inl rfl
    | some sourceResult =>
        cases ht : typedLoadMetadataByte (renameMetadata resolve id metadata)
            offset typeId with
        | none => exact Or.inr (Or.inl rfl)
        | some targetResult =>
            by_cases hbyte : (targetResult.1 == renameByte resolve sourceResult.1) = false
            · exact Or.inr (Or.inr ⟨sourceResult, targetResult, by simpa using hs,
                by simpa using ht, Or.inl hbyte⟩)
            · by_cases hfootprint : (targetResult.2 == sourceResult.2) = false
              · exact Or.inr (Or.inr ⟨sourceResult, targetResult, by simpa using hs,
                  by simpa using ht, Or.inr hfootprint⟩)
              · simp [pairedTypedLoadMetadataByte, hs, ht, hbyte, hfootprint] at hnone
  · rintro (hsource | htarget | hguard)
    · simp [pairedTypedLoadMetadataByte, hsource]
    · simp [pairedTypedLoadMetadataByte, htarget]
    · rcases hguard with ⟨sourceResult, targetResult, hsource, htarget, hcondition⟩
      rcases hcondition with hbyte | hfootprint
      · simp [pairedTypedLoadMetadataByte, hsource, htarget, hbyte]
      · simp [pairedTypedLoadMetadataByte, hsource, htarget, hfootprint]

theorem typedLoadMetadataByte_success
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag) (location : LocationState TypeId)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some location)
    (htype : location.effectiveType = .typed typeId)
    (hsame : (typeId == typeId) = true) :
    typedLoadMetadataByte metadata offset typeId =
      some (byte, footprint .read { allocation := 0, offset := offset, width := 1 }) := by
  simp [typedLoadMetadataByte, hbyte, hlocation, htype, hsame]

theorem typedLoadMetadataByte_footprint
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (result : Byte Tag × Footprint)
    (hresult : typedLoadMetadataByte metadata offset typeId = some result) :
    result.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hbyte : metadata.allocation.bytes[offset]? with
  | none => simp [typedLoadMetadataByte, hbyte] at hresult
  | some byte =>
      cases hlocation : metadata.locations[offset]? with
      | none => simp [typedLoadMetadataByte, hbyte, hlocation] at hresult
      | some location =>
          cases htype : location.effectiveType with
          | typed storedType =>
              by_cases hsame : storedType == typeId
              · simp [typedLoadMetadataByte, hbyte, hlocation, htype, hsame] at hresult
                exact congrArg (fun pair => pair.2) hresult.symm
              · simp [typedLoadMetadataByte, hbyte, hlocation, htype, hsame] at hresult
          | untyped => simp [typedLoadMetadataByte, hbyte, hlocation, htype] at hresult
          | padding => simp [typedLoadMetadataByte, hbyte, hlocation, htype] at hresult
          | indeterminate => simp [typedLoadMetadataByte, hbyte, hlocation, htype] at hresult

theorem typedLoadMetadataByte_contract
    [BEq TypeId]
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (result : Byte Tag × Footprint)
    (hresult : typedLoadMetadataByte metadata offset typeId = some result) :
    ∃ (byte : Byte Tag) (location : LocationState TypeId),
      metadata.allocation.bytes[offset]? = some byte ∧
      metadata.locations[offset]? = some location ∧
      (∃ storedType,
        location.effectiveType = .typed storedType ∧
        (storedType == typeId) = true) ∧
      result.1 = byte ∧
      result.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hbyte : metadata.allocation.bytes[offset]? with
  | none => simp [typedLoadMetadataByte, hbyte] at hresult
  | some byte =>
      cases hlocation : metadata.locations[offset]? with
      | none => simp [typedLoadMetadataByte, hbyte, hlocation] at hresult
      | some location =>
          cases htype : location.effectiveType with
          | typed storedType =>
              by_cases hsame : storedType == typeId
              · simp [typedLoadMetadataByte, hbyte, hlocation, htype, hsame] at hresult
                rcases hresult with rfl
                exact ⟨byte, location, rfl, rfl, ⟨storedType, htype, hsame⟩,
                  rfl, rfl⟩
              · simp [typedLoadMetadataByte, hbyte, hlocation, htype, hsame] at hresult
          | untyped => simp [typedLoadMetadataByte, hbyte, hlocation, htype] at hresult
          | padding => simp [typedLoadMetadataByte, hbyte, hlocation, htype] at hresult
          | indeterminate => simp [typedLoadMetadataByte, hbyte, hlocation, htype] at hresult

theorem pairedTypedLoadMetadataByte_footprints
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedTypedLoadMetadataByte resolve id metadata offset typeId =
      some result) :
    result.1.2 = footprint .read { allocation := 0, offset := offset, width := 1 } ∧
      result.2.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hs : typedLoadMetadataByte metadata offset typeId with
  | none => simp [pairedTypedLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedLoadMetadataByte (renameMetadata resolve id metadata)
          offset typeId with
      | none => simp [pairedTypedLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedLoadMetadataByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := hresult.2
          rcases hpair with rfl
          exact ⟨typedLoadMetadataByte_footprint _ _ _ _ hs,
            typedLoadMetadataByte_footprint _ _ _ _ ht⟩

theorem pairedTypedLoadMetadataByte_correspondence
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedTypedLoadMetadataByte resolve id metadata offset typeId =
      some result) :
    (result.2.1 == renameByte resolve result.1.1) = true ∧
      (result.2.2 == result.1.2) = true := by
  cases hs : typedLoadMetadataByte metadata offset typeId with
  | none => simp [pairedTypedLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : typedLoadMetadataByte (renameMetadata resolve id metadata)
          offset typeId with
      | none => simp [pairedTypedLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedTypedLoadMetadataByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := hresult.2
          rcases hpair with rfl
          exact ⟨hresult.1.1, hresult.1.2⟩

theorem pairedTypedLoadMetadataByte_success
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hbyteTarget : (renameMetadata resolve id metadata).allocation.bytes[offset]? =
      some (renameByte resolve byte))
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .typed typeId, initialized := true })
    (hsame : (typeId == typeId) = true)
    (hbyteEq : (renameByte resolve byte == renameByte resolve byte) = true)
    (hfootprintEq :
      (footprint .read { allocation := 0, offset := offset, width := 1 } ==
        footprint .read { allocation := 0, offset := offset, width := 1 }) = true) :
    pairedTypedLoadMetadataByte resolve id metadata offset typeId =
      some ((byte, footprint .read { allocation := 0, offset := offset, width := 1 }),
        (renameByte resolve byte,
          footprint .read { allocation := 0, offset := offset, width := 1 })) := by
  have htargetLocation : (renameMetadata resolve id metadata).locations[offset]? = some
      { effectiveType := .typed typeId, initialized := true } := by
    simpa [renameMetadata] using hlocation
  simp [pairedTypedLoadMetadataByte, typedLoadMetadataByte,
    hbyte, hbyteTarget, hlocation, htargetLocation, hsame, hbyteEq, hfootprintEq]

def pairedTypedStoreLoadMetadataByte [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag) :
    Option (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))) := do
  let sourceStore ← typedStoreMetadataByte metadata offset typeId byte
  let targetStore ← typedStoreMetadataByte (renameMetadata resolve id metadata)
    offset typeId (renameByte resolve byte)
  let sourceLoad ← typedLoadMetadataByte sourceStore.1 offset typeId
  let targetLoad ← typedLoadMetadataByte targetStore.1 offset typeId
  if targetStore.1 == renameMetadata resolve id sourceStore.1 &&
      targetStore.2 == sourceStore.2 &&
      targetLoad.1 == renameByte resolve sourceLoad.1 &&
      targetLoad.2 == sourceLoad.2 then
    some ((sourceStore, sourceLoad), (targetStore, targetLoad))
  else none

theorem pairedTypedStoreLoadMetadataByte_empty_none
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (hbytes : metadata.allocation.bytes = []) :
    pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte = none := by
  simp [pairedTypedStoreLoadMetadataByte, typedStoreMetadataByte,
    typedLoadMetadataByte, renameMetadata, hbytes]

theorem pairedTypedStoreLoadMetadataByte_decompose
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : typedLoadMetadataByte sourceStore.1 offset typeId with
          | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : typedLoadMetadataByte targetStore.1 offset typeId with
              | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  exact ⟨(sourceStore, sourceLoad), (targetStore, targetLoad), hresult.2.symm⟩

theorem pairedTypedStoreLoadMetadataByte_refusal_source_store
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (hsource : typedStoreMetadataByte metadata offset typeId byte = none) :
    pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte = none := by
  simp [pairedTypedStoreLoadMetadataByte, hsource]

theorem pairedTypedStoreLoadMetadataByte_refusal_target_store
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (htarget : typedStoreMetadataByte (renameMetadata resolve id metadata)
      offset typeId (renameByte resolve byte) = none) :
    pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte = none := by
  simp [pairedTypedStoreLoadMetadataByte, htarget]

theorem pairedTypedStoreLoadMetadataByte_refusal_source_load
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (sourceStore : AllocationMetadata Tag State TypeId × Footprint)
    (hstore : typedStoreMetadataByte metadata offset typeId byte = some sourceStore)
    (hload : typedLoadMetadataByte sourceStore.1 offset typeId = none) :
    pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte = none := by
  simp [pairedTypedStoreLoadMetadataByte, hstore, hload]

theorem pairedTypedStoreLoadMetadataByte_refusal_target_load
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (targetStore : AllocationMetadata Tag State TypeId × Footprint)
    (htarget : typedStoreMetadataByte (renameMetadata resolve id metadata)
      offset typeId (renameByte resolve byte) = some targetStore)
    (hload : typedLoadMetadataByte targetStore.1 offset typeId = none) :
    pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte = none := by
  simp [pairedTypedStoreLoadMetadataByte, htarget, hload]

theorem pairedTypedStoreLoadMetadataByte_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (hrefusal :
      typedStoreMetadataByte metadata offset typeId byte = none ∨
      typedStoreMetadataByte (renameMetadata resolve id metadata) offset typeId
        (renameByte resolve byte) = none ∨
      (∃ sourceStore,
        typedStoreMetadataByte metadata offset typeId byte = some sourceStore ∧
        typedLoadMetadataByte sourceStore.1 offset typeId = none) ∨
      (∃ targetStore,
        typedStoreMetadataByte (renameMetadata resolve id metadata) offset typeId
          (renameByte resolve byte) = some targetStore ∧
        typedLoadMetadataByte targetStore.1 offset typeId = none)) :
    pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte = none := by
  rcases hrefusal with hsource | htarget | hsourceLoad | htargetLoad
  · simp [pairedTypedStoreLoadMetadataByte, hsource]
  · simp [pairedTypedStoreLoadMetadataByte, htarget]
  · rcases hsourceLoad with ⟨sourceStore, hstore, hload⟩
    simp [pairedTypedStoreLoadMetadataByte, hstore, hload]
  · rcases htargetLoad with ⟨targetStore, hstore, hload⟩
    simp [pairedTypedStoreLoadMetadataByte, hstore, hload]

theorem pairedTypedStoreLoadMetadataByte_guard_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (sourceStore : AllocationMetadata Tag State TypeId × Footprint)
    (targetStore : AllocationMetadata Tag State TypeId × Footprint)
    (sourceLoad targetLoad : Byte Tag × Footprint)
    (hsource : typedStoreMetadataByte metadata offset typeId byte = some sourceStore)
    (htarget : typedStoreMetadataByte (renameMetadata resolve id metadata) offset typeId
      (renameByte resolve byte) = some targetStore)
    (hsourceLoad : typedLoadMetadataByte sourceStore.1 offset typeId = some sourceLoad)
    (htargetLoad : typedLoadMetadataByte targetStore.1 offset typeId = some targetLoad)
    (hguard : (targetStore.1 == renameMetadata resolve id sourceStore.1 &&
      targetStore.2 == sourceStore.2 &&
      targetLoad.1 == renameByte resolve sourceLoad.1 &&
      targetLoad.2 == sourceLoad.2) = false) :
    pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte = none := by
  have hguard' :
      (targetStore.1 == renameMetadata resolve id sourceStore.1 &&
        targetStore.2 == sourceStore.2 &&
        targetLoad.1 == renameByte resolve sourceLoad.1 &&
        targetLoad.2 == sourceLoad.2) ≠ true := by
    intro htrue
    rw [htrue] at hguard
    simp at hguard
  simp [pairedTypedStoreLoadMetadataByte, hsource, htarget, hsourceLoad,
    htargetLoad]
  grind

theorem pairedTypedStoreLoadMetadataByte_sound
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result) :
    ∃ sourceStore sourceLoad targetStore targetLoad,
      result = ((sourceStore, sourceLoad), (targetStore, targetLoad)) ∧
      typedStoreMetadataByte metadata offset typeId byte = some sourceStore ∧
      typedStoreMetadataByte (renameMetadata resolve id metadata) offset typeId
        (renameByte resolve byte) = some targetStore ∧
      typedLoadMetadataByte sourceStore.1 offset typeId = some sourceLoad ∧
      typedLoadMetadataByte targetStore.1 offset typeId = some targetLoad ∧
      (targetStore.1 == renameMetadata resolve id sourceStore.1) = true ∧
      (targetStore.2 == sourceStore.2) = true ∧
      (targetLoad.1 == renameByte resolve sourceLoad.1) = true ∧
      (targetLoad.2 == sourceLoad.2) = true := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : typedLoadMetadataByte sourceStore.1 offset typeId with
          | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : typedLoadMetadataByte targetStore.1 offset typeId with
              | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  rcases hresult with ⟨hcondition, hpair⟩
                  exact ⟨sourceStore, sourceLoad, targetStore, targetLoad,
                    hpair.symm, by simpa using hs, by simpa using ht,
                    by simpa using hsl, by simpa using htl,
                    hcondition.1.1.1, hcondition.1.1.2,
                    hcondition.1.2, hcondition.2⟩

theorem pairedTypedStoreLoadMetadataByte_footprints
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result) :
    result.1.1.2 = footprint .write { allocation := 0, offset := offset, width := 1 } ∧
      result.1.2.2 = footprint .read { allocation := 0, offset := offset, width := 1 } ∧
      result.2.1.2 = footprint .write { allocation := 0, offset := offset, width := 1 } ∧
      result.2.2.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : typedLoadMetadataByte sourceStore.1 offset typeId with
          | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : typedLoadMetadataByte targetStore.1 offset typeId with
              | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  exact ⟨typedStoreMetadataByte_footprint _ _ _ _ _ hs,
                    typedLoadMetadataByte_footprint _ _ _ _ hsl,
                    typedStoreMetadataByte_footprint _ _ _ _ _ ht,
                    typedLoadMetadataByte_footprint _ _ _ _ htl⟩

theorem pairedTypedStoreLoadMetadataByte_correspondence
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result) :
    (result.2.1.1 == renameMetadata resolve id result.1.1.1) = true ∧
      (result.2.1.2 == result.1.1.2) = true ∧
      (result.2.2.1 == renameByte resolve result.1.2.1) = true ∧
      (result.2.2.2 == result.1.2.2) = true := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : typedLoadMetadataByte sourceStore.1 offset typeId with
          | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : typedLoadMetadataByte targetStore.1 offset typeId with
              | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  exact ⟨hresult.1.1.1.1, hresult.1.1.1.2,
                    hresult.1.1.2, hresult.1.2⟩

theorem pairedTypedStoreLoadMetadataByte_preserves_payload
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result) :
    result.1.1.1.allocation.live = metadata.allocation.live ∧
      result.1.1.1.allocation.address = metadata.allocation.address ∧
      result.1.1.1.allocation.state = metadata.allocation.state ∧
      result.2.1.1.allocation.live =
        (renameMetadata resolve id metadata).allocation.live ∧
      result.2.1.1.allocation.address =
        (renameMetadata resolve id metadata).allocation.address ∧
      result.2.1.1.allocation.state =
        (renameMetadata resolve id metadata).allocation.state := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : typedLoadMetadataByte sourceStore.1 offset typeId with
          | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : typedLoadMetadataByte targetStore.1 offset typeId with
              | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  obtain ⟨hslive, hsaddr, hsstate⟩ :=
                    typedStoreMetadataByte_preserves_payload _ _ _ _ _ hs
                  obtain ⟨htlive, htaddr, htstate⟩ :=
                    typedStoreMetadataByte_preserves_payload _ _ _ _ _ ht
                  exact ⟨hslive, hsaddr, hsstate, htlive, htaddr, htstate⟩

theorem pairedTypedStoreLoadMetadataByte_preserves_lengths
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result) :
    result.1.1.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
      result.1.1.1.locations.length = metadata.locations.length ∧
      result.2.1.1.allocation.bytes.length =
        (renameMetadata resolve id metadata).allocation.bytes.length ∧
      result.2.1.1.locations.length =
        (renameMetadata resolve id metadata).locations.length := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : typedLoadMetadataByte sourceStore.1 offset typeId with
          | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : typedLoadMetadataByte targetStore.1 offset typeId with
              | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  exact ⟨typedStoreMetadataByte_preserves_byte_length _ _ _ _ _ hs,
                    typedStoreMetadataByte_preserves_length _ _ _ _ _ hs,
                    typedStoreMetadataByte_preserves_byte_length _ _ _ _ _ ht,
                    typedStoreMetadataByte_preserves_length _ _ _ _ _ ht⟩

theorem pairedTypedStoreLoadMetadataByte_preserves_wellFormed
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result)
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hbytesTarget : bytesWf 0 (listSet
      (renameMetadata resolve id metadata).allocation.bytes offset
      (renameByte resolve byte)))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length)
    (hlocationsTarget :
      (renameMetadata resolve id metadata).locations.length =
        (renameMetadata resolve id metadata).allocation.bytes.length) :
    result.1.1.1.wellFormed 0 ∧ result.2.1.1.wellFormed 0 := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : typedLoadMetadataByte sourceStore.1 offset typeId with
          | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : typedLoadMetadataByte targetStore.1 offset typeId with
              | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  exact ⟨typedStoreMetadataByte_preserves_wellFormed _ _ _ _ _ hs
                      hbytes hlocations,
                    typedStoreMetadataByte_preserves_wellFormed _ _ _ _ _ ht
                      hbytesTarget hlocationsTarget⟩

theorem pairedTypedStoreLoadMetadataByte_preserves_locations
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result) :
    result.1.1.1.locations = listSet metadata.locations offset
        { effectiveType := .typed typeId, initialized := true } ∧
      result.2.1.1.locations = listSet
        (renameMetadata resolve id metadata).locations offset
        { effectiveType := .typed typeId, initialized := true } := by
  cases hs : typedStoreMetadataByte metadata offset typeId byte with
  | none => simp [pairedTypedStoreLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : typedStoreMetadataByte (renameMetadata resolve id metadata)
          offset typeId (renameByte resolve byte) with
      | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : typedLoadMetadataByte sourceStore.1 offset typeId with
          | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : typedLoadMetadataByte targetStore.1 offset typeId with
              | none => simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedTypedStoreLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  exact ⟨typedStoreMetadataByte_success_shape _ _ _ _ _ hs |>.2.1,
                    typedStoreMetadataByte_success_shape _ _ _ _ _ ht |>.2.1⟩

def unionLoadMetadataByte
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) : Option (Byte Tag × Footprint) := do
  let byte ← metadata.allocation.bytes[offset]?
  let location ← metadata.locations[offset]?
  if !location.initialized then none
  else some (byte, footprint .read { allocation := 0, offset := offset, width := 1 })

theorem unionLoadMetadataByte_failure_contract
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat) :
    unionLoadMetadataByte metadata offset = none ↔
      metadata.allocation.bytes[offset]? = none ∨
      metadata.locations[offset]? = none ∨
      (∃ byte location,
        metadata.allocation.bytes[offset]? = some byte ∧
        metadata.locations[offset]? = some location ∧
        location.initialized = false) := by
  constructor
  · intro hnone
    cases hbyte : metadata.allocation.bytes[offset]? with
    | none => exact Or.inl rfl
    | some byte =>
        cases hlocation : metadata.locations[offset]? with
        | none => exact Or.inr (Or.inl rfl)
        | some location =>
            right
            right
            refine ⟨byte, location, rfl, rfl, ?_⟩
            cases hinitialized : location.initialized with
            | false => exact rfl
            | true => simp [unionLoadMetadataByte, hbyte, hlocation, hinitialized] at hnone
  · intro hfailure
    rcases hfailure with hbyte | hlocation | ⟨byte, location, hbyte, hlocation, hinitialized⟩
    · simp [unionLoadMetadataByte, hbyte]
    · simp [unionLoadMetadataByte, hlocation]
    · simp [unionLoadMetadataByte, hbyte, hlocation, hinitialized]

theorem unionLoadMetadataByte_empty_none
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat)
    (hbytes : metadata.allocation.bytes = []) :
    unionLoadMetadataByte metadata offset = none := by
  simp [unionLoadMetadataByte, hbytes]

def pairedUnionLoadMetadataByte [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat) :
    Option ((Byte Tag × Footprint) × (Byte Tag × Footprint)) := do
  let sourceResult ← unionLoadMetadataByte metadata offset
  let targetResult ← unionLoadMetadataByte (renameMetadata resolve id metadata) offset
  if targetResult.1 == renameByte resolve sourceResult.1 &&
      targetResult.2 == sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedUnionLoadMetadataByte_empty_none
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (hbytes : metadata.allocation.bytes = []) :
    pairedUnionLoadMetadataByte resolve id metadata offset = none := by
  simp [pairedUnionLoadMetadataByte, unionLoadMetadataByte,
    renameMetadata, hbytes]

theorem pairedUnionLoadMetadataByte_decompose
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedUnionLoadMetadataByte resolve id metadata offset = some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : unionLoadMetadataByte metadata offset with
  | none => simp [pairedUnionLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : unionLoadMetadataByte (renameMetadata resolve id metadata) offset with
      | none => simp [pairedUnionLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedUnionLoadMetadataByte, hs, ht] at hresult
          exact ⟨sourceResult, targetResult, hresult.2.symm⟩

theorem pairedUnionLoadMetadataByte_sound
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedUnionLoadMetadataByte resolve id metadata offset = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      unionLoadMetadataByte metadata offset = some sourceResult ∧
      unionLoadMetadataByte (renameMetadata resolve id metadata) offset = some targetResult ∧
      (targetResult.1 == renameByte resolve sourceResult.1) = true ∧
      (targetResult.2 == sourceResult.2) = true := by
  cases hs : unionLoadMetadataByte metadata offset with
  | none => simp [pairedUnionLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : unionLoadMetadataByte (renameMetadata resolve id metadata) offset with
      | none => simp [pairedUnionLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedUnionLoadMetadataByte, hs, ht] at hresult
          rcases hresult with ⟨hcondition, hpair⟩
          exact ⟨sourceResult, targetResult, hpair.symm,
            by simpa using hs, by simpa using ht,
            hcondition.1, hcondition.2⟩

theorem pairedUnionLoadMetadataByte_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat)
    (hrefusal : unionLoadMetadataByte metadata offset = none ∨
      unionLoadMetadataByte (renameMetadata resolve id metadata) offset = none) :
    pairedUnionLoadMetadataByte resolve id metadata offset = none := by
  cases hrefusal with
  | inl hsource => simp [pairedUnionLoadMetadataByte, hsource]
  | inr htarget => simp [pairedUnionLoadMetadataByte, htarget]

theorem pairedUnionLoadMetadataByte_refusal_source
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (hsource : unionLoadMetadataByte metadata offset = none) :
    pairedUnionLoadMetadataByte resolve id metadata offset = none := by
  simp [pairedUnionLoadMetadataByte, hsource]

theorem pairedUnionLoadMetadataByte_refusal_target
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (htarget : unionLoadMetadataByte (renameMetadata resolve id metadata) offset = none) :
    pairedUnionLoadMetadataByte resolve id metadata offset = none := by
  simp [pairedUnionLoadMetadataByte, htarget]

theorem pairedUnionLoadMetadataByte_guard_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (sourceResult targetResult : Byte Tag × Footprint)
    (hsource : unionLoadMetadataByte metadata offset = some sourceResult)
    (htarget : unionLoadMetadataByte (renameMetadata resolve id metadata) offset =
      some targetResult)
    (hguard : (targetResult.1 == renameByte resolve sourceResult.1 &&
      targetResult.2 == sourceResult.2) = false) :
    pairedUnionLoadMetadataByte resolve id metadata offset = none := by
  have hguard' :
      (targetResult.1 == renameByte resolve sourceResult.1 &&
        targetResult.2 == sourceResult.2) ≠ true := by
    intro htrue
    rw [htrue] at hguard
    simp at hguard
  simp [pairedUnionLoadMetadataByte, hsource, htarget]
  grind

theorem unionLoadMetadataByte_success
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (location : LocationState TypeId)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some location)
    (hinitialized : location.initialized = true) :
    unionLoadMetadataByte metadata offset =
      some (byte, footprint .read { allocation := 0, offset := offset, width := 1 }) := by
  simp [unionLoadMetadataByte, hbyte, hlocation, hinitialized]

theorem pairedUnionLoadMetadataByte_success
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (location : LocationState TypeId)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hbyteTarget : (renameMetadata resolve id metadata).allocation.bytes[offset]? =
      some (renameByte resolve byte))
    (hlocation : metadata.locations[offset]? = some location)
    (htargetLocation :
      (renameMetadata resolve id metadata).locations[offset]? = some location)
    (hinitialized : location.initialized = true)
    (hbyteEq : (renameByte resolve byte == renameByte resolve byte) = true)
    (hfootprintEq :
      (footprint .read { allocation := 0, offset := offset, width := 1 } ==
        footprint .read { allocation := 0, offset := offset, width := 1 }) = true) :
    pairedUnionLoadMetadataByte resolve id metadata offset =
      some ((byte, footprint .read { allocation := 0, offset := offset, width := 1 }),
        (renameByte resolve byte,
          footprint .read { allocation := 0, offset := offset, width := 1 })) := by
  simp [pairedUnionLoadMetadataByte, unionLoadMetadataByte,
    hbyte, hbyteTarget, hlocation, htargetLocation, hinitialized,
    hbyteEq, hfootprintEq]

theorem unionLoadMetadataByte_footprint
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (result : Byte Tag × Footprint)
    (hresult : unionLoadMetadataByte metadata offset = some result) :
    result.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hbyte : metadata.allocation.bytes[offset]? with
  | none => simp [unionLoadMetadataByte, hbyte] at hresult
  | some byte =>
      cases hlocation : metadata.locations[offset]? with
      | none => simp [unionLoadMetadataByte, hbyte, hlocation] at hresult
      | some location =>
          cases hinitialized : location.initialized with
          | false => simp [unionLoadMetadataByte, hbyte, hlocation, hinitialized] at hresult
          | true =>
              simp [unionLoadMetadataByte, hbyte, hlocation, hinitialized] at hresult
              exact congrArg (fun pair => pair.2) hresult.symm

theorem unionLoadMetadataByte_contract
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (result : Byte Tag × Footprint)
    (hresult : unionLoadMetadataByte metadata offset = some result) :
    ∃ (byte : Byte Tag) (location : LocationState TypeId),
      metadata.allocation.bytes[offset]? = some byte ∧
      metadata.locations[offset]? = some location ∧
      location.initialized = true ∧
      result.1 = byte ∧
      result.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hbyte : metadata.allocation.bytes[offset]? with
  | none => simp [unionLoadMetadataByte, hbyte] at hresult
  | some byte =>
      cases hlocation : metadata.locations[offset]? with
      | none => simp [unionLoadMetadataByte, hbyte, hlocation] at hresult
      | some location =>
          cases hinitialized : location.initialized with
          | false => simp [unionLoadMetadataByte, hbyte, hlocation, hinitialized] at hresult
          | true =>
              simp [unionLoadMetadataByte, hbyte, hlocation, hinitialized] at hresult
              rcases hresult with rfl
              exact ⟨byte, location, rfl, rfl, hinitialized, rfl, rfl⟩

theorem unionLoadMetadataByte_uninitialized_refusal
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .untyped, initialized := false }) :
    unionLoadMetadataByte metadata offset = none := by
  simp [unionLoadMetadataByte, hbyte, hlocation]

theorem pairedUnionLoadMetadataByte_footprints
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedUnionLoadMetadataByte resolve id metadata offset = some result) :
    result.1.2 = footprint .read { allocation := 0, offset := offset, width := 1 } ∧
      result.2.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hs : unionLoadMetadataByte metadata offset with
  | none => simp [pairedUnionLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : unionLoadMetadataByte (renameMetadata resolve id metadata) offset with
      | none => simp [pairedUnionLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedUnionLoadMetadataByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := hresult.2
          rcases hpair with rfl
          exact ⟨unionLoadMetadataByte_footprint _ _ _ hs,
            unionLoadMetadataByte_footprint _ _ _ ht⟩

def pairedStoreUnionLoadMetadataByte [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) :
    Option (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))) := do
  let sourceStore ← storeMetadataByte metadata offset byte
  let targetStore ← storeMetadataByte (renameMetadata resolve id metadata)
    offset (renameByte resolve byte)
  let sourceLoad ← unionLoadMetadataByte sourceStore.1 offset
  let targetLoad ← unionLoadMetadataByte targetStore.1 offset
  if targetStore.1 == renameMetadata resolve id sourceStore.1 &&
      targetStore.2 == sourceStore.2 &&
      targetLoad.1 == renameByte resolve sourceLoad.1 &&
      targetLoad.2 == sourceLoad.2 then
    some ((sourceStore, sourceLoad), (targetStore, targetLoad))
  else none

theorem pairedStoreUnionLoadMetadataByte_empty_none
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (hbytes : metadata.allocation.bytes = []) :
    pairedStoreUnionLoadMetadataByte resolve id metadata offset byte = none := by
  simp [pairedStoreUnionLoadMetadataByte, storeMetadataByte,
    unionLoadMetadataByte, renameMetadata, hbytes]

theorem pairedStoreUnionLoadMetadataByte_decompose
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedStoreUnionLoadMetadataByte resolve id metadata offset byte =
      some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreUnionLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata) offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : unionLoadMetadataByte sourceStore.1 offset with
          | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : unionLoadMetadataByte targetStore.1 offset with
              | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  exact ⟨(sourceStore, sourceLoad), (targetStore, targetLoad), hresult.2.symm⟩

theorem pairedStoreUnionLoadMetadataByte_sound
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedStoreUnionLoadMetadataByte resolve id metadata offset byte =
      some result) :
    ∃ sourceStore sourceLoad targetStore targetLoad,
      result = ((sourceStore, sourceLoad), (targetStore, targetLoad)) ∧
      storeMetadataByte metadata offset byte = some sourceStore ∧
      storeMetadataByte (renameMetadata resolve id metadata) offset (renameByte resolve byte) =
        some targetStore ∧
      unionLoadMetadataByte sourceStore.1 offset = some sourceLoad ∧
      unionLoadMetadataByte targetStore.1 offset = some targetLoad ∧
      (targetStore.1 == renameMetadata resolve id sourceStore.1) = true ∧
      (targetStore.2 == sourceStore.2) = true ∧
      (targetLoad.1 == renameByte resolve sourceLoad.1) = true ∧
      (targetLoad.2 == sourceLoad.2) = true := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreUnionLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata) offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : unionLoadMetadataByte sourceStore.1 offset with
          | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : unionLoadMetadataByte targetStore.1 offset with
              | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  rcases hresult with ⟨hcondition, hpair⟩
                  exact ⟨sourceStore, sourceLoad, targetStore, targetLoad,
                    hpair.symm, by simpa using hs, by simpa using ht,
                    by simpa using hsl, by simpa using htl,
                    hcondition.1.1.1, hcondition.1.1.2,
                    hcondition.1.2, hcondition.2⟩

theorem pairedStoreUnionLoadMetadataByte_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (hrefusal :
      storeMetadataByte metadata offset byte = none ∨
      storeMetadataByte (renameMetadata resolve id metadata) offset
        (renameByte resolve byte) = none ∨
      (∃ sourceStore,
        storeMetadataByte metadata offset byte = some sourceStore ∧
        unionLoadMetadataByte sourceStore.1 offset = none) ∨
      (∃ targetStore,
        storeMetadataByte (renameMetadata resolve id metadata) offset
          (renameByte resolve byte) = some targetStore ∧
        unionLoadMetadataByte targetStore.1 offset = none)) :
    pairedStoreUnionLoadMetadataByte resolve id metadata offset byte = none := by
  rcases hrefusal with hsource | htarget | hsourceLoad | htargetLoad
  · simp [pairedStoreUnionLoadMetadataByte, hsource]
  · simp [pairedStoreUnionLoadMetadataByte, htarget]
  · rcases hsourceLoad with ⟨sourceStore, hstore, hload⟩
    simp [pairedStoreUnionLoadMetadataByte, hstore, hload]
  · rcases htargetLoad with ⟨targetStore, hstore, hload⟩
    simp [pairedStoreUnionLoadMetadataByte, hstore, hload]

theorem pairedStoreUnionLoadMetadataByte_refusal_source_store
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (hsource : storeMetadataByte metadata offset byte = none) :
    pairedStoreUnionLoadMetadataByte resolve id metadata offset byte = none := by
  simp [pairedStoreUnionLoadMetadataByte, hsource]

theorem pairedStoreUnionLoadMetadataByte_refusal_target_store
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (htarget : storeMetadataByte (renameMetadata resolve id metadata) offset
      (renameByte resolve byte) = none) :
    pairedStoreUnionLoadMetadataByte resolve id metadata offset byte = none := by
  simp [pairedStoreUnionLoadMetadataByte, htarget]

theorem pairedStoreUnionLoadMetadataByte_refusal_source_load
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (sourceStore : AllocationMetadata Tag State TypeId × Footprint)
    (hstore : storeMetadataByte metadata offset byte = some sourceStore)
    (hload : unionLoadMetadataByte sourceStore.1 offset = none) :
    pairedStoreUnionLoadMetadataByte resolve id metadata offset byte = none := by
  simp [pairedStoreUnionLoadMetadataByte, hstore, hload]

theorem pairedStoreUnionLoadMetadataByte_refusal_target_load
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (targetStore : AllocationMetadata Tag State TypeId × Footprint)
    (htarget : storeMetadataByte (renameMetadata resolve id metadata) offset
      (renameByte resolve byte) = some targetStore)
    (hload : unionLoadMetadataByte targetStore.1 offset = none) :
    pairedStoreUnionLoadMetadataByte resolve id metadata offset byte = none := by
  simp [pairedStoreUnionLoadMetadataByte, htarget, hload]

theorem pairedStoreUnionLoadMetadataByte_guard_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (sourceStore targetStore : AllocationMetadata Tag State TypeId × Footprint)
    (sourceLoad targetLoad : Byte Tag × Footprint)
    (hsource : storeMetadataByte metadata offset byte = some sourceStore)
    (htarget : storeMetadataByte (renameMetadata resolve id metadata) offset
      (renameByte resolve byte) = some targetStore)
    (hsourceLoad : unionLoadMetadataByte sourceStore.1 offset = some sourceLoad)
    (htargetLoad : unionLoadMetadataByte targetStore.1 offset = some targetLoad)
    (hguard : (targetStore.1 == renameMetadata resolve id sourceStore.1 &&
      targetStore.2 == sourceStore.2 &&
      targetLoad.1 == renameByte resolve sourceLoad.1 &&
      targetLoad.2 == sourceLoad.2) = false) :
    pairedStoreUnionLoadMetadataByte resolve id metadata offset byte = none := by
  have hguard' :
      (targetStore.1 == renameMetadata resolve id sourceStore.1 &&
        targetStore.2 == sourceStore.2 &&
        targetLoad.1 == renameByte resolve sourceLoad.1 &&
        targetLoad.2 == sourceLoad.2) ≠ true := by
    intro htrue
    rw [htrue] at hguard
    simp at hguard
  simp [pairedStoreUnionLoadMetadataByte, hsource, htarget, hsourceLoad,
    htargetLoad]
  grind

theorem pairedStoreUnionLoadMetadataByte_footprints
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedStoreUnionLoadMetadataByte resolve id metadata offset byte =
      some result) :
    result.1.1.2 = footprint .write { allocation := 0, offset := offset, width := 1 } ∧
      result.1.2.2 = footprint .read { allocation := 0, offset := offset, width := 1 } ∧
      result.2.1.2 = footprint .write { allocation := 0, offset := offset, width := 1 } ∧
      result.2.2.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreUnionLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata)
          offset (renameByte resolve byte) with
      | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : unionLoadMetadataByte sourceStore.1 offset with
          | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : unionLoadMetadataByte targetStore.1 offset with
              | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  exact ⟨(storeMetadataByte_success_shape _ _ _ _ hs).2.2,
                    unionLoadMetadataByte_footprint _ _ _ hsl,
                    (storeMetadataByte_success_shape _ _ _ _ ht).2.2,
                    unionLoadMetadataByte_footprint _ _ _ htl⟩

theorem pairedStoreUnionLoadMetadataByte_preserves_payload
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedStoreUnionLoadMetadataByte resolve id metadata offset byte =
      some result) :
    result.1.1.1.allocation.live = metadata.allocation.live ∧
      result.1.1.1.allocation.address = metadata.allocation.address ∧
      result.1.1.1.allocation.state = metadata.allocation.state ∧
      result.2.1.1.allocation.live =
        (renameMetadata resolve id metadata).allocation.live ∧
      result.2.1.1.allocation.address =
        (renameMetadata resolve id metadata).allocation.address ∧
      result.2.1.1.allocation.state =
        (renameMetadata resolve id metadata).allocation.state := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreUnionLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata)
          offset (renameByte resolve byte) with
      | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : unionLoadMetadataByte sourceStore.1 offset with
          | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : unionLoadMetadataByte targetStore.1 offset with
              | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  have hsource := hs
                  have htarget := ht
                  simp [storeMetadataByte] at hsource htarget
                  rcases hsource with ⟨_, hsourceEq⟩
                  rcases htarget with ⟨_, htargetEq⟩
                  have hslive := congrArg (fun pair => pair.1.allocation.live) hsourceEq
                  have hsaddr := congrArg (fun pair => pair.1.allocation.address) hsourceEq
                  have hsstate := congrArg (fun pair => pair.1.allocation.state) hsourceEq
                  have htlive := congrArg (fun pair => pair.1.allocation.live) htargetEq
                  have htaddr := congrArg (fun pair => pair.1.allocation.address) htargetEq
                  have htstate := congrArg (fun pair => pair.1.allocation.state) htargetEq
                  simpa [storeMetadataByte] using
                    ⟨hslive.symm, hsaddr.symm, hsstate.symm,
                      htlive.symm, htaddr.symm, htstate.symm⟩

theorem pairedStoreUnionLoadMetadataByte_preserves_locations
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedStoreUnionLoadMetadataByte resolve id metadata offset byte =
      some result) :
    result.1.1.1.locations = metadata.locations ∧
      result.2.1.1.locations = (renameMetadata resolve id metadata).locations := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreUnionLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata)
          offset (renameByte resolve byte) with
      | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : unionLoadMetadataByte sourceStore.1 offset with
          | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : unionLoadMetadataByte targetStore.1 offset with
              | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  exact ⟨storeMetadataByte_preserves_locations _ _ _ _ hs,
                    storeMetadataByte_preserves_locations _ _ _ _ ht⟩

theorem pairedStoreUnionLoadMetadataByte_preserves_wellFormed
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) × (Byte Tag × Footprint)))
    (hresult : pairedStoreUnionLoadMetadataByte resolve id metadata offset byte =
      some result)
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hbytesTarget : bytesWf 0 (listSet
      (renameMetadata resolve id metadata).allocation.bytes offset
      (renameByte resolve byte)))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length)
    (hlocationsTarget :
      (renameMetadata resolve id metadata).locations.length =
        (renameMetadata resolve id metadata).allocation.bytes.length) :
    result.1.1.1.wellFormed 0 ∧ result.2.1.1.wellFormed 0 := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreUnionLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata)
          offset (renameByte resolve byte) with
      | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : unionLoadMetadataByte sourceStore.1 offset with
          | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : unionLoadMetadataByte targetStore.1 offset with
              | none => simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreUnionLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult.2
                  rcases hpair with rfl
                  exact ⟨storeMetadataByte_preserves_wellFormed _ _ _ _ hs
                      hbytes hlocations,
                    storeMetadataByte_preserves_wellFormed _ _ _ _ ht
                      hbytesTarget hlocationsTarget⟩

inductive RepresentationChoice where
  | byte (bits : UInt8)
deriving Repr, BEq

def mergeByte (old : Byte Tag) (mask value choice : UInt8) : Byte Tag :=
  let oldBits := match old with
    | .value bits _ _ => bits.toNat
    | .uninitialized => choice.toNat
  let merged := (oldBits &&& Nat.xor mask.toNat 255) ||| (value.toNat &&& mask.toNat)
  match old with
  | .value _ provenance fragment => .value (UInt8.ofNat merged) provenance fragment
  | .uninitialized => .value (UInt8.ofNat merged) none none

def mergeBytes (old : List (Byte Tag)) (values masks choices : List UInt8) :
    Option (List (Byte Tag)) :=
  if old.length != values.length || values.length != masks.length ||
      masks.length != choices.length then none
  else some (List.zipWith (fun oldByte entry =>
    mergeByte oldByte entry.1.1 entry.1.2 entry.2)
    old (List.zipWith (fun value mask => (value, mask)) values masks
      |>.zip choices))

theorem mergeBytes_empty_success {Tag : Type} :
    mergeBytes ([] : List (Byte Tag)) [] [] [] = some [] := by
  rfl

def mergeFootprint (allocation offset width : Nat) : Footprint :=
  footprint .write { allocation := allocation, offset := offset, width := width }

theorem mergeBytes_success
    (old : List (Byte Tag)) (values masks choices : List UInt8)
    (hold : old.length = values.length)
    (hvalues : values.length = masks.length)
    (hmasks : masks.length = choices.length) :
    mergeBytes old values masks choices =
      some (List.zipWith (fun oldByte entry =>
        mergeByte oldByte entry.1.1 entry.1.2 entry.2)
        old (List.zipWith (fun value mask => (value, mask)) values masks
          |>.zip choices)) := by
  simp [mergeBytes, hold, hvalues, hmasks]

theorem mergeBytes_rejects_old_value_mismatch
    (old : List (Byte Tag)) (values masks choices : List UInt8)
    (hmismatch : old.length ≠ values.length) :
    mergeBytes old values masks choices = none := by
  simp [mergeBytes, hmismatch]

theorem mergeBytes_rejects_value_mask_mismatch
    (old : List (Byte Tag)) (values masks choices : List UInt8)
    (hmismatch : values.length ≠ masks.length) :
    mergeBytes old values masks choices = none := by
  simp [mergeBytes, hmismatch]

theorem mergeBytes_rejects_mask_choice_mismatch
    (old : List (Byte Tag)) (values masks choices : List UInt8)
    (hmismatch : masks.length ≠ choices.length) :
    mergeBytes old values masks choices = none := by
  simp [mergeBytes, hmismatch]

theorem mergeBytes_contract
    (old : List (Byte Tag)) (values masks choices : List UInt8)
    (result : List (Byte Tag))
    (hresult : mergeBytes old values masks choices = some result) :
    old.length = values.length ∧
      values.length = masks.length ∧
      masks.length = choices.length ∧
      result = List.zipWith (fun oldByte entry =>
        mergeByte oldByte entry.1.1 entry.1.2 entry.2)
        old (List.zipWith (fun value mask => (value, mask)) values masks
          |>.zip choices) := by
  simp [mergeBytes] at hresult
  rcases hresult with ⟨hconditions, hEq⟩
  exact ⟨hconditions.1.1, hconditions.1.2, hconditions.2, hEq.symm⟩

theorem mergeFootprint_access_count
    (allocation offset width : Nat) :
    (mergeFootprint allocation offset width).accesses.length = 1 := by
  rfl

theorem mergeFootprint_contract
    (allocation offset width : Nat) :
    mergeFootprint allocation offset width =
        footprint .write { allocation := allocation, offset := offset, width := width } ∧
      (mergeFootprint allocation offset width).accesses.length = 1 := by
  exact ⟨rfl, mergeFootprint_access_count allocation offset width⟩

theorem mergeByte_preserves_pointer_fragment
    (pointer : Provenance Tag) (fragment : Nat)
    (bits mask value choice : UInt8) :
    byteProvenance (mergeByte (.value bits (some pointer) (some fragment)) mask value choice) =
      some pointer ∧
    byteFragment (mergeByte (.value bits (some pointer) (some fragment)) mask value choice) =
      some fragment := by
  simp [mergeByte, byteProvenance, byteFragment]

theorem mergeByte_contract
    (old : Byte Tag) (mask value choice : UInt8) :
    match old with
    | .uninitialized =>
        mergeByte old mask value choice =
            .value
              (UInt8.ofNat
                ((choice.toNat &&& Nat.xor mask.toNat 255) |||
                  (value.toNat &&& mask.toNat))) none none ∧
          byteProvenance (mergeByte old mask value choice) = none ∧
          byteFragment (mergeByte old mask value choice) = none
    | .value bits provenance fragment =>
        mergeByte old mask value choice =
            .value
              (UInt8.ofNat
                ((bits.toNat &&& Nat.xor mask.toNat 255) |||
                  (value.toNat &&& mask.toNat))) provenance fragment ∧
          byteProvenance (mergeByte old mask value choice) = provenance ∧
          byteFragment (mergeByte old mask value choice) = fragment := by
  cases old <;> simp [mergeByte, byteProvenance, byteFragment]

def pairedMergeByte [BEq Tag] (resolve : AllocId → Nat) (old : Byte Tag)
    (mask value choice : UInt8) : Option (Byte Tag × Byte Tag) :=
  let source := mergeByte old mask value choice
  let target := mergeByte (renameByte resolve old) mask value choice
  if target == renameByte resolve source then some (source, target) else none

theorem pairedMergeByte_success
    [BEq Tag] (resolve : AllocId → Nat) (old : Byte Tag)
    (mask value choice : UInt8)
    (hguard : (mergeByte (renameByte resolve old) mask value choice ==
      renameByte resolve (mergeByte old mask value choice)) = true) :
    pairedMergeByte resolve old mask value choice =
      some (mergeByte old mask value choice,
        mergeByte (renameByte resolve old) mask value choice) := by
  simp [pairedMergeByte, hguard]

theorem pairedMergeByte_refusal
    [BEq Tag] (resolve : AllocId → Nat) (old : Byte Tag)
    (mask value choice : UInt8)
    (hguard : (mergeByte (renameByte resolve old) mask value choice ==
      renameByte resolve (mergeByte old mask value choice)) = false) :
    pairedMergeByte resolve old mask value choice = none := by
  simp [pairedMergeByte, hguard]

def copySnapshot (source destination : List (Byte Tag)) : Option (List (Byte Tag)) :=
  if source.length == destination.length then some source else none

theorem copySnapshot_empty_success :
    copySnapshot ([] : List (Byte Tag)) [] = some [] := by
  rfl

def pairedCopySnapshot [BEq Tag] (resolve : AllocId → Nat)
    (source destination : List (Byte Tag)) :
    Option ((List (Byte Tag)) × (List (Byte Tag))) := do
  let sourceResult ← copySnapshot source destination
  let targetResult ← copySnapshot (source.map (renameByte resolve))
    (destination.map (renameByte resolve))
  some (sourceResult, targetResult)

theorem pairedCopySnapshot_empty_success
    {Tag : Type} [BEq Tag] (resolve : AllocId → Nat) :
    pairedCopySnapshot (Tag := Tag) resolve ([] : List (Byte Tag)) [] =
      some (([] : List (Byte Tag)), []) := by
  rfl

theorem pairedCopySnapshot_decompose
    [BEq Tag] (resolve : AllocId → Nat)
    (source destination : List (Byte Tag))
    (result : List (Byte Tag) × List (Byte Tag))
    (hresult : pairedCopySnapshot resolve source destination = some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : copySnapshot source destination with
  | none => simp [pairedCopySnapshot, hs] at hresult
  | some sourceResult =>
      cases ht : copySnapshot (source.map (renameByte resolve))
          (destination.map (renameByte resolve)) with
      | none => simp [pairedCopySnapshot, hs, ht] at hresult
      | some targetResult =>
          rw [pairedCopySnapshot, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := by
            simpa only [Option.bind_some] using Option.some.inj hresult
          exact ⟨sourceResult, targetResult, hpair.symm⟩

theorem pairedCopySnapshot_success
    [BEq Tag] (resolve : AllocId → Nat)
    (source destination : List (Byte Tag))
    (hsame : source.length = destination.length) :
    pairedCopySnapshot resolve source destination =
      some (source, source.map (renameByte resolve)) := by
  simp [pairedCopySnapshot, copySnapshot, hsame, List.length_map]

theorem pairedCopySnapshot_refusal
    [BEq Tag] (resolve : AllocId → Nat)
    (source destination : List (Byte Tag))
    (hmismatch : source.length ≠ destination.length) :
    pairedCopySnapshot resolve source destination = none := by
  simp [pairedCopySnapshot, copySnapshot, hmismatch]

theorem pairedCopySnapshot_byte_correspondence [BEq Tag]
    (resolve : AllocId → Nat)
    (source destination : List (Byte Tag))
    (result : List (Byte Tag) × List (Byte Tag))
    (hresult : pairedCopySnapshot resolve source destination = some result) :
    result.2 = result.1.map (renameByte resolve) := by
  cases hs : copySnapshot source destination with
  | none => simp [pairedCopySnapshot, hs] at hresult
  | some sourceResult =>
      cases ht : copySnapshot (source.map (renameByte resolve))
          (destination.map (renameByte resolve)) with
      | none => simp [pairedCopySnapshot, hs, ht] at hresult
      | some targetResult =>
          simp [pairedCopySnapshot, hs, ht] at hresult
          rcases hresult with rfl
          simp [copySnapshot] at hs ht
          rcases hs with ⟨_, rfl⟩
          rcases ht with ⟨_, rfl⟩
          rfl

theorem copySnapshot_preserves_length
    (source destination : List (Byte Tag)) (result : List (Byte Tag))
    (hresult : copySnapshot source destination = some result) :
    result.length = source.length := by
  simp [copySnapshot] at hresult
  rcases hresult with ⟨_, rfl⟩
  rfl

theorem copySnapshot_success
    (source destination : List (Byte Tag))
    (hsame : source.length = destination.length) :
    copySnapshot source destination = some source := by
  simp [copySnapshot, hsame]

theorem copySnapshot_rejects_length_mismatch
    (source destination : List (Byte Tag))
    (hdifferent : source.length ≠ destination.length) :
    copySnapshot source destination = none := by
  simp [copySnapshot, hdifferent]

theorem copySnapshot_contract
    (source destination : List (Byte Tag)) (result : List (Byte Tag))
    (hresult : copySnapshot source destination = some result) :
    source.length = destination.length ∧ result = source := by
  by_cases hsame : source.length == destination.length
  · have hlength : source.length = destination.length := by
      exact beq_iff_eq.mp hsame
    simp [copySnapshot, hsame] at hresult
    exact ⟨hlength, hresult.symm⟩
  · simp [copySnapshot, hsame] at hresult

theorem copySnapshot_failure_contract
    (source destination : List (Byte Tag)) :
    copySnapshot source destination = none ↔
      source.length ≠ destination.length := by
  by_cases hsame : source.length = destination.length
  · simp [copySnapshot, hsame]
  · simp [copySnapshot, hsame]

def copyFootprint (source destination : Region) (width : Nat) : Footprint :=
  { accesses := [(AccessKind.read, { source with width := width }),
                 (AccessKind.write, { destination with width := width })] }

def pairedCopyFootprint (source destination : Region) (width : Nat) : Bool :=
  (copyFootprint source destination width).accesses.length == 2

theorem copyFootprint_access_count
    (source destination : Region) (width : Nat) :
    (copyFootprint source destination width).accesses.length = 2 := by
  rfl

theorem copyFootprint_contract
    (source destination : Region) (width : Nat) :
    copyFootprint source destination width =
        { accesses := [(AccessKind.read, { source with width := width }),
                       (AccessKind.write, { destination with width := width })] } ∧
      (copyFootprint source destination width).accesses.length = 2 := by
  exact ⟨rfl, copyFootprint_access_count source destination width⟩

theorem pairedCopyFootprint_sound (source destination : Region) (width : Nat) :
    pairedCopyFootprint source destination width = true := by
  simp [pairedCopyFootprint, copyFootprint]

theorem pairedCopyFootprint_contract (source destination : Region) (width : Nat) :
    pairedCopyFootprint source destination width = true := by
  exact pairedCopyFootprint_sound source destination width

def regionsOverlap (source destination : Region) (width : Nat) : Bool :=
  source.allocation == destination.allocation &&
    source.offset < destination.offset + width &&
    destination.offset < source.offset + width

theorem regionsOverlap_contract
    (source destination : Region) (width : Nat) :
    regionsOverlap source destination width = true ↔
      source.allocation = destination.allocation ∧
      source.offset < destination.offset + width ∧
      destination.offset < source.offset + width := by
  simp only [regionsOverlap, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨hallocation, hsource⟩, hdestination⟩
    exact ⟨hallocation, decide_eq_true_iff.mp hsource,
      decide_eq_true_iff.mp hdestination⟩
  · rintro ⟨hallocation, hsource, hdestination⟩
    exact ⟨⟨hallocation, decide_eq_true hsource⟩,
      decide_eq_true hdestination⟩

def memcpySnapshot (source destination : Region) (bytes : List (Byte Tag)) :
    Option (List (Byte Tag)) :=
  if regionsOverlap source destination bytes.length then none
  else copySnapshot bytes bytes

theorem memcpySnapshot_empty_success {Tag : Type}
    (source destination : Region)
    (hnonoverlap : regionsOverlap source destination 0 = false) :
    memcpySnapshot (Tag := Tag) source destination [] = some [] := by
  simp [memcpySnapshot, hnonoverlap, copySnapshot]

theorem memcpySnapshot_rejects_overlap
    (source destination : Region) (bytes : List (Byte Tag))
    (hoverlap : regionsOverlap source destination bytes.length = true) :
    memcpySnapshot source destination bytes = none := by
  simp [memcpySnapshot, hoverlap]

theorem memcpySnapshot_success_nonoverlap
    (source destination : Region) (bytes : List (Byte Tag))
    (hnonoverlap : regionsOverlap source destination bytes.length = false) :
    memcpySnapshot source destination bytes = some bytes := by
  simp [memcpySnapshot, hnonoverlap, copySnapshot]

theorem memcpySnapshot_contract
    (source destination : Region) (bytes result : List (Byte Tag))
    (hresult : memcpySnapshot source destination bytes = some result) :
    regionsOverlap source destination bytes.length = false ∧
      result = bytes := by
  by_cases hoverlap : regionsOverlap source destination bytes.length = true
  · simp [memcpySnapshot, hoverlap] at hresult
  · have hnonoverlap : regionsOverlap source destination bytes.length = false := by
      apply Bool.eq_false_iff.mpr
      exact hoverlap
    simp [memcpySnapshot, hnonoverlap, copySnapshot] at hresult
    exact ⟨hnonoverlap, hresult.symm⟩

theorem memcpySnapshot_failure_contract
    (source destination : Region) (bytes : List (Byte Tag)) :
    memcpySnapshot source destination bytes = none ↔
      regionsOverlap source destination bytes.length = true := by
  by_cases hoverlap : regionsOverlap source destination bytes.length = true
  · simp [memcpySnapshot, hoverlap]
  · have hnonoverlap : regionsOverlap source destination bytes.length = false := by
      exact Bool.eq_false_iff.mpr hoverlap
    simp [memcpySnapshot, hoverlap, hnonoverlap, copySnapshot]

def memmoveSnapshot (_source _destination : Region) (bytes : List (Byte Tag)) :
    Option (List (Byte Tag)) := some bytes

theorem memmoveSnapshot_empty_success {Tag : Type}
    (source destination : Region) :
    memmoveSnapshot (Tag := Tag) source destination [] = some [] := by
  rfl

theorem memmoveSnapshot_success
    (source destination : Region) (bytes : List (Byte Tag)) :
    memmoveSnapshot source destination bytes = some bytes := by
  rfl

theorem memmoveSnapshot_preserves_length
    (source destination : Region) (bytes result : List (Byte Tag))
    (hresult : memmoveSnapshot source destination bytes = some result) :
    result.length = bytes.length := by
  simp [memmoveSnapshot] at hresult
  exact congrArg List.length hresult.symm

theorem memmoveSnapshot_contract
    (source destination : Region) (bytes result : List (Byte Tag))
    (hresult : memmoveSnapshot source destination bytes = some result) :
    result = bytes ∧ result.length = bytes.length := by
  simp [memmoveSnapshot] at hresult
  exact ⟨hresult.symm, by simp [hresult]⟩

theorem memmoveSnapshot_failure_contract
    (source destination : Region) (bytes : List (Byte Tag)) :
    memmoveSnapshot source destination bytes = none ↔ False := by
  simp [memmoveSnapshot]

def pairedMemmoveSnapshot [BEq Tag] (resolve : AllocId → Nat)
    (source destination : Region) (bytes : List (Byte Tag)) :
    Option (List (Byte Tag) × List (Byte Tag)) := do
  let sourceResult ← memmoveSnapshot source destination bytes
  let targetResult ← memmoveSnapshot source destination (bytes.map (renameByte resolve))
  some (sourceResult, targetResult)

theorem pairedMemmoveSnapshot_empty_success
    {Tag : Type} [BEq Tag] (resolve : AllocId → Nat)
    (source destination : Region) :
    pairedMemmoveSnapshot (Tag := Tag) resolve source destination [] =
      some (([] : List (Byte Tag)), []) := by
  rfl

theorem pairedMemmoveSnapshot_decompose
    [BEq Tag] (resolve : AllocId → Nat)
    (source destination : Region) (bytes : List (Byte Tag))
    (result : List (Byte Tag) × List (Byte Tag))
    (hresult : pairedMemmoveSnapshot resolve source destination bytes = some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  rw [pairedMemmoveSnapshot, memmoveSnapshot] at hresult
  have hpair : (bytes, bytes.map (renameByte resolve)) = result := by
    simpa only [Option.bind_some] using Option.some.inj hresult
  exact ⟨bytes, bytes.map (renameByte resolve), hpair.symm⟩

theorem pairedMemmoveSnapshot_success [BEq Tag]
    (resolve : AllocId → Nat) (source destination : Region)
    (bytes : List (Byte Tag)) :
    pairedMemmoveSnapshot resolve source destination bytes =
      some (bytes, bytes.map (renameByte resolve)) := by
  simp [pairedMemmoveSnapshot, memmoveSnapshot]

theorem pairedMemmoveSnapshot_preserves_lengths [BEq Tag]
    (resolve : AllocId → Nat) (source destination : Region)
    (bytes : List (Byte Tag)) (result : List (Byte Tag) × List (Byte Tag))
    (hresult : pairedMemmoveSnapshot resolve source destination bytes = some result) :
    result.1.length = bytes.length ∧ result.2.length = bytes.length := by
  simp [pairedMemmoveSnapshot, memmoveSnapshot] at hresult
  rcases hresult with ⟨hResult, rfl⟩
  constructor
  · rfl
  · simp [List.length_map]

theorem pairedMemmoveSnapshot_byte_correspondence [BEq Tag]
    (resolve : AllocId → Nat) (source destination : Region)
    (bytes : List (Byte Tag))
    (result : List (Byte Tag) × List (Byte Tag))
    (hresult : pairedMemmoveSnapshot resolve source destination bytes = some result) :
    result.2 = result.1.map (renameByte resolve) := by
  simp [pairedMemmoveSnapshot, memmoveSnapshot] at hresult
  rcases hresult with ⟨hResult, rfl⟩
  simp

theorem pairedMemmoveSnapshot_failure_contract [BEq Tag]
    (resolve : AllocId → Nat) (source destination : Region)
    (bytes : List (Byte Tag)) :
    pairedMemmoveSnapshot resolve source destination bytes = none ↔ False := by
  simp [pairedMemmoveSnapshot, memmoveSnapshot]

def pairedMemmoveFootprint (source destination : Region) (width : Nat) : Bool :=
  (copyFootprint source destination width).accesses.length == 2

theorem pairedMemmoveFootprint_sound (source destination : Region) (width : Nat) :
    pairedMemmoveFootprint source destination width = true := by
  simp [pairedMemmoveFootprint, copyFootprint]

theorem pairedMemmoveFootprint_contract (source destination : Region) (width : Nat) :
    pairedMemmoveFootprint source destination width = true := by
  exact pairedMemmoveFootprint_sound source destination width

structure AllocationRequest (Tag State : Type) where
  bytes : List (Byte Tag)
  state : State
deriving Repr

def renameAllocationRequest (resolve : AllocId → Nat)
    (request : AllocationRequest Tag State) : AllocationRequest Tag State :=
  { request with bytes := request.bytes.map (renameByte resolve) }

theorem renameAllocationRequest_bytes
    (resolve : AllocId → Nat) (request : AllocationRequest Tag State) :
    (renameAllocationRequest resolve request).bytes =
      request.bytes.map (renameByte resolve) := by
  rfl

theorem renameAllocationRequest_length
    (resolve : AllocId → Nat) (request : AllocationRequest Tag State) :
    (renameAllocationRequest resolve request).bytes.length = request.bytes.length := by
  simp [renameAllocationRequest]

theorem renameAllocationRequest_contract
    (resolve : AllocId → Nat) (request : AllocationRequest Tag State) :
    (renameAllocationRequest resolve request).bytes =
        request.bytes.map (renameByte resolve) ∧
      (renameAllocationRequest resolve request).bytes.length = request.bytes.length ∧
      (renameAllocationRequest resolve request).state = request.state := by
  exact ⟨renameAllocationRequest_bytes resolve request,
    renameAllocationRequest_length resolve request, rfl⟩

theorem renameAllocationRequest_idempotent
    (resolve : AllocId → Nat) (request : AllocationRequest Tag State) :
    renameAllocationRequest resolve (renameAllocationRequest resolve request) =
      renameAllocationRequest resolve request := by
  cases request with
  | mk bytes state =>
      simp [renameAllocationRequest, List.map_map, renameByte_idempotent]

inductive Placement where
  | address (base : Nat)
  | unaddressable
  | fail
deriving Repr, BEq


inductive ReallocOutcome (Tag State TypeId : Type) where
  | failed (old : AllocationMetadata Tag State TypeId)
  | replaced (fresh : AllocationMetadata Tag State TypeId)
deriving Repr

def reallocMetadata (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    Option (ReallocOutcome Tag State TypeId × Footprint) :=
  match placement with
  | .fail => some (.failed old, footprint AccessKind.metadata
      (Region.mk 0 0 old.allocation.bytes.length))
  | .address base =>
      if locations.length != request.bytes.length then none
      else some (.replaced
        { allocation :=
            { live := true,
              address := some base,
              bytes := request.bytes,
              state := request.state },
          locations := locations },
        footprint AccessKind.metadata (Region.mk 0 0 request.bytes.length))
  | .unaddressable =>
      if locations.length != request.bytes.length then none
      else some (.replaced
        { allocation :=
            { live := true, address := none, bytes := request.bytes, state := request.state },
          locations := locations },
        footprint AccessKind.metadata (Region.mk 0 0 request.bytes.length))

theorem reallocMetadata_failure_preserves_length
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (result : ReallocOutcome Tag State TypeId × Footprint)
    (hresult : reallocMetadata old request locations .fail = some result) :
    match result.1 with
    | .failed previous => previous.allocation.bytes.length = old.allocation.bytes.length
    | .replaced _ => False := by
  simp [reallocMetadata] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  rfl

theorem reallocMetadata_failure_shape
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) :
    reallocMetadata old request locations .fail =
      some (.failed old,
        footprint .metadata (Region.mk 0 0 old.allocation.bytes.length)) := by
  rfl

theorem reallocMetadata_empty_failure_shape
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (hbytes : old.allocation.bytes = []) :
    reallocMetadata old request locations .fail =
      some (.failed old, footprint .metadata (Region.mk 0 0 0)) := by
  simp [reallocMetadata, hbytes]

theorem reallocMetadata_address_success
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (base : Nat)
    (hsame : locations.length = request.bytes.length) :
    reallocMetadata old request locations (.address base) =
      some (.replaced
        { allocation :=
            { live := true, address := some base,
              bytes := request.bytes, state := request.state },
          locations := locations },
        footprint .metadata (Region.mk 0 0 request.bytes.length)) := by
  simp [reallocMetadata, hsame]

theorem reallocMetadata_empty_address_success
    (old : AllocationMetadata Tag State TypeId) (state : State) (base : Nat) :
    reallocMetadata old { bytes := [], state := state } [] (.address base) =
      some (.replaced
        { allocation :=
            { live := true, address := some base,
              bytes := [], state := state },
          locations := [] },
        footprint .metadata (Region.mk 0 0 0)) := by
  exact reallocMetadata_address_success old { bytes := [], state := state } [] base rfl

theorem reallocMetadata_unaddressable_success
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (hsame : locations.length = request.bytes.length) :
    reallocMetadata old request locations .unaddressable =
      some (.replaced
        { allocation :=
            { live := true, address := none,
              bytes := request.bytes, state := request.state },
          locations := locations },
        footprint .metadata (Region.mk 0 0 request.bytes.length)) := by
  simp [reallocMetadata, hsame]

theorem reallocMetadata_empty_unaddressable_success
    (old : AllocationMetadata Tag State TypeId) (state : State) :
    reallocMetadata old { bytes := [], state := state } [] .unaddressable =
      some (.replaced
        { allocation :=
            { live := true, address := none,
              bytes := [], state := state },
          locations := [] },
        footprint .metadata (Region.mk 0 0 0)) := by
  exact reallocMetadata_unaddressable_success old
    { bytes := [], state := state } [] rfl

theorem reallocMetadata_empty_result_shape
    (old : AllocationMetadata Tag State TypeId)
    (state : State) (placement : Placement)
    (result : ReallocOutcome Tag State TypeId × Footprint)
    (hresult : reallocMetadata old { bytes := [], state := state } [] placement = some result) :
    match placement with
    | .address base =>
        result =
          (.replaced
            { allocation :=
                { live := true, address := some base,
                  bytes := [], state := state },
              locations := [] },
            footprint .metadata (Region.mk 0 0 0))
    | .unaddressable =>
        result =
          (.replaced
            { allocation :=
                { live := true, address := none,
                  bytes := [], state := state },
              locations := [] },
            footprint .metadata (Region.mk 0 0 0))
    | .fail =>
        result = (.failed old,
          footprint .metadata (Region.mk 0 0 old.allocation.bytes.length)) := by
  cases placement with
  | address base =>
      simp [reallocMetadata] at hresult
      exact hresult.symm
  | unaddressable =>
      simp [reallocMetadata] at hresult
      exact hresult.symm
  | fail =>
      simp [reallocMetadata] at hresult
      exact hresult.symm

theorem reallocMetadata_contract
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : ReallocOutcome Tag State TypeId × Footprint)
    (hresult : reallocMetadata old request locations placement = some result) :
    match placement with
    | .fail =>
        result = (.failed old,
          footprint .metadata (Region.mk 0 0 old.allocation.bytes.length))
    | .address base =>
        locations.length = request.bytes.length ∧
          result =
            (.replaced
              { allocation :=
                  { live := true, address := some base,
                    bytes := request.bytes, state := request.state },
                locations := locations },
              footprint .metadata (Region.mk 0 0 request.bytes.length))
    | .unaddressable =>
        locations.length = request.bytes.length ∧
          result =
            (.replaced
              { allocation :=
                  { live := true, address := none,
                    bytes := request.bytes, state := request.state },
                locations := locations },
              footprint .metadata (Region.mk 0 0 request.bytes.length)) := by
  cases placement with
  | fail =>
      simp [reallocMetadata] at hresult
      exact hresult.symm
  | address base =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [reallocMetadata, hsame] at hresult
        exact ⟨hsame, hresult.symm⟩
      · simp [reallocMetadata, hsame] at hresult
  | unaddressable =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [reallocMetadata, hsame] at hresult
        exact ⟨hsame, hresult.symm⟩
      · simp [reallocMetadata, hsame] at hresult

theorem reallocMetadata_address_rejects_length_mismatch
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (base : Nat)
    (hmismatch : locations.length ≠ request.bytes.length) :
    reallocMetadata old request locations (.address base) = none := by
  simp [reallocMetadata, hmismatch]

theorem reallocMetadata_unaddressable_rejects_length_mismatch
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (hmismatch : locations.length ≠ request.bytes.length) :
    reallocMetadata old request locations .unaddressable = none := by
  simp [reallocMetadata, hmismatch]

theorem reallocMetadata_failure_contract
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    reallocMetadata old request locations placement = none ↔
      match placement with
      | .fail => False
      | .address _ => locations.length ≠ request.bytes.length
      | .unaddressable => locations.length ≠ request.bytes.length := by
  cases placement with
  | fail => simp [reallocMetadata]
  | address base => simp [reallocMetadata]
  | unaddressable => simp [reallocMetadata]

def pairedReallocMetadata (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    Option ((ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint)) := do
  let sourceResult ← reallocMetadata old request locations placement
  let targetResult ← reallocMetadata (renameMetadata resolve 0 old)
    (renameAllocationRequest resolve request) locations
    (match placement with
    | .address _ => .address (resolve 0)
    | .unaddressable => .unaddressable
    | .fail => .fail)
  some (sourceResult, targetResult)

theorem pairedReallocMetadata_address_success
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (base : Nat)
    (hsame : locations.length = request.bytes.length) :
    pairedReallocMetadata resolve old request locations (.address base) =
      some (
        (.replaced
          { allocation :=
              { live := true, address := some base,
                bytes := request.bytes, state := request.state },
            locations := locations },
          footprint .metadata (Region.mk 0 0 request.bytes.length)),
        (.replaced
          { allocation :=
              { live := true, address := some (resolve 0),
                bytes := (renameAllocationRequest resolve request).bytes,
                state := request.state },
            locations := locations },
          footprint .metadata (Region.mk 0 0 request.bytes.length))) := by
  simp [pairedReallocMetadata, reallocMetadata, hsame, renameAllocationRequest]

theorem pairedReallocMetadata_empty_address_success
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId) (state : State) (base : Nat) :
    pairedReallocMetadata resolve old { bytes := [], state := state } [] (.address base) =
      some (
        (.replaced
          { allocation :=
              { live := true, address := some base,
                bytes := [], state := state },
            locations := [] },
          footprint .metadata (Region.mk 0 0 0)),
        (.replaced
          { allocation :=
              { live := true, address := some (resolve 0),
                bytes := [], state := state },
            locations := [] },
          footprint .metadata (Region.mk 0 0 0))) := by
  simpa [renameAllocationRequest] using
    pairedReallocMetadata_address_success resolve old
      { bytes := [], state := state } [] base rfl

theorem pairedReallocMetadata_unaddressable_success
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (hsame : locations.length = request.bytes.length) :
    pairedReallocMetadata resolve old request locations .unaddressable =
      some (
        (.replaced
          { allocation :=
              { live := true, address := none,
                bytes := request.bytes,
                state := request.state },
            locations := locations },
          footprint .metadata (Region.mk 0 0 request.bytes.length)),
        (.replaced
          { allocation :=
              { live := true, address := none,
                bytes := (renameAllocationRequest resolve request).bytes,
                state := request.state },
            locations := locations },
          footprint .metadata (Region.mk 0 0 request.bytes.length))) := by
  simp [pairedReallocMetadata, reallocMetadata, hsame, renameAllocationRequest]

theorem pairedReallocMetadata_empty_unaddressable_success
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId) (state : State) :
    pairedReallocMetadata resolve old { bytes := [], state := state } [] .unaddressable =
      some (
        (.replaced
          { allocation :=
              { live := true, address := none,
                bytes := [], state := state },
            locations := [] },
          footprint .metadata (Region.mk 0 0 0)),
        (.replaced
          { allocation :=
              { live := true, address := none,
                bytes := [], state := state },
            locations := [] },
          footprint .metadata (Region.mk 0 0 0))) := by
  simpa [renameAllocationRequest] using
    pairedReallocMetadata_unaddressable_success resolve old
      { bytes := [], state := state } [] rfl

theorem pairedReallocMetadata_address_rejects_length_mismatch
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (base : Nat)
    (hmismatch : locations.length ≠ request.bytes.length) :
    pairedReallocMetadata resolve old request locations (.address base) = none := by
  simp [pairedReallocMetadata, reallocMetadata, hmismatch, renameAllocationRequest]

theorem pairedReallocMetadata_unaddressable_rejects_length_mismatch
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (hmismatch : locations.length ≠ request.bytes.length) :
    pairedReallocMetadata resolve old request locations .unaddressable = none := by
  simp [pairedReallocMetadata, reallocMetadata, hmismatch, renameAllocationRequest]

theorem pairedReallocMetadata_failure_shape
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations .fail = some result) :
    result.1.1 = .failed old ∧
      result.2.1 = .failed (renameMetadata resolve 0 old) ∧
      result.1.2 = footprint .metadata (Region.mk 0 0 old.allocation.bytes.length) ∧
      result.2.2 = footprint .metadata
        (Region.mk 0 0 (renameMetadata resolve 0 old).allocation.bytes.length) := by
  simp [pairedReallocMetadata, reallocMetadata] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pairedReallocMetadata_empty_failure_shape
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (hbytes : old.allocation.bytes = []) :
    pairedReallocMetadata resolve old request locations .fail =
      some (
        (.failed old, footprint .metadata (Region.mk 0 0 0)),
        (.failed (renameMetadata resolve 0 old),
          footprint .metadata (Region.mk 0 0 0))) := by
  simp [pairedReallocMetadata, reallocMetadata, renameMetadata, hbytes]

theorem pairedReallocMetadata_decompose
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations placement = some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases placement with
  | address base =>
      cases hs : reallocMetadata old request locations (.address base) with
      | none => simp [pairedReallocMetadata, hs] at hresult
      | some sourceResult =>
          cases ht : reallocMetadata (renameMetadata resolve 0 old)
              (renameAllocationRequest resolve request) locations
              (.address (resolve 0)) with
          | none => simp [pairedReallocMetadata, hs, ht] at hresult
          | some targetResult =>
              rw [pairedReallocMetadata, hs, ht] at hresult
              have hpair : (sourceResult, targetResult) = result := by
                simpa only [Option.bind_some] using Option.some.inj hresult
              exact ⟨sourceResult, targetResult, hpair.symm⟩

  | unaddressable =>
      cases hs : reallocMetadata old request locations .unaddressable with
      | none => simp [pairedReallocMetadata, hs] at hresult
      | some sourceResult =>
          cases ht : reallocMetadata (renameMetadata resolve 0 old)
              (renameAllocationRequest resolve request) locations
              .unaddressable with
          | none => simp [pairedReallocMetadata, hs, ht] at hresult
          | some targetResult =>
              rw [pairedReallocMetadata, hs, ht] at hresult
              have hpair : (sourceResult, targetResult) = result := by
                simpa only [Option.bind_some] using Option.some.inj hresult
              exact ⟨sourceResult, targetResult, hpair.symm⟩
  | fail =>
      cases hs : reallocMetadata old request locations .fail with
      | none => simp [pairedReallocMetadata, hs] at hresult
      | some sourceResult =>
          cases ht : reallocMetadata (renameMetadata resolve 0 old)
              (renameAllocationRequest resolve request) locations .fail with
          | none => simp [pairedReallocMetadata, hs, ht] at hresult
          | some targetResult =>
              rw [pairedReallocMetadata, hs, ht] at hresult
              have hpair : (sourceResult, targetResult) = result := by
                simpa only [Option.bind_some] using Option.some.inj hresult
              exact ⟨sourceResult, targetResult, hpair.symm⟩

theorem pairedReallocMetadata_sound
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (hresult : pairedReallocMetadata resolve old request locations placement = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      reallocMetadata old request locations placement = some sourceResult ∧
      reallocMetadata (renameMetadata resolve 0 old)
        (renameAllocationRequest resolve request) locations
        (match placement with
        | .address _ => .address (resolve 0)
        | .unaddressable => .unaddressable
        | .fail => .fail) = some targetResult := by
  cases placement with
  | address base =>
      cases hs : reallocMetadata old request locations (.address base) with
      | none => simp [pairedReallocMetadata, hs] at hresult
      | some sourceResult =>
          cases ht : reallocMetadata (renameMetadata resolve 0 old)
              (renameAllocationRequest resolve request) locations
              (.address (resolve 0)) with
          | none => simp [pairedReallocMetadata, hs, ht] at hresult
          | some targetResult =>
              simp [pairedReallocMetadata, hs, ht] at hresult
              exact ⟨sourceResult, targetResult, hresult.symm, by simpa using hs,
                by simpa using ht⟩
  | unaddressable =>
      cases hs : reallocMetadata old request locations .unaddressable with
      | none => simp [pairedReallocMetadata, hs] at hresult
      | some sourceResult =>
          cases ht : reallocMetadata (renameMetadata resolve 0 old)
              (renameAllocationRequest resolve request) locations .unaddressable with
          | none => simp [pairedReallocMetadata, hs, ht] at hresult
          | some targetResult =>
              simp [pairedReallocMetadata, hs, ht] at hresult
              exact ⟨sourceResult, targetResult, hresult.symm, by simpa using hs,
                by simpa using ht⟩
  | fail =>
      cases hs : reallocMetadata old request locations .fail with
      | none => simp [pairedReallocMetadata, hs] at hresult
      | some sourceResult =>
          cases ht : reallocMetadata (renameMetadata resolve 0 old)
              (renameAllocationRequest resolve request) locations .fail with
          | none => simp [pairedReallocMetadata, hs, ht] at hresult
          | some targetResult =>
              simp [pairedReallocMetadata, hs, ht] at hresult
              exact ⟨sourceResult, targetResult, hresult.symm, by simpa using hs,
                by simpa using ht⟩

theorem pairedReallocMetadata_preserves_wellFormed
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hold : old.wellFormed 0)
    (hbytes : bytesWf 0 request.bytes)
    (hlocations : locations.length = request.bytes.length)
    (hresult : pairedReallocMetadata resolve old request locations placement = some result) :
    (match result.1.1 with
    | .failed previous => previous.wellFormed 0
    | .replaced fresh => fresh.wellFormed 0) ∧
    (match result.2.1 with
    | .failed previous => previous.wellFormed 0
    | .replaced fresh => fresh.wellFormed 0) := by
  have renameBytesWf : ∀ (id : AllocId) (bytes : List (Byte Tag)),
      bytesWf id bytes → bytesWf id (bytes.map (renameByte resolve)) := by
    intro id bytes h
    induction bytes with
    | nil => simp [bytesWf]
    | cons byte rest ih =>
        cases byte with
        | uninitialized =>
            simp [bytesWf] at h ⊢
            exact ih h
        | value bits provenance fragment =>
            cases provenance with
            | none =>
                simp [bytesWf, renameByte] at h ⊢
                exact ih h
            | some provenance =>
                cases fragment with
                | none =>
                    simp [bytesWf, renameByte] at h ⊢
                    exact And.intro h.1 (ih h.2)
                | some fragment =>
                    simp [bytesWf, renameByte] at h ⊢
                    exact And.intro h.1 (ih h.2)
  cases placement with
  | address base =>
      simp [pairedReallocMetadata, reallocMetadata, hlocations,
        renameAllocationRequest] at hresult
      rcases hresult with rfl
      have hbytesTarget : bytesWf 0 (renameAllocationRequest resolve request).bytes := by
        simpa [renameAllocationRequest] using renameBytesWf 0 request.bytes hbytes
      constructor
      · simp [AllocationMetadata.wellFormed]
        exact ⟨hbytes, hlocations⟩
      · simp only [AllocationMetadata.wellFormed]
        exact ⟨hbytesTarget, by simpa [renameAllocationRequest] using hlocations⟩
  | unaddressable =>
      simp [pairedReallocMetadata, reallocMetadata, hlocations,
        renameAllocationRequest] at hresult
      rcases hresult with rfl
      have hbytesTarget : bytesWf 0 (renameAllocationRequest resolve request).bytes := by
        simpa [renameAllocationRequest] using renameBytesWf 0 request.bytes hbytes
      constructor
      · simp [AllocationMetadata.wellFormed]
        exact ⟨hbytes, hlocations⟩
      · simp only [AllocationMetadata.wellFormed]
        exact ⟨hbytesTarget, by simpa [renameAllocationRequest] using hlocations⟩
  | fail =>
      simp [pairedReallocMetadata, reallocMetadata] at hresult
      rcases hresult with rfl
      have htarget : (renameMetadata resolve 0 old).wellFormed 0 := by
        unfold AllocationMetadata.wellFormed at hold ⊢
        exact ⟨renameBytesWf 0 old.allocation.bytes hold.1,
          by simpa [renameMetadata] using hold.2⟩
      exact ⟨hold, htarget⟩

theorem pairedReallocMetadata_empty_result_wellFormed
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (state : State) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hold : old.wellFormed 0)
    (hresult : pairedReallocMetadata resolve old { bytes := [], state := state }
      [] placement = some result) :
    (match result.1.1 with
    | .failed previous => previous.wellFormed 0
    | .replaced fresh => fresh.wellFormed 0) ∧
    (match result.2.1 with
    | .failed previous => previous.wellFormed 0
    | .replaced fresh => fresh.wellFormed 0) := by
  exact pairedReallocMetadata_preserves_wellFormed resolve old
    { bytes := [], state := state } [] placement result hold
    (by simp [bytesWf]) rfl hresult

theorem pairedReallocMetadata_preserves_lengths
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations placement = some result) :
    (match result.1.1 with
    | .failed previous => previous.allocation.bytes.length = old.allocation.bytes.length
    | .replaced fresh =>
        fresh.allocation.bytes.length = request.bytes.length ∧
          fresh.locations.length = locations.length) ∧
    (match result.2.1 with
    | .failed previous =>
        previous.allocation.bytes.length =
          (renameMetadata resolve 0 old).allocation.bytes.length
    | .replaced fresh =>
        fresh.allocation.bytes.length = (renameAllocationRequest resolve request).bytes.length ∧
          fresh.locations.length = locations.length) := by
  cases placement with
  | address base =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp [renameAllocationRequest]
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | unaddressable =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp [renameAllocationRequest]
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | fail =>
      simp [pairedReallocMetadata, reallocMetadata] at hresult
      rcases hresult with rfl
      simp [renameMetadata]

theorem pairedReallocMetadata_empty_result_lengths
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (state : State) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old { bytes := [], state := state }
      [] placement = some result) :
    (match result.1.1 with
    | .failed previous => previous.allocation.bytes.length = old.allocation.bytes.length
    | .replaced fresh => fresh.allocation.bytes.length = 0 ∧ fresh.locations.length = 0) ∧
    (match result.2.1 with
    | .failed previous =>
        previous.allocation.bytes.length =
          (renameMetadata resolve 0 old).allocation.bytes.length
    | .replaced fresh => fresh.allocation.bytes.length = 0 ∧ fresh.locations.length = 0) := by
  exact pairedReallocMetadata_preserves_lengths resolve old
    { bytes := [], state := state } [] placement result hresult

theorem pairedReallocMetadata_empty_address_result_footprints
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (state : State) (base : Nat)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old { bytes := [], state := state }
      [] (.address base) = some result) :
    result.1.2 = footprint .metadata (Region.mk 0 0 0) ∧
      result.2.2 = footprint .metadata (Region.mk 0 0 0) := by
  simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest] at hresult
  rcases hresult with rfl
  exact ⟨rfl, rfl⟩

theorem pairedReallocMetadata_empty_unaddressable_result_footprints
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (state : State)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old { bytes := [], state := state }
      [] .unaddressable = some result) :
    result.1.2 = footprint .metadata (Region.mk 0 0 0) ∧
      result.2.2 = footprint .metadata (Region.mk 0 0 0) := by
  simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest] at hresult
  rcases hresult with rfl
  exact ⟨rfl, rfl⟩

theorem pairedReallocMetadata_footprints
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations placement = some result) :
    result.1.2 = footprint .metadata
        (Region.mk 0 0 (match result.1.1 with
          | .failed previous => previous.allocation.bytes.length
          | .replaced fresh => fresh.allocation.bytes.length)) ∧
      result.2.2 = footprint .metadata
        (Region.mk 0 0 (match result.2.1 with
          | .failed previous => previous.allocation.bytes.length
          | .replaced fresh => fresh.allocation.bytes.length)) := by
  cases placement with
  | address base =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp [renameAllocationRequest]
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | unaddressable =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp [renameAllocationRequest]
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | fail =>
      simp [pairedReallocMetadata, reallocMetadata] at hresult
      rcases hresult with rfl
      simp [renameMetadata]

theorem pairedReallocMetadata_empty_result_footprints
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (state : State) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old { bytes := [], state := state }
      [] placement = some result) :
    (match result.1.1 with
    | .failed _ => result.1.2 = footprint .metadata
        (Region.mk 0 0 old.allocation.bytes.length)
    | .replaced _ => result.1.2 = footprint .metadata (Region.mk 0 0 0)) ∧
    (match result.2.1 with
    | .failed _ => result.2.2 = footprint .metadata
        (Region.mk 0 0 (renameMetadata resolve 0 old).allocation.bytes.length)
    | .replaced _ => result.2.2 = footprint .metadata (Region.mk 0 0 0)) := by
  cases placement with
  | address base =>
      simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest] at hresult
      rcases hresult with rfl
      simp
  | unaddressable =>
      simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest] at hresult
      rcases hresult with rfl
      simp
  | fail =>
      simp [pairedReallocMetadata, reallocMetadata] at hresult
      rcases hresult with rfl
      simp [renameMetadata]

theorem pairedReallocMetadata_empty_result_shape
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (state : State) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old { bytes := [], state := state }
      [] placement = some result) :
    (match result.1.1 with
    | .failed previous =>
        previous = old ∧ result.1.2 = footprint .metadata
          (Region.mk 0 0 old.allocation.bytes.length)
    | .replaced fresh =>
        fresh.allocation.bytes = [] ∧ fresh.allocation.state = state ∧
          fresh.locations = [] ∧ result.1.2 = footprint .metadata (Region.mk 0 0 0)) ∧
    (match result.2.1 with
    | .failed previous =>
        previous = renameMetadata resolve 0 old ∧ result.2.2 = footprint .metadata
          (Region.mk 0 0 (renameMetadata resolve 0 old).allocation.bytes.length)
    | .replaced fresh =>
        fresh.allocation.bytes = [] ∧ fresh.allocation.state = state ∧
          fresh.locations = [] ∧ result.2.2 = footprint .metadata (Region.mk 0 0 0)) := by
  cases placement with
  | address base =>
      simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest] at hresult
      rcases hresult with rfl
      simp
  | unaddressable =>
      simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest] at hresult
      rcases hresult with rfl
      simp
  | fail =>
      simp [pairedReallocMetadata, reallocMetadata] at hresult
      rcases hresult with rfl
      simp [renameMetadata]

theorem pairedReallocMetadata_preserves_payload
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations placement = some result) :
    (match result.1.1 with
    | .failed previous =>
        previous = old
    | .replaced fresh =>
        fresh.allocation.bytes = request.bytes ∧
          fresh.allocation.state = request.state ∧
          fresh.locations = locations) ∧
    (match result.2.1 with
    | .failed previous =>
        previous = renameMetadata resolve 0 old
    | .replaced fresh =>
        fresh.allocation.bytes = (renameAllocationRequest resolve request).bytes ∧
          fresh.allocation.state = request.state ∧
          fresh.locations = locations) := by
  cases placement with
  | address base =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp [renameAllocationRequest]
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | unaddressable =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp [renameAllocationRequest]
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | fail =>
      simp [pairedReallocMetadata, reallocMetadata] at hresult
      rcases hresult with rfl
      simp

theorem pairedReallocMetadata_empty_result_payload
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (state : State) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old { bytes := [], state := state }
      [] placement = some result) :
    (match result.1.1 with
    | .failed previous => previous = old
    | .replaced fresh =>
        fresh.allocation.bytes = [] ∧ fresh.allocation.state = state ∧
          fresh.locations = []) ∧
    (match result.2.1 with
    | .failed previous => previous = renameMetadata resolve 0 old
    | .replaced fresh =>
        fresh.allocation.bytes = [] ∧ fresh.allocation.state = state ∧
          fresh.locations = []) := by
  exact pairedReallocMetadata_preserves_payload resolve old
    { bytes := [], state := state } [] placement result hresult

theorem pairedReallocMetadata_preserves_liveness
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations placement = some result) :
    (match result.1.1 with
    | .failed previous => previous.allocation.live = old.allocation.live
    | .replaced fresh => fresh.allocation.live = true) ∧
    (match result.2.1 with
    | .failed previous => previous.allocation.live =
        (renameMetadata resolve 0 old).allocation.live
    | .replaced fresh => fresh.allocation.live = true) := by
  cases placement with
  | address base =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | unaddressable =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | fail =>
      simp [pairedReallocMetadata, reallocMetadata] at hresult
      rcases hresult with rfl
      simp

theorem pairedReallocMetadata_empty_result_liveness
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (state : State) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old { bytes := [], state := state }
      [] placement = some result) :
    (match result.1.1 with
    | .failed previous => previous.allocation.live = old.allocation.live
    | .replaced fresh => fresh.allocation.live = true) ∧
    (match result.2.1 with
    | .failed previous => previous.allocation.live =
        (renameMetadata resolve 0 old).allocation.live
    | .replaced fresh => fresh.allocation.live = true) := by
  exact pairedReallocMetadata_preserves_liveness resolve old
    { bytes := [], state := state } [] placement result hresult

theorem pairedReallocMetadata_preserves_locations
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations placement = some result) :
    (match result.1.1 with
    | .failed previous => previous.locations = old.locations
    | .replaced fresh => fresh.locations = locations) ∧
    (match result.2.1 with
    | .failed previous => previous.locations = (renameMetadata resolve 0 old).locations
    | .replaced fresh => fresh.locations = locations) := by
  cases placement with
  | address base =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | unaddressable =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
        rcases hresult with rfl
        simp
      · simp [pairedReallocMetadata, reallocMetadata, renameAllocationRequest, hsame] at hresult
  | fail =>
      simp [pairedReallocMetadata, reallocMetadata] at hresult
      rcases hresult with rfl
      simp

theorem pairedReallocMetadata_empty_result_locations
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (state : State) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old { bytes := [], state := state }
      [] placement = some result) :
    (match result.1.1 with
    | .failed previous => previous.locations = old.locations
    | .replaced fresh => fresh.locations = []) ∧
    (match result.2.1 with
    | .failed previous => previous.locations = (renameMetadata resolve 0 old).locations
    | .replaced fresh => fresh.locations = []) := by
  exact pairedReallocMetadata_preserves_locations resolve old
    { bytes := [], state := state } [] placement result hresult

theorem pairedReallocMetadata_refusal_source
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (hsource : reallocMetadata old request locations placement = none) :
    pairedReallocMetadata resolve old request locations placement = none := by
  simp [pairedReallocMetadata, hsource]

theorem pairedReallocMetadata_refusal_target
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (htarget : reallocMetadata (renameMetadata resolve 0 old)
        (renameAllocationRequest resolve request) locations
        (match placement with
        | .address _ => .address (resolve 0)
        | .unaddressable => .unaddressable
        | .fail => .fail) = none) :
    pairedReallocMetadata resolve old request locations placement = none := by
  simp [pairedReallocMetadata, htarget]

theorem pairedReallocMetadata_refusal
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (hrefusal : reallocMetadata old request locations placement = none ∨
      reallocMetadata (renameMetadata resolve 0 old)
        (renameAllocationRequest resolve request) locations
        (match placement with
        | .address _ => .address (resolve 0)
        | .unaddressable => .unaddressable
        | .fail => .fail) = none) :
    pairedReallocMetadata resolve old request locations placement = none := by
  rcases hrefusal with hsource | htarget
  · simp [pairedReallocMetadata, hsource]
  · simp [pairedReallocMetadata, htarget]

theorem pairedReallocMetadata_failure_contract
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    pairedReallocMetadata resolve old request locations placement = none ↔
      reallocMetadata old request locations placement = none ∨
        reallocMetadata (renameMetadata resolve 0 old)
          (renameAllocationRequest resolve request) locations
          (match placement with
          | .address _ => .address (resolve 0)
          | .unaddressable => .unaddressable
          | .fail => .fail) = none := by
  cases placement with
  | fail =>
      simp [pairedReallocMetadata, reallocMetadata]
  | address base =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, hsame]
      · simp [pairedReallocMetadata, reallocMetadata, hsame]
  | unaddressable =>
      by_cases hsame : locations.length = request.bytes.length
      · simp [pairedReallocMetadata, reallocMetadata, hsame]
      · simp [pairedReallocMetadata, reallocMetadata, hsame]

inductive ZeroSizeOutcome (Tag State TypeId : Type) where
  | null
  | token (metadata : AllocationMetadata Tag State TypeId)
deriving Repr

def allocateZeroSize (state : State) (placement : Placement) :
    ZeroSizeOutcome Tag State TypeId × Footprint :=
  match placement with
  | .fail => (.null, footprint AccessKind.metadata (Region.mk 0 0 0))
  | .address base =>
      (.token { allocation := { live := true, address := some base, bytes := [], state := state }, locations := [] },
       footprint AccessKind.metadata (Region.mk 0 0 0))
  | .unaddressable =>
      (.token { allocation := { live := true, address := none, bytes := [], state := state }, locations := [] },
       footprint AccessKind.metadata (Region.mk 0 0 0))

theorem allocateZeroSize_failure_shape (state : State) :
    allocateZeroSize (Tag := Tag) (TypeId := TypeId) state .fail =
      (.null, footprint .metadata (Region.mk 0 0 0)) := by
  rfl

theorem allocateZeroSize_failure_result (state : State) :
    (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state .fail).1 = .null := by
  rfl

theorem allocateZeroSize_address_shape (state : State) (base : Nat) :
    allocateZeroSize (Tag := Tag) (TypeId := TypeId) state (.address base) =
      (.token { allocation := { live := true, address := some base, bytes := [], state := state }, locations := [] },
        footprint .metadata (Region.mk 0 0 0)) := by
  rfl

theorem allocateZeroSize_unaddressable_shape (state : State) :
    allocateZeroSize (Tag := Tag) (TypeId := TypeId) state .unaddressable =
      (.token { allocation := { live := true, address := none, bytes := [], state := state }, locations := [] },
        footprint .metadata (Region.mk 0 0 0)) := by
  rfl

theorem allocateZeroSize_footprint (state : State) (placement : Placement) :
    (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).2 =
      footprint .metadata (Region.mk 0 0 0) := by
  cases placement <;> rfl

theorem allocateZeroSize_contract
    (state : State) (placement : Placement)
    (result : ZeroSizeOutcome Tag State TypeId × Footprint)
    (hresult : allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement = result) :
    match placement with
    | .fail =>
        result = (.null, footprint .metadata (Region.mk 0 0 0))
    | .address base =>
        result =
          (.token
            { allocation :=
                { live := true, address := some base, bytes := [], state := state },
              locations := [] },
            footprint .metadata (Region.mk 0 0 0))
    | .unaddressable =>
        result =
          (.token
            { allocation :=
                { live := true, address := none, bytes := [], state := state },
              locations := [] },
            footprint .metadata (Region.mk 0 0 0)) := by
  cases placement with
  | fail =>
      simp [allocateZeroSize] at hresult
      exact hresult.symm
  | address base =>
      simp [allocateZeroSize] at hresult
      exact hresult.symm
  | unaddressable =>
      simp [allocateZeroSize] at hresult
      exact hresult.symm

def renameZeroSizeOutcome (resolve : AllocId → Nat) :
    ZeroSizeOutcome Tag State TypeId → ZeroSizeOutcome Tag State TypeId
  | .null => .null
  | .token metadata =>
      .token { metadata with
        allocation := { metadata.allocation with
          address := metadata.allocation.address.map (fun _ => resolve 0) } }

theorem renameZeroSizeOutcome_preserves_failure
    (resolve : AllocId → Nat) :
    renameZeroSizeOutcome (Tag := Tag) (State := State) (TypeId := TypeId)
      resolve (.null) = .null := by
  rfl

theorem renameZeroSizeOutcome_token_shape
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    renameZeroSizeOutcome resolve (.token metadata) =
      .token { metadata with
        allocation := { metadata.allocation with
          address := metadata.allocation.address.map (fun _ => resolve 0) } } := by
  rfl

theorem renameZeroSizeOutcome_token_preserves_wellFormed
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (h : metadata.wellFormed 0) :
    ({ metadata with
        allocation := { metadata.allocation with
          address := metadata.allocation.address.map (fun _ => resolve 0) } }).wellFormed 0 := by
  unfold AllocationMetadata.wellFormed at h ⊢
  exact ⟨h.1, h.2⟩

theorem renameZeroSizeOutcome_token_unaddressable
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (haddress : metadata.allocation.address = none) :
    ∃ renamed,
      renameZeroSizeOutcome resolve (.token metadata) = .token renamed ∧
      renamed.allocation.address = none := by
  refine ⟨{ metadata with
    allocation := { metadata.allocation with
      address := metadata.allocation.address.map (fun _ => resolve 0) } }, rfl, ?_⟩
  simp [haddress]

theorem renameZeroSizeOutcome_token_address
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) (base : Nat)
    (haddress : metadata.allocation.address = some base) :
    ∃ renamed,
      renameZeroSizeOutcome resolve (.token metadata) = .token renamed ∧
      renamed.allocation.address = some (resolve 0) := by
  refine ⟨{ metadata with
    allocation := { metadata.allocation with
      address := metadata.allocation.address.map (fun _ => resolve 0) } }, rfl, ?_⟩
  simp [haddress]

def pairedAllocateZeroSize {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) : Bool :=
  match (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1,
    (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
      (match placement with
      | .address _ => .address (resolve 0)
      | .unaddressable => .unaddressable
      | .fail => .fail)).1 with
  | .null, .null => true
  | .token _, .token _ => true
  | _, _ => false

theorem pairedAllocateZeroSize_agrees
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) :
    pairedAllocateZeroSize (Tag := Tag) (State := State) (TypeId := TypeId)
      resolve state placement = true := by
  cases placement <;> simp [pairedAllocateZeroSize, allocateZeroSize]

theorem pairedAllocateZeroSize_true
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) :
    pairedAllocateZeroSize (Tag := Tag) (State := State) (TypeId := TypeId)
      resolve state placement = true := by
  exact pairedAllocateZeroSize_agrees resolve state placement

theorem pairedAllocateZeroSize_shapes
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) :
    match placement with
    | .fail =>
        (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state .fail).1 = .null ∧
          (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state .fail).1 = .null
    | .address base =>
        (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state (.address base)).1 =
          .token { allocation := { live := true, address := some base, bytes := [], state := state }, locations := [] } ∧
          (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
            (.address (resolve 0))).1 =
          .token { allocation := { live := true, address := some (resolve 0), bytes := [], state := state }, locations := [] }
    | .unaddressable =>
        (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state .unaddressable).1 =
          .token { allocation := { live := true, address := none, bytes := [], state := state }, locations := [] } ∧
          (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state .unaddressable).1 =
          .token { allocation := { live := true, address := none, bytes := [], state := state }, locations := [] } := by
  cases placement <;> simp [allocateZeroSize]

theorem pairedAllocateZeroSize_footprints
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) :
    (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).2 =
        footprint .metadata (Region.mk 0 0 0) ∧
      (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
        (match placement with
        | .address _ => .address (resolve 0)
        | .unaddressable => .unaddressable
        | .fail => .fail)).2 =
        footprint .metadata (Region.mk 0 0 0) := by
  cases placement <;> constructor <;> rfl

theorem pairedAllocateZeroSize_sound
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) :
    (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 = .null ∧
      (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
        (match placement with
        | .address _ => .address (resolve 0)
        | .unaddressable => .unaddressable
        | .fail => .fail)).1 = .null ∨
    (∃ source target,
      (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 = .token source ∧
      (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
        (match placement with
        | .address _ => .address (resolve 0)
        | .unaddressable => .unaddressable
        | .fail => .fail)).1 = .token target) := by
  cases placement <;> simp [allocateZeroSize]

theorem pairedAllocateZeroSize_sound_wellFormed
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) :
    ((allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 = .null ∧
      (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
        (match placement with
        | .address _ => .address (resolve 0)
        | .unaddressable => .unaddressable
        | .fail => .fail)).1 = .null) ∨
    (∃ source target,
      (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 = .token source ∧
      (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
        (match placement with
        | .address _ => .address (resolve 0)
        | .unaddressable => .unaddressable
        | .fail => .fail)).1 = .token target ∧
      source.wellFormed 0 ∧ target.wellFormed 0) := by
  cases placement <;> simp [allocateZeroSize, AllocationMetadata.wellFormed, bytesWf]

theorem pairedAllocateZeroSize_both_null
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement)
    (hsource : (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 = .null)
    (htarget : (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
      (match placement with
      | .address _ => .address (resolve 0)
      | .unaddressable => .unaddressable
      | .fail => .fail)).1 = .null) :
    pairedAllocateZeroSize (Tag := Tag) (State := State) (TypeId := TypeId)
      resolve state placement = true := by
  cases placement <;> simp [pairedAllocateZeroSize, allocateZeroSize]

theorem pairedAllocateZeroSize_both_token
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) (source target : AllocationMetadata Tag State TypeId)
    (hsource : (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 =
      .token source)
    (htarget : (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
      (match placement with
      | .address _ => .address (resolve 0)
      | .unaddressable => .unaddressable
      | .fail => .fail)).1 = .token target) :
    pairedAllocateZeroSize (Tag := Tag) (State := State) (TypeId := TypeId)
      resolve state placement = true := by
  cases placement <;> simp [pairedAllocateZeroSize, allocateZeroSize]

theorem allocateZeroSize_token_wellFormed
    {Tag State TypeId : Type} (state : State) (placement : Placement)
    (metadata : AllocationMetadata Tag State TypeId)
    (hresult : (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 =
      .token metadata) :
    metadata.wellFormed 0 := by
  cases placement with
  | fail => simp [allocateZeroSize] at hresult
  | address base =>
      simp [allocateZeroSize] at hresult
      rcases hresult with rfl
      simp [AllocationMetadata.wellFormed, bytesWf]
  | unaddressable =>
      simp [allocateZeroSize] at hresult
      rcases hresult with rfl
      simp [AllocationMetadata.wellFormed, bytesWf]

theorem pairedAllocateZeroSize_tokens_wellFormed
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) (source target : AllocationMetadata Tag State TypeId)
    (hsource : (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 =
      .token source)
    (htarget : (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
      (match placement with
      | .address _ => .address (resolve 0)
      | .unaddressable => .unaddressable
      | .fail => .fail)).1 = .token target) :
    source.wellFormed 0 ∧ target.wellFormed 0 := by
  cases placement with
  | fail => simp [allocateZeroSize] at hsource htarget
  | address base =>
      simp [allocateZeroSize] at hsource htarget
      rcases hsource with rfl
      rcases htarget with rfl
      simp [AllocationMetadata.wellFormed, bytesWf]
  | unaddressable =>
      simp [allocateZeroSize] at hsource htarget
      rcases hsource with rfl
      rcases htarget with rfl
      simp [AllocationMetadata.wellFormed, bytesWf]

theorem renameZeroSizeOutcome_token_byte_length
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    ∃ renamed,
      renameZeroSizeOutcome resolve (.token metadata) = .token renamed ∧
      renamed.allocation.bytes.length = metadata.allocation.bytes.length := by
  refine ⟨{ metadata with
    allocation := { metadata.allocation with
      address := metadata.allocation.address.map (fun _ => resolve 0) } }, rfl, rfl⟩

inductive ReallocZeroOutcome where
  | freedNull
  | refusedUndefined
deriving Repr, BEq, DecidableEq

def reallocZeroGNU17 : ReallocZeroOutcome := .freedNull

theorem reallocZeroGNU17_shape :
    reallocZeroGNU17 = .freedNull := by
  rfl

theorem reallocZeroGNU17_ne_refusedUndefined :
    reallocZeroGNU17 ≠ .refusedUndefined := by
  simp [reallocZeroGNU17]

def reallocZeroAgrees (source target : ReallocZeroOutcome) : Bool :=
  if source = target then true else false

theorem reallocZeroAgrees_refusal (source target : ReallocZeroOutcome)
    (hneq : source ≠ target) :
    reallocZeroAgrees source target = false := by
  simp [reallocZeroAgrees, hneq]

theorem reallocZeroAgrees_contract (source target : ReallocZeroOutcome) :
    reallocZeroAgrees source target = true ↔ source = target := by
  simp [reallocZeroAgrees]

def pairedReallocZero (_resolve : AllocId → Nat) : Bool :=
  reallocZeroAgrees reallocZeroGNU17 reallocZeroGNU17

theorem pairedReallocZero_sound (resolve : AllocId → Nat) :
    pairedReallocZero resolve := by
  change reallocZeroAgrees reallocZeroGNU17 reallocZeroGNU17 = true
  simp [reallocZeroAgrees]

theorem pairedReallocZero_true (resolve : AllocId → Nat) :
    pairedReallocZero resolve = true := by
  change reallocZeroAgrees reallocZeroGNU17 reallocZeroGNU17 = true
  simp [reallocZeroAgrees]

theorem pairedReallocZero_contract (resolve : AllocId → Nat) :
    pairedReallocZero resolve = true := by
  exact pairedReallocZero_true resolve

def isZeroToken (metadata : AllocationMetadata Tag State TypeId) : Bool :=
  metadata.allocation.live && metadata.allocation.bytes.isEmpty

theorem isZeroToken_contract
    (metadata : AllocationMetadata Tag State TypeId) :
    isZeroToken metadata = true ↔
      metadata.allocation.live = true ∧ metadata.allocation.bytes = [] := by
  simp [isZeroToken]

def zeroTokenEqual (left right : AllocationMetadata Tag State TypeId) : Bool :=
  isZeroToken left && isZeroToken right && left.allocation.address == right.allocation.address

theorem zeroTokenEqual_sound
    (left right : AllocationMetadata Tag State TypeId)
    (h : zeroTokenEqual left right = true) :
    isZeroToken left = true ∧
      isZeroToken right = true ∧
      left.allocation.address = right.allocation.address := by
  simp [zeroTokenEqual, isZeroToken] at h ⊢
  exact ⟨h.1.1, h.1.2, by simpa using h.2⟩

theorem zeroTokenEqual_refusal
    (left right : AllocationMetadata Tag State TypeId)
    (hrefusal : isZeroToken left = false ∨
      isZeroToken right = false ∨
      left.allocation.address ≠ right.allocation.address) :
    zeroTokenEqual left right = false := by
  rcases hrefusal with hleft | hright | haddress
  · simp [zeroTokenEqual, hleft]
  · simp [zeroTokenEqual, hright]
  · simp [zeroTokenEqual, haddress]

theorem zeroTokenEqual_contract
    (left right : AllocationMetadata Tag State TypeId) :
    zeroTokenEqual left right = true ↔
      isZeroToken left = true ∧
      isZeroToken right = true ∧
      left.allocation.address = right.allocation.address := by
  constructor
  · exact zeroTokenEqual_sound left right
  · intro h
    simp [zeroTokenEqual, h.1, h.2.1, h.2.2]

theorem zeroTokenEqual_failure_contract
    (left right : AllocationMetadata Tag State TypeId) :
    zeroTokenEqual left right = false ↔
      isZeroToken left = false ∨
      isZeroToken right = false ∨
      left.allocation.address ≠ right.allocation.address := by
  by_cases hleft : isZeroToken left = true
  · by_cases hright : isZeroToken right = true
    · by_cases haddress : left.allocation.address = right.allocation.address
      · simp [zeroTokenEqual, hleft, hright, haddress]
      · simp [zeroTokenEqual, hleft, hright, haddress]
    · simp [zeroTokenEqual, hleft, hright]
  · simp [zeroTokenEqual, hleft]

def zeroTokenFreeable (metadata : AllocationMetadata Tag State TypeId) : Bool :=
  isZeroToken metadata

theorem zeroTokenFreeable_sound
    (metadata : AllocationMetadata Tag State TypeId)
    (h : zeroTokenFreeable metadata = true) :
    metadata.allocation.live = true ∧
      metadata.allocation.bytes = [] := by
  simpa [zeroTokenFreeable, isZeroToken] using h

theorem zeroTokenFreeable_refusal
    (metadata : AllocationMetadata Tag State TypeId)
    (hrefusal : metadata.allocation.live = false ∨
      metadata.allocation.bytes ≠ []) :
    zeroTokenFreeable metadata = false := by
  rcases hrefusal with hdead | hbytes
  · simp [zeroTokenFreeable, isZeroToken, hdead]
  · cases h : metadata.allocation.live <;>
      simp [zeroTokenFreeable, isZeroToken, h, hbytes]

theorem zeroTokenFreeable_contract
    (metadata : AllocationMetadata Tag State TypeId) :
    zeroTokenFreeable metadata = true ↔
      metadata.allocation.live = true ∧ metadata.allocation.bytes = [] := by
  constructor
  · exact zeroTokenFreeable_sound metadata
  · intro h
    simp [zeroTokenFreeable, isZeroToken, h.1, h.2]

theorem zeroTokenFreeable_failure_contract
    (metadata : AllocationMetadata Tag State TypeId) :
    zeroTokenFreeable metadata = false ↔
      metadata.allocation.live = false ∨ metadata.allocation.bytes ≠ [] := by
  by_cases hlive : metadata.allocation.live = true
  · by_cases hbytes : metadata.allocation.bytes = []
    · simp [zeroTokenFreeable, isZeroToken, hlive, hbytes]
    · simp [zeroTokenFreeable, isZeroToken, hlive, hbytes]
  · have hdead : metadata.allocation.live = false := by
      exact Bool.eq_false_iff.mpr hlive
    simp [zeroTokenFreeable, isZeroToken, hlive, hdead]

def renameZeroTokenMetadata (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    AllocationMetadata Tag State TypeId :=
  { metadata with
    allocation := { metadata.allocation with
      address := metadata.allocation.address.map (fun _ => resolve 0) } }

theorem renameZeroSizeOutcome_contract
    (resolve : AllocId → Nat)
    (outcome : ZeroSizeOutcome Tag State TypeId) :
    renameZeroSizeOutcome resolve outcome =
      match outcome with
      | .null => .null
      | .token metadata => .token (renameZeroTokenMetadata resolve metadata) := by
  cases outcome <;> rfl

theorem renameZeroTokenMetadata_preserves_payload
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameZeroTokenMetadata resolve metadata).allocation.live = metadata.allocation.live ∧
      (renameZeroTokenMetadata resolve metadata).allocation.bytes = metadata.allocation.bytes ∧
      (renameZeroTokenMetadata resolve metadata).allocation.state = metadata.allocation.state ∧
      (renameZeroTokenMetadata resolve metadata).locations = metadata.locations := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem renameZeroTokenMetadata_unaddressable
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (haddress : metadata.allocation.address = none) :
    (renameZeroTokenMetadata resolve metadata).allocation.address = none := by
  simp [renameZeroTokenMetadata, haddress]

theorem renameZeroTokenMetadata_address
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) (base : Nat)
    (haddress : metadata.allocation.address = some base) :
    (renameZeroTokenMetadata resolve metadata).allocation.address = some (resolve 0) := by
  simp [renameZeroTokenMetadata, haddress]

theorem renameZeroTokenMetadata_idempotent
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    renameZeroTokenMetadata resolve (renameZeroTokenMetadata resolve metadata) =
      renameZeroTokenMetadata resolve metadata := by
  cases metadata with
  | mk allocation locations =>
      cases allocation with
      | mk live address bytes state =>
          cases address <;> rfl

theorem renameZeroTokenMetadata_preserves_wellFormed
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (h : metadata.wellFormed 0) :
    (renameZeroTokenMetadata resolve metadata).wellFormed 0 := by
  unfold AllocationMetadata.wellFormed at h ⊢
  exact ⟨by simpa [renameZeroTokenMetadata] using h.1,
    by simpa [renameZeroTokenMetadata] using h.2⟩

theorem renameZeroTokenMetadata_contract
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hmetadata : metadata.wellFormed 0) :
    (renameZeroTokenMetadata resolve metadata).allocation.live =
        metadata.allocation.live ∧
      (renameZeroTokenMetadata resolve metadata).allocation.bytes =
        metadata.allocation.bytes ∧
      (renameZeroTokenMetadata resolve metadata).allocation.state =
        metadata.allocation.state ∧
      (renameZeroTokenMetadata resolve metadata).locations = metadata.locations ∧
      (renameZeroTokenMetadata resolve metadata).allocation.address =
        metadata.allocation.address.map (fun _ => resolve 0) ∧
      renameZeroTokenMetadata resolve (renameZeroTokenMetadata resolve metadata) =
        renameZeroTokenMetadata resolve metadata ∧
      (renameZeroTokenMetadata resolve metadata).wellFormed 0 := by
  rcases renameZeroTokenMetadata_preserves_payload resolve metadata with
    ⟨hlive, hbytes, hstate, hlocations⟩
  exact ⟨hlive, hbytes, hstate, hlocations, rfl,
    renameZeroTokenMetadata_idempotent resolve metadata,
    renameZeroTokenMetadata_preserves_wellFormed resolve metadata hmetadata⟩

theorem renameZeroSizeOutcome_token_contract
    (resolve : AllocId → Nat)
    (outcome : ZeroSizeOutcome Tag State TypeId)
    (hmetadata : ∀ metadata,
      outcome = .token metadata → metadata.wellFormed 0) :
    match outcome with
    | .null => renameZeroSizeOutcome resolve outcome = .null
    | .token metadata =>
        ∃ renamed,
          renameZeroSizeOutcome resolve outcome = .token renamed ∧
          renamed.allocation.bytes.length = metadata.allocation.bytes.length ∧
          renamed.wellFormed 0 := by
  cases outcome with
  | null => rfl
  | token metadata =>
      refine ⟨renameZeroTokenMetadata resolve metadata, rfl, ?_, ?_⟩
      · rfl
      · exact renameZeroTokenMetadata_preserves_wellFormed resolve metadata
          (hmetadata metadata rfl)

def pairedZeroTokenEqual (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId) : Bool :=
  zeroTokenEqual (renameZeroTokenMetadata resolve left)
    (renameZeroTokenMetadata resolve right) ==
    zeroTokenEqual left right

theorem pairedZeroTokenEqual_sound (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId)
    (h : pairedZeroTokenEqual resolve left right) :
    zeroTokenEqual (renameZeroTokenMetadata resolve left)
      (renameZeroTokenMetadata resolve right) = zeroTokenEqual left right := by
  simpa [pairedZeroTokenEqual] using h

theorem pairedZeroTokenEqual_success (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId)
    (heq : zeroTokenEqual (renameZeroTokenMetadata resolve left)
      (renameZeroTokenMetadata resolve right) = zeroTokenEqual left right) :
    pairedZeroTokenEqual resolve left right = true := by
  simp [pairedZeroTokenEqual, heq]

theorem pairedZeroTokenEqual_contract (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId) :
    pairedZeroTokenEqual resolve left right = true ↔
      zeroTokenEqual (renameZeroTokenMetadata resolve left)
        (renameZeroTokenMetadata resolve right) = zeroTokenEqual left right := by
  simp [pairedZeroTokenEqual, beq_iff_eq]

theorem pairedZeroTokenEqual_failure_contract (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId) :
    pairedZeroTokenEqual resolve left right = false ↔
      zeroTokenEqual (renameZeroTokenMetadata resolve left)
        (renameZeroTokenMetadata resolve right) ≠ zeroTokenEqual left right := by
  simp [pairedZeroTokenEqual, beq_iff_eq]

theorem zeroTokenEqual_rename_of_equal (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId)
    (haddress : left.allocation.address = right.allocation.address) :
    zeroTokenEqual (renameZeroTokenMetadata resolve left)
      (renameZeroTokenMetadata resolve right) = zeroTokenEqual left right := by
  simp [zeroTokenEqual, isZeroToken, renameZeroTokenMetadata, haddress]

theorem pairedZeroTokenEqual_true_of_equal_address (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId)
    (haddress : left.allocation.address = right.allocation.address) :
    pairedZeroTokenEqual resolve left right = true := by
  apply pairedZeroTokenEqual_success
  exact zeroTokenEqual_rename_of_equal resolve left right haddress

theorem pairedZeroTokenEqual_refusal (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId)
    (hneq : zeroTokenEqual (renameZeroTokenMetadata resolve left)
      (renameZeroTokenMetadata resolve right) ≠ zeroTokenEqual left right) :
    pairedZeroTokenEqual resolve left right = false := by
  simp [pairedZeroTokenEqual, hneq]

theorem renameZeroTokenMetadata_freeable (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    zeroTokenFreeable (renameZeroTokenMetadata resolve metadata) =
      zeroTokenFreeable metadata := by
  simp [zeroTokenFreeable, isZeroToken, renameZeroTokenMetadata]

def freeMetadata (metadata : AllocationMetadata Tag State TypeId) :
    Option (AllocationMetadata Tag State TypeId × Footprint) :=
  if metadata.allocation.live then
    some ({ metadata with allocation := { metadata.allocation with live := false } },
      footprint AccessKind.metadata (Region.mk 0 0 metadata.allocation.bytes.length))
  else none

theorem freeMetadata_live_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (hlive : metadata.allocation.live = true) :
    freeMetadata metadata =
      some ({ metadata with allocation := { metadata.allocation with live := false } },
        footprint .metadata (Region.mk 0 0 metadata.allocation.bytes.length)) := by
  simp [freeMetadata, hlive]

theorem freeMetadata_empty_live_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (hlive : metadata.allocation.live = true)
    (hbytes : metadata.allocation.bytes = []) :
    freeMetadata metadata =
      some ({ metadata with allocation := { metadata.allocation with live := false } },
        footprint .metadata (Region.mk 0 0 0)) := by
  simp [freeMetadata, hlive, hbytes]

theorem freeMetadata_dead_refusal
    (metadata : AllocationMetadata Tag State TypeId)
    (hdead : metadata.allocation.live = false) :
    freeMetadata metadata = none := by
  simp [freeMetadata, hdead]

theorem freeMetadata_failure_contract
    (metadata : AllocationMetadata Tag State TypeId) :
    freeMetadata metadata = none ↔ metadata.allocation.live = false := by
  cases hlive : metadata.allocation.live <;>
    simp [freeMetadata, hlive]

theorem freeMetadata_preserves_locations
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : freeMetadata metadata = some result) :
    result.1.locations = metadata.locations := by
  cases hlive : metadata.allocation.live with
  | false => simp [freeMetadata, hlive] at hresult
  | true =>
      have hpair := Option.some.inj (by
        simpa [freeMetadata, hlive] using hresult)
      exact (congrArg (fun pair => pair.1.locations) hpair).symm

theorem freeMetadata_marks_dead
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : freeMetadata metadata = some result) :
    result.1.allocation.live = false := by
  cases hlive : metadata.allocation.live with
  | false => simp [freeMetadata, hlive] at hresult
  | true =>
      have hpair := Option.some.inj (by
        simpa [freeMetadata, hlive] using hresult)
      simpa using (congrArg (fun pair => pair.1.allocation.live) hpair).symm

theorem freeMetadata_empty_marks_dead
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hbytes : metadata.allocation.bytes = [])
    (hresult : freeMetadata metadata = some result) :
    result.1.allocation.live = false := by
  exact freeMetadata_marks_dead metadata result hresult

theorem freeMetadata_footprint_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : freeMetadata metadata = some result) :
    result.2 = footprint .metadata
      (Region.mk 0 0 metadata.allocation.bytes.length) := by
  cases hlive : metadata.allocation.live with
  | false => simp [freeMetadata, hlive] at hresult
  | true =>
      have hpair := Option.some.inj (by
        simpa [freeMetadata, hlive] using hresult)
      exact (congrArg (fun pair => pair.2) hpair).symm

theorem freeMetadata_preserves_payload
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : freeMetadata metadata = some result) :
    result.1.allocation.address = metadata.allocation.address ∧
      result.1.allocation.bytes = metadata.allocation.bytes ∧
      result.1.allocation.state = metadata.allocation.state := by
  cases hlive : metadata.allocation.live with
  | false => simp [freeMetadata, hlive] at hresult
  | true =>
      have hpair := Option.some.inj (by
        simpa [freeMetadata, hlive] using hresult)
      have haddress := congrArg (fun pair => pair.1.allocation.address) hpair
      have hbytes := congrArg (fun pair => pair.1.allocation.bytes) hpair
      have hstate := congrArg (fun pair => pair.1.allocation.state) hpair
      exact ⟨haddress.symm, hbytes.symm, hstate.symm⟩

theorem freeMetadata_preserves_wellFormed
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hmetadata : metadata.wellFormed 0)
    (hresult : freeMetadata metadata = some result) :
    result.1.wellFormed 0 := by
  have hlocations := freeMetadata_preserves_locations metadata result hresult
  have hpayload := freeMetadata_preserves_payload metadata result hresult
  unfold AllocationMetadata.wellFormed at hmetadata ⊢
  constructor
  · rw [hpayload.2.1]
    exact hmetadata.1
  · rw [hlocations, hpayload.2.1]
    exact hmetadata.2

theorem freeMetadata_contract
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hmetadata : metadata.wellFormed 0)
    (hresult : freeMetadata metadata = some result) :
    result.1.allocation.live = false ∧
      result.1.locations = metadata.locations ∧
      result.1.allocation.address = metadata.allocation.address ∧
      result.1.allocation.bytes = metadata.allocation.bytes ∧
      result.1.allocation.state = metadata.allocation.state ∧
      result.2 = footprint .metadata
        (Region.mk 0 0 metadata.allocation.bytes.length) ∧
      result.1.wellFormed 0 := by
  exact ⟨freeMetadata_marks_dead metadata result hresult,
    freeMetadata_preserves_locations metadata result hresult,
    (freeMetadata_preserves_payload metadata result hresult).1,
    (freeMetadata_preserves_payload metadata result hresult).2.1,
    (freeMetadata_preserves_payload metadata result hresult).2.2,
    freeMetadata_footprint_shape metadata result hresult,
    freeMetadata_preserves_wellFormed metadata result hmetadata hresult⟩

theorem freeMetadata_empty_preserves_wellFormed
    (metadata : AllocationMetadata Tag State TypeId)
    (hmetadata : metadata.wellFormed 0)
    (hlive : metadata.allocation.live = true)
    (hbytes : metadata.allocation.bytes = []) :
    ∃ result,
      freeMetadata metadata = some result ∧ result.1.wellFormed 0 := by
  refine ⟨({ metadata with allocation := { metadata.allocation with live := false } },
    footprint .metadata (Region.mk 0 0 0)), ?_, ?_⟩
  · simp [freeMetadata, hlive, hbytes]
  · have hloc : metadata.locations.length = 0 := by
      rw [hmetadata.2, hbytes]
      rfl
    have hlocations : metadata.locations = [] := List.eq_nil_of_length_eq_zero hloc
    simp [AllocationMetadata.wellFormed, bytesWf, hbytes, hlocations]

def pairedFreeMetadata (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    Option ((AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint)) := do
  let sourceResult ← freeMetadata metadata
  let targetResult ← freeMetadata (renameZeroTokenMetadata resolve metadata)
  some (sourceResult, targetResult)

theorem pairedFreeMetadata_live_success
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hlive : metadata.allocation.live = true) :
    pairedFreeMetadata resolve metadata =
      some (
        ({ metadata with allocation := { metadata.allocation with live := false } },
          footprint .metadata (Region.mk 0 0 metadata.allocation.bytes.length)),
        ({ renameZeroTokenMetadata resolve metadata with
            allocation :=
              { (renameZeroTokenMetadata resolve metadata).allocation with live := false } },
          footprint .metadata
            (Region.mk 0 0 (renameZeroTokenMetadata resolve metadata).allocation.bytes.length))) := by
  simp [pairedFreeMetadata, freeMetadata, hlive, renameZeroTokenMetadata]

theorem pairedFreeMetadata_empty_live_success
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hlive : metadata.allocation.live = true)
    (hbytes : metadata.allocation.bytes = []) :
    pairedFreeMetadata resolve metadata =
      some (
        ({ metadata with allocation := { metadata.allocation with live := false } },
          footprint .metadata (Region.mk 0 0 0)),
        ({ renameZeroTokenMetadata resolve metadata with
            allocation :=
              { (renameZeroTokenMetadata resolve metadata).allocation with live := false } },
          footprint .metadata (Region.mk 0 0 0))) := by
  simp [pairedFreeMetadata, freeMetadata, hlive, hbytes, renameZeroTokenMetadata]

theorem pairedFreeMetadata_empty_preserves_wellFormed
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hmetadata : metadata.wellFormed 0)
    (hlive : metadata.allocation.live = true)
    (hbytes : metadata.allocation.bytes = []) :
    ∃ result,
      pairedFreeMetadata resolve metadata = some result ∧
      result.1.1.wellFormed 0 ∧ result.2.1.wellFormed 0 := by
  have hsingle : ∃ sourceResult,
      freeMetadata metadata = some sourceResult ∧ sourceResult.1.wellFormed 0 :=
    freeMetadata_empty_preserves_wellFormed metadata hmetadata hlive hbytes
  have htargetMetadata : (renameZeroTokenMetadata resolve metadata).wellFormed 0 := by
    exact renameZeroTokenMetadata_preserves_wellFormed resolve metadata hmetadata
  have htargetLive : (renameZeroTokenMetadata resolve metadata).allocation.live = true := by
    simp [renameZeroTokenMetadata, hlive]
  have htargetBytes : (renameZeroTokenMetadata resolve metadata).allocation.bytes = [] := by
    simp [renameZeroTokenMetadata, hbytes]
  have htarget := freeMetadata_empty_preserves_wellFormed
    (renameZeroTokenMetadata resolve metadata) htargetMetadata htargetLive htargetBytes
  rcases hsingle with ⟨sourceResult, hsource, hsourceWf⟩
  rcases htarget with ⟨targetResult, htarget, htargetWf⟩
  refine ⟨(sourceResult, targetResult), ?_, hsourceWf, htargetWf⟩
  simp [pairedFreeMetadata, hsource, htarget]

theorem pairedFreeMetadata_dead_refusal
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hdead : metadata.allocation.live = false) :
    pairedFreeMetadata resolve metadata = none := by
  simp [pairedFreeMetadata, freeMetadata, hdead, renameZeroTokenMetadata]

theorem pairedFreeMetadata_empty_dead_refusal
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hdead : metadata.allocation.live = false)
    (hbytes : metadata.allocation.bytes = []) :
    pairedFreeMetadata resolve metadata = none := by
  simp [pairedFreeMetadata, freeMetadata, hdead, hbytes, renameZeroTokenMetadata]

theorem pairedFreeMetadata_decompose
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : freeMetadata metadata with
  | none => simp [pairedFreeMetadata, hs] at hresult
  | some sourceResult =>
      cases ht : freeMetadata (renameZeroTokenMetadata resolve metadata) with
      | none => simp [pairedFreeMetadata, hs, ht] at hresult
      | some targetResult =>
          rw [pairedFreeMetadata, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := by
            simpa only [Option.bind_some] using Option.some.inj hresult
          exact ⟨sourceResult, targetResult, hpair.symm⟩

theorem pairedFreeMetadata_sound
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      freeMetadata metadata = some sourceResult ∧
      freeMetadata (renameZeroTokenMetadata resolve metadata) = some targetResult := by
  cases hs : freeMetadata metadata with
  | none => simp [pairedFreeMetadata, hs] at hresult
  | some sourceResult =>
      cases ht : freeMetadata (renameZeroTokenMetadata resolve metadata) with
      | none => simp [pairedFreeMetadata, hs, ht] at hresult
      | some targetResult =>
          simp [pairedFreeMetadata, hs, ht] at hresult
          exact ⟨sourceResult, targetResult, hresult.symm,
            by simpa using hs, by simpa using ht⟩

theorem pairedFreeMetadata_refusal_source
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hsource : freeMetadata metadata = none) :
    pairedFreeMetadata resolve metadata = none := by
  simp [pairedFreeMetadata, hsource]

theorem pairedFreeMetadata_refusal_target
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (htarget : freeMetadata (renameZeroTokenMetadata resolve metadata) = none) :
    pairedFreeMetadata resolve metadata = none := by
  simp [pairedFreeMetadata, htarget]

theorem pairedFreeMetadata_refusal
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hrefusal : freeMetadata metadata = none ∨
      freeMetadata (renameZeroTokenMetadata resolve metadata) = none) :
    pairedFreeMetadata resolve metadata = none := by
  rcases hrefusal with hsource | htarget
  · simp [pairedFreeMetadata, hsource]
  · simp [pairedFreeMetadata, htarget]

theorem pairedFreeMetadata_failure_contract
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    pairedFreeMetadata resolve metadata = none ↔
      freeMetadata metadata = none ∨
        freeMetadata (renameZeroTokenMetadata resolve metadata) = none := by
  cases hlive : metadata.allocation.live with
  | false =>
      simp [pairedFreeMetadata, freeMetadata, hlive, renameZeroTokenMetadata]
  | true =>
      simp [pairedFreeMetadata, freeMetadata, hlive, renameZeroTokenMetadata]

theorem pairedFreeMetadata_footprints
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.2 = footprint .metadata
        (Region.mk 0 0 metadata.allocation.bytes.length) ∧
      result.2.2 = footprint .metadata
        (Region.mk 0 0 metadata.allocation.bytes.length) := by
  cases hs : freeMetadata metadata with
  | none => simp [pairedFreeMetadata, hs] at hresult
  | some sourceResult =>
      cases ht : freeMetadata (renameZeroTokenMetadata resolve metadata) with
      | none => simp [pairedFreeMetadata, hs, ht] at hresult
      | some targetResult =>
          simp [pairedFreeMetadata, hs, ht] at hresult
          rcases hresult with rfl
          have htarget := freeMetadata_footprint_shape
            (renameZeroTokenMetadata resolve metadata) _ ht
          exact ⟨freeMetadata_footprint_shape _ _ hs,
            by simpa [renameZeroTokenMetadata] using htarget⟩

theorem pairedFreeMetadata_empty_footprints
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result)
    (hbytes : metadata.allocation.bytes = []) :
    result.1.2 = footprint .metadata (Region.mk 0 0 0) ∧
      result.2.2 = footprint .metadata (Region.mk 0 0 0) := by
  have hgeneral := pairedFreeMetadata_footprints resolve metadata result hresult
  simpa [hbytes, renameZeroTokenMetadata] using hgeneral

theorem pairedFreeMetadata_marks_dead
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.allocation.live = false ∧
      result.2.1.allocation.live = false := by
  cases hs : freeMetadata metadata with
  | none => simp [pairedFreeMetadata, hs] at hresult
  | some sourceResult =>
      cases ht : freeMetadata (renameZeroTokenMetadata resolve metadata) with
      | none => simp [pairedFreeMetadata, hs, ht] at hresult
      | some targetResult =>
          simp [pairedFreeMetadata, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨freeMetadata_marks_dead _ _ hs,
            freeMetadata_marks_dead _ _ ht⟩

theorem pairedFreeMetadata_empty_marks_dead
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hbytes : metadata.allocation.bytes = [])
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.allocation.live = false ∧
      result.2.1.allocation.live = false := by
  exact pairedFreeMetadata_marks_dead resolve metadata result hresult

theorem pairedFreeMetadata_preserves_locations
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.locations = metadata.locations ∧
      result.2.1.locations = (renameZeroTokenMetadata resolve metadata).locations := by
  cases hs : freeMetadata metadata with
  | none => simp [pairedFreeMetadata, hs] at hresult
  | some sourceResult =>
      cases ht : freeMetadata (renameZeroTokenMetadata resolve metadata) with
      | none => simp [pairedFreeMetadata, hs, ht] at hresult
      | some targetResult =>
          simp [pairedFreeMetadata, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨freeMetadata_preserves_locations _ _ hs,
            freeMetadata_preserves_locations _ _ ht⟩

theorem pairedFreeMetadata_preserves_lengths
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
      result.1.1.locations.length = metadata.locations.length ∧
      result.2.1.allocation.bytes.length =
        (renameZeroTokenMetadata resolve metadata).allocation.bytes.length ∧
      result.2.1.locations.length =
        (renameZeroTokenMetadata resolve metadata).locations.length := by
  cases hs : freeMetadata metadata with
  | none => simp [pairedFreeMetadata, hs] at hresult
  | some sourceResult =>
      cases ht : freeMetadata (renameZeroTokenMetadata resolve metadata) with
      | none => simp [pairedFreeMetadata, hs, ht] at hresult
      | some targetResult =>
          simp [pairedFreeMetadata, hs, ht] at hresult
          rcases hresult with rfl
          have hslocations := freeMetadata_preserves_locations _ _ hs
          have htlocations := freeMetadata_preserves_locations _ _ ht
          have hspayload := freeMetadata_preserves_payload _ _ hs
          have htpayload := freeMetadata_preserves_payload _ _ ht
          exact ⟨congrArg List.length hspayload.2.1,
            congrArg List.length hslocations,
            congrArg List.length htpayload.2.1,
            congrArg List.length htlocations⟩

theorem pairedFreeMetadata_preserves_payload
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.allocation.address = metadata.allocation.address ∧
      result.1.1.allocation.bytes = metadata.allocation.bytes ∧
      result.1.1.allocation.state = metadata.allocation.state ∧
      result.2.1.allocation.address =
        (renameZeroTokenMetadata resolve metadata).allocation.address ∧
      result.2.1.allocation.bytes =
        (renameZeroTokenMetadata resolve metadata).allocation.bytes ∧
      result.2.1.allocation.state =
        (renameZeroTokenMetadata resolve metadata).allocation.state := by
  cases hs : freeMetadata metadata with
  | none => simp [pairedFreeMetadata, hs] at hresult
  | some sourceResult =>
      cases ht : freeMetadata (renameZeroTokenMetadata resolve metadata) with
      | none => simp [pairedFreeMetadata, hs, ht] at hresult
      | some targetResult =>
          simp [pairedFreeMetadata, hs, ht] at hresult
          rcases hresult with rfl
          obtain ⟨hsa, hsb, hsc⟩ := freeMetadata_preserves_payload _ _ hs
          obtain ⟨hta, htb, htc⟩ := freeMetadata_preserves_payload _ _ ht
          exact ⟨hsa, hsb, hsc, hta, htb, htc⟩

theorem pairedFreeMetadata_preserves_wellFormed
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hmetadata : metadata.wellFormed 0)
    (hmetadataTarget : (renameZeroTokenMetadata resolve metadata).wellFormed 0)
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.wellFormed 0 ∧ result.2.1.wellFormed 0 := by
  cases hs : freeMetadata metadata with
  | none => simp [pairedFreeMetadata, hs] at hresult
  | some sourceResult =>
      cases ht : freeMetadata (renameZeroTokenMetadata resolve metadata) with
      | none => simp [pairedFreeMetadata, hs, ht] at hresult
      | some targetResult =>
          simp [pairedFreeMetadata, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := hresult
          rcases hpair with rfl
          exact ⟨freeMetadata_preserves_wellFormed metadata sourceResult
              hmetadata hs,
            freeMetadata_preserves_wellFormed
              (renameZeroTokenMetadata resolve metadata) targetResult
              hmetadataTarget ht⟩

theorem pairedFreeMetadata_preserves_wellFormed_from_source
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hmetadata : metadata.wellFormed 0)
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.wellFormed 0 ∧ result.2.1.wellFormed 0 := by
  exact pairedFreeMetadata_preserves_wellFormed resolve metadata result hmetadata
    (renameZeroTokenMetadata_preserves_wellFormed resolve metadata hmetadata) hresult

theorem pairedFreeMetadata_empty_preserves_payload
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hbytes : metadata.allocation.bytes = [])
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.allocation.bytes = [] ∧
      result.2.1.allocation.bytes = [] := by
  have hgeneral := pairedFreeMetadata_preserves_payload resolve metadata result hresult
  have htargetBytes : (renameZeroTokenMetadata resolve metadata).allocation.bytes = [] := by
    simp [renameZeroTokenMetadata, hbytes]
  rcases hgeneral with ⟨hsa, hsb, hsc, hta, htb, htc⟩
  exact ⟨by simpa [hbytes] using hsb,
    by simpa [htargetBytes] using htb⟩

theorem pairedFreeMetadata_empty_preserves_lengths
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hbytes : metadata.allocation.bytes = [])
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.allocation.bytes.length = 0 ∧
      result.1.1.locations.length = metadata.locations.length ∧
      result.2.1.allocation.bytes.length = 0 ∧
      result.2.1.locations.length =
        (renameZeroTokenMetadata resolve metadata).locations.length := by
  have hgeneral := pairedFreeMetadata_preserves_lengths resolve metadata result hresult
  have htargetBytes : (renameZeroTokenMetadata resolve metadata).allocation.bytes = [] := by
    simp [renameZeroTokenMetadata, hbytes]
  exact ⟨by simpa [hbytes] using hgeneral.1,
    hgeneral.2.1,
    by simpa [htargetBytes] using hgeneral.2.2.1,
    hgeneral.2.2.2⟩

theorem pairedFreeMetadata_empty_preserves_locations
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hbytes : metadata.allocation.bytes = [])
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.locations = metadata.locations ∧
      result.2.1.locations = (renameZeroTokenMetadata resolve metadata).locations := by
  exact pairedFreeMetadata_preserves_locations resolve metadata result hresult

theorem pairedFreeMetadata_empty_result_shape
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hbytes : metadata.allocation.bytes = [])
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.allocation.bytes = [] ∧
      result.2.1.allocation.bytes = [] ∧
      result.1.1.locations = metadata.locations ∧
      result.2.1.locations = (renameZeroTokenMetadata resolve metadata).locations ∧
      result.1.1.allocation.live = false ∧
      result.2.1.allocation.live = false ∧
      result.1.2 = footprint .metadata (Region.mk 0 0 0) ∧
      result.2.2 = footprint .metadata (Region.mk 0 0 0) := by
  have hpayload := pairedFreeMetadata_empty_preserves_payload
    resolve metadata result hbytes hresult
  have hlocations := pairedFreeMetadata_empty_preserves_locations
    resolve metadata result hbytes hresult
  have hdead := pairedFreeMetadata_empty_marks_dead
    resolve metadata result hbytes hresult
  have hfootprints := pairedFreeMetadata_empty_footprints
    resolve metadata result hresult hbytes
  exact ⟨hpayload.1, hpayload.2, hlocations.1, hlocations.2,
    hdead.1, hdead.2, hfootprints.1, hfootprints.2⟩

theorem freeMetadata_empty_preserves_payload
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hbytes : metadata.allocation.bytes = [])
    (hresult : freeMetadata metadata = some result) :
    result.1.allocation.address = metadata.allocation.address ∧
      result.1.allocation.bytes = [] ∧
      result.1.allocation.state = metadata.allocation.state := by
  have hgeneral := freeMetadata_preserves_payload metadata result hresult
  exact ⟨hgeneral.1, by simpa [hbytes] using hgeneral.2.1, hgeneral.2.2⟩

theorem freeMetadata_empty_result_footprint
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hbytes : metadata.allocation.bytes = [])
    (hresult : freeMetadata metadata = some result) :
    result.2 = footprint .metadata (Region.mk 0 0 0) := by
  have hgeneral := freeMetadata_footprint_shape metadata result hresult
  simpa [hbytes] using hgeneral

theorem freeMetadata_empty_preserves_lengths
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hbytes : metadata.allocation.bytes = [])
    (hresult : freeMetadata metadata = some result) :
    result.1.allocation.bytes.length = 0 ∧
      result.1.locations.length = metadata.locations.length := by
  have hpayload := freeMetadata_empty_preserves_payload metadata result hbytes hresult
  have hlocations := freeMetadata_preserves_locations metadata result hresult
  exact ⟨by simpa [hpayload.2] using List.length_nil,
    congrArg List.length hlocations⟩

theorem pairedFreeMetadata_empty_result_wellFormed
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hmetadata : metadata.wellFormed 0)
    (hbytes : metadata.allocation.bytes = [])
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.1.1.wellFormed 0 ∧ result.2.1.wellFormed 0 := by
  exact pairedFreeMetadata_preserves_wellFormed_from_source
    resolve metadata result hmetadata hresult

theorem freeMetadata_empty_result_wellFormed
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hmetadata : metadata.wellFormed 0)
    (hbytes : metadata.allocation.bytes = [])
    (hresult : freeMetadata metadata = some result) :
    result.1.wellFormed 0 := by
  exact freeMetadata_preserves_wellFormed metadata result hmetadata hresult

inductive FreeOutcome where
  | nullSuccess
  | freed
  | stalePointer
  | unmatchedPointer
deriving Repr, BEq, DecidableEq

def freePointer (metadata : Option (AllocationMetadata Tag State TypeId)) : FreeOutcome :=
  match metadata with
  | none => .nullSuccess
  | some metadata => if metadata.allocation.live then .freed else .stalePointer

theorem freePointer_result_contract
    (metadata : Option (AllocationMetadata Tag State TypeId))
    (result : FreeOutcome)
    (hresult : freePointer metadata = result) :
    match metadata, result with
    | none, .nullSuccess => True
    | some allocation, .freed => allocation.allocation.live = true
    | some allocation, .stalePointer => allocation.allocation.live = false
    | _, .unmatchedPointer => False
    | _, _ => False := by
  cases metadata with
  | none =>
      cases result <;> simp [freePointer] at hresult ⊢
  | some allocation =>
      cases hlive : allocation.allocation.live with
      | false =>
          cases result <;> simp [freePointer, hlive] at hresult ⊢
      | true =>
          cases result <;> simp [freePointer, hlive] at hresult ⊢

theorem freePointer_null_shape :
    freePointer (Tag := Tag) (State := State) (TypeId := TypeId) none = .nullSuccess := by
  rfl

theorem freePointer_live_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (hlive : metadata.allocation.live = true) :
    freePointer (some metadata) = .freed := by
  simp [freePointer, hlive]

theorem freePointer_empty_live_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (hlive : metadata.allocation.live = true)
    (hbytes : metadata.allocation.bytes = []) :
    freePointer (some metadata) = .freed := by
  simp [freePointer, hlive]

theorem freePointer_dead_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (hdead : metadata.allocation.live = false) :
    freePointer (some metadata) = .stalePointer := by
  simp [freePointer, hdead]

theorem freePointer_empty_dead_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (hdead : metadata.allocation.live = false)
    (hbytes : metadata.allocation.bytes = []) :
    freePointer (some metadata) = .stalePointer := by
  simp [freePointer, hdead]

theorem freeMetadata_result_stale_pointer
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : freeMetadata metadata = some result) :
    freePointer (some result.1) = .stalePointer := by
  have hdead := freeMetadata_marks_dead metadata result hresult
  simp [freePointer, hdead]

theorem freeMetadata_empty_result_stale_pointer
    (metadata : AllocationMetadata Tag State TypeId)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hbytes : metadata.allocation.bytes = [])
    (hresult : freeMetadata metadata = some result) :
    freePointer (some result.1) = .stalePointer := by
  exact freeMetadata_result_stale_pointer metadata result hresult

theorem pairedFreeMetadata_result_stale_pointers
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    freePointer (some result.1.1) = .stalePointer ∧
      freePointer (some result.2.1) = .stalePointer := by
  have hdead := pairedFreeMetadata_marks_dead resolve metadata result hresult
  exact ⟨freePointer_dead_shape _ hdead.1,
    freePointer_dead_shape _ hdead.2⟩

theorem pairedFreeMetadata_empty_result_stale_pointers
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hbytes : metadata.allocation.bytes = [])
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    freePointer (some result.1.1) = .stalePointer ∧
      freePointer (some result.2.1) = .stalePointer := by
  exact pairedFreeMetadata_result_stale_pointers resolve metadata result hresult

theorem pairedFreeMetadata_empty_contract
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hmetadata : metadata.wellFormed 0)
    (hbytes : metadata.allocation.bytes = [])
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    (result.1.1.allocation.bytes = [] ∧
      result.2.1.allocation.bytes = [] ∧
      result.1.1.locations = metadata.locations ∧
      result.2.1.locations = (renameZeroTokenMetadata resolve metadata).locations ∧
      result.1.1.allocation.live = false ∧
      result.2.1.allocation.live = false ∧
      result.1.2 = footprint .metadata (Region.mk 0 0 0) ∧
      result.2.2 = footprint .metadata (Region.mk 0 0 0)) ∧
      (result.1.1.wellFormed 0 ∧ result.2.1.wellFormed 0) ∧
      (freePointer (some result.1.1) = .stalePointer ∧
        freePointer (some result.2.1) = .stalePointer) := by
  constructor
  · exact pairedFreeMetadata_empty_result_shape resolve metadata result hbytes hresult
  constructor
  · exact pairedFreeMetadata_empty_result_wellFormed resolve metadata result
      hmetadata hbytes hresult
  · exact pairedFreeMetadata_empty_result_stale_pointers resolve metadata result
      hbytes hresult

theorem freePointer_live_or_dead
    (metadata : AllocationMetadata Tag State TypeId) :
    freePointer (some metadata) = .freed ∨
      freePointer (some metadata) = .stalePointer := by
  cases h : metadata.allocation.live <;>
    simp [freePointer, h]

theorem freePointer_classification
    (metadata : Option (AllocationMetadata Tag State TypeId)) :
    freePointer metadata = .nullSuccess ∨
      freePointer metadata = .freed ∨
      freePointer metadata = .stalePointer := by
  cases metadata with
  | none => simp [freePointer]
  | some metadata =>
      cases h : metadata.allocation.live <;>
        simp [freePointer, h]

theorem freePointer_contract
    (metadata : Option (AllocationMetadata Tag State TypeId))
    (outcome : FreeOutcome) :
    freePointer metadata = outcome ↔
      match metadata, outcome with
      | none, .nullSuccess => True
      | some metadata, .freed => metadata.allocation.live = true
      | some metadata, .stalePointer => metadata.allocation.live = false
      | _, _ => False := by
  cases metadata with
  | none => cases outcome <;> simp [freePointer]
  | some metadata =>
      cases hlive : metadata.allocation.live <;>
        cases outcome <;> simp [freePointer, hlive]

theorem freePointer_ne_unmatchedPointer
    (metadata : Option (AllocationMetadata Tag State TypeId)) :
    freePointer metadata ≠ .unmatchedPointer := by
  cases metadata with
  | none => simp [freePointer]
  | some metadata =>
      cases h : metadata.allocation.live <;>
        simp [freePointer, h]

def pairedFreePointer (resolve : AllocId → Nat)
    (metadata : Option (AllocationMetadata Tag State TypeId)) : Bool :=
  if freePointer metadata =
      freePointer (metadata.map (renameZeroTokenMetadata resolve)) then true else false

theorem pairedFreePointer_sound (resolve : AllocId → Nat)
    (metadata : Option (AllocationMetadata Tag State TypeId)) :
    pairedFreePointer resolve metadata := by
  cases metadata with
  | none => simp [pairedFreePointer]
  | some metadata =>
      cases hlive : metadata.allocation.live <;>
        simp [pairedFreePointer, freePointer, renameZeroTokenMetadata, hlive]

theorem pairedFreePointer_true (resolve : AllocId → Nat)
    (metadata : Option (AllocationMetadata Tag State TypeId)) :
    pairedFreePointer resolve metadata = true := by
  exact pairedFreePointer_sound resolve metadata

theorem pairedFreePointer_failure_contract (resolve : AllocId → Nat)
    (metadata : Option (AllocationMetadata Tag State TypeId)) :
    pairedFreePointer resolve metadata = false ↔ False := by
  cases metadata with
  | none => simp [pairedFreePointer, freePointer]
  | some metadata =>
      cases hlive : metadata.allocation.live <;>
        simp [pairedFreePointer, freePointer, renameZeroTokenMetadata, hlive]

theorem pairedFreePointer_agrees (resolve : AllocId → Nat)
    (metadata : Option (AllocationMetadata Tag State TypeId)) :
    freePointer metadata =
      freePointer (metadata.map (renameZeroTokenMetadata resolve)) := by
  cases metadata with
  | none => rfl
  | some metadata =>
      cases hlive : metadata.allocation.live <;>
        simp [freePointer, renameZeroTokenMetadata, hlive]

theorem pairedFreePointer_empty_agrees
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hbytes : metadata.allocation.bytes = []) :
    freePointer (some metadata) =
      freePointer (some (renameZeroTokenMetadata resolve metadata)) := by
  exact pairedFreePointer_agrees resolve (some metadata)

theorem pairedFreePointer_empty_true
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (hbytes : metadata.allocation.bytes = []) :
    pairedFreePointer resolve (some metadata) = true := by
  exact pairedFreePointer_true resolve (some metadata)

def representationLoadMetadataByte
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice) :
    Option (Byte Tag × Footprint) := do
  let byte ← metadata.allocation.bytes[offset]?
  let location ← metadata.locations[offset]?
  match location.effectiveType, choice with
  | .padding, .byte bits | .indeterminate, .byte bits =>
      some (.value bits none none,
        footprint .read { allocation := 0, offset := offset, width := 1 })
  | _, _ => some (byte,
      footprint .read { allocation := 0, offset := offset, width := 1 })

theorem representationLoadMetadataByte_empty_none
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (hbytes : metadata.allocation.bytes = []) :
    representationLoadMetadataByte metadata offset choice = none := by
  simp [representationLoadMetadataByte, hbytes]

theorem representationLoadMetadataByte_success
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (choice : RepresentationChoice) (byte : Byte Tag)
    (location : LocationState TypeId)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some location) :
    representationLoadMetadataByte metadata offset choice =
      some (match location.effectiveType, choice with
        | .padding, .byte bits | .indeterminate, .byte bits =>
            (.value bits none none,
              footprint .read { allocation := 0, offset := offset, width := 1 })
        | _, _ => (byte,
            footprint .read { allocation := 0, offset := offset, width := 1 })) := by
  cases htype : location.effectiveType <;> cases choice <;>
    simp [representationLoadMetadataByte, hbyte, hlocation, htype]

theorem representationLoadMetadataByte_contract
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (choice : RepresentationChoice) (result : Byte Tag × Footprint)
    (hresult : representationLoadMetadataByte metadata offset choice = some result) :
    ∃ byte location,
      metadata.allocation.bytes[offset]? = some byte ∧
      metadata.locations[offset]? = some location ∧
      result =
        (match location.effectiveType, choice with
        | .padding, .byte bits | .indeterminate, .byte bits =>
            (.value bits none none,
              footprint .read { allocation := 0, offset := offset, width := 1 })
        | _, _ => (byte,
            footprint .read { allocation := 0, offset := offset, width := 1 })) := by
  cases hbyte : metadata.allocation.bytes[offset]? with
  | none =>
      simp [representationLoadMetadataByte, hbyte] at hresult
  | some byte =>
      cases hlocation : metadata.locations[offset]? with
      | none =>
          simp [representationLoadMetadataByte, hbyte, hlocation] at hresult
      | some location =>
          cases htype : location.effectiveType <;> cases choice <;>
            simp [representationLoadMetadataByte, hbyte, hlocation, htype] at hresult
          all_goals
            refine ⟨byte, location, rfl, rfl, ?_⟩
            simpa [htype] using hresult.symm

theorem representationLoadMetadataByte_footprint
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (choice : RepresentationChoice) (result : Byte Tag × Footprint)
    (hresult : representationLoadMetadataByte metadata offset choice = some result) :
    result.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hbyte : metadata.allocation.bytes[offset]? with
  | none => simp [representationLoadMetadataByte, hbyte] at hresult
  | some byte =>
      cases hlocation : metadata.locations[offset]? with
      | none => simp [representationLoadMetadataByte, hbyte, hlocation] at hresult
      | some location =>
          cases htype : location.effectiveType <;> cases choice <;>
            simp [representationLoadMetadataByte, hbyte, hlocation, htype] at hresult
          all_goals exact congrArg (fun pair => pair.2) hresult.symm

theorem representationLoadMetadataByte_outOfBounds
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (choice : RepresentationChoice)
    (hbyte : metadata.allocation.bytes[offset]? = none) :
    representationLoadMetadataByte metadata offset choice = none := by
  simp [representationLoadMetadataByte, hbyte]

theorem representationLoadMetadataByte_missing_location
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (choice : RepresentationChoice) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = none) :
    representationLoadMetadataByte metadata offset choice = none := by
  simp [representationLoadMetadataByte, hbyte, hlocation]

theorem representationLoadMetadataByte_failure_contract
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (choice : RepresentationChoice) :
    representationLoadMetadataByte metadata offset choice = none ↔
      metadata.allocation.bytes[offset]? = none ∨
      metadata.locations[offset]? = none := by
  constructor
  · intro hnone
    cases hbyte : metadata.allocation.bytes[offset]? with
    | none => exact Or.inl rfl
    | some byte =>
        cases hlocation : metadata.locations[offset]? with
        | none => exact Or.inr rfl
        | some location =>
            cases htype : location.effectiveType <;> cases choice <;>
              simp [representationLoadMetadataByte, hbyte, hlocation, htype] at hnone
  · rintro (hbyte | hlocation)
    · simp [representationLoadMetadataByte, hbyte]
    · simp [representationLoadMetadataByte, hlocation]

theorem representationLoadMetadataByte_indeterminate_choice
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (bits : UInt8) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .indeterminate, initialized := false }) :
    representationLoadMetadataByte metadata offset (.byte bits) =
      some (.value bits none none,
        footprint .read { allocation := 0, offset := offset, width := 1 }) := by
  simp [representationLoadMetadataByte, hbyte, hlocation]

theorem representationLoadMetadataByte_padding_choice
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (bits : UInt8) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .padding, initialized := true }) :
    representationLoadMetadataByte metadata offset (.byte bits) =
      some (.value bits none none,
        footprint .read { allocation := 0, offset := offset, width := 1 }) := by
  simp [representationLoadMetadataByte, hbyte, hlocation]

theorem representationLoadMetadataByte_untyped_byte
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (choice : RepresentationChoice) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .untyped, initialized := true }) :
    representationLoadMetadataByte metadata offset choice =
      some (byte,
        footprint .read { allocation := 0, offset := offset, width := 1 }) := by
  simp [representationLoadMetadataByte, hbyte, hlocation]

def pairedRepresentationLoadMetadataByte (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice) :
    Option ((Byte Tag × Footprint) × (Byte Tag × Footprint)) := do
  let sourceResult ← representationLoadMetadataByte metadata offset choice
  let targetResult ← representationLoadMetadataByte (renameMetadata resolve id metadata)
    offset choice
  some (sourceResult, targetResult)

theorem pairedRepresentationLoadMetadataByte_empty_none
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (hbytes : metadata.allocation.bytes = []) :
    pairedRepresentationLoadMetadataByte resolve id metadata offset choice = none := by
  simp [pairedRepresentationLoadMetadataByte, representationLoadMetadataByte,
    renameMetadata, hbytes]

theorem pairedRepresentationLoadMetadataByte_decompose
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedRepresentationLoadMetadataByte resolve id metadata offset choice =
      some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : representationLoadMetadataByte metadata offset choice with
  | none => simp [pairedRepresentationLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : representationLoadMetadataByte (renameMetadata resolve id metadata)
          offset choice with
      | none => simp [pairedRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          rw [pairedRepresentationLoadMetadataByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := by
            simpa only [Option.bind_some] using Option.some.inj hresult
          exact ⟨sourceResult, targetResult, hpair.symm⟩

theorem pairedRepresentationLoadMetadataByte_sound
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedRepresentationLoadMetadataByte resolve id metadata offset choice =
      some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      representationLoadMetadataByte metadata offset choice = some sourceResult ∧
      representationLoadMetadataByte (renameMetadata resolve id metadata) offset choice =
        some targetResult := by
  cases hs : representationLoadMetadataByte metadata offset choice with
  | none => simp [pairedRepresentationLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : representationLoadMetadataByte (renameMetadata resolve id metadata)
          offset choice with
      | none => simp [pairedRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedRepresentationLoadMetadataByte, hs, ht] at hresult
          exact ⟨sourceResult, targetResult, hresult.symm,
            by simpa using hs, by simpa using ht⟩

theorem pairedRepresentationLoadMetadataByte_refusal
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (hrefusal : representationLoadMetadataByte metadata offset choice = none ∨
      representationLoadMetadataByte (renameMetadata resolve id metadata) offset choice = none) :
    pairedRepresentationLoadMetadataByte resolve id metadata offset choice = none := by
  cases hrefusal with
  | inl hsource => simp [pairedRepresentationLoadMetadataByte, hsource]
  | inr htarget => simp [pairedRepresentationLoadMetadataByte, htarget]

theorem pairedRepresentationLoadMetadataByte_refusal_source
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (hsource : representationLoadMetadataByte metadata offset choice = none) :
    pairedRepresentationLoadMetadataByte resolve id metadata offset choice = none := by
  simp [pairedRepresentationLoadMetadataByte, hsource]

theorem pairedRepresentationLoadMetadataByte_refusal_target
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (htarget : representationLoadMetadataByte (renameMetadata resolve id metadata)
      offset choice = none) :
    pairedRepresentationLoadMetadataByte resolve id metadata offset choice = none := by
  simp [pairedRepresentationLoadMetadataByte, htarget]

theorem pairedRepresentationLoadMetadataByte_failure_contract
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice) :
    pairedRepresentationLoadMetadataByte resolve id metadata offset choice = none ↔
      representationLoadMetadataByte metadata offset choice = none ∨
        representationLoadMetadataByte (renameMetadata resolve id metadata)
          offset choice = none := by
  constructor
  · intro hnone
    cases hs : representationLoadMetadataByte metadata offset choice with
    | none => exact Or.inl rfl
    | some sourceResult =>
        cases ht : representationLoadMetadataByte (renameMetadata resolve id metadata)
            offset choice with
        | none => exact Or.inr rfl
        | some targetResult =>
            simp [pairedRepresentationLoadMetadataByte, hs, ht] at hnone
  · rintro (hsource | htarget)
    · simp [pairedRepresentationLoadMetadataByte, hsource]
    · simp [pairedRepresentationLoadMetadataByte, htarget]

theorem pairedRepresentationLoadMetadataByte_footprints
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedRepresentationLoadMetadataByte resolve id metadata offset choice =
      some result) :
    result.1.2 = footprint .read { allocation := 0, offset := offset, width := 1 } ∧
      result.2.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hs : representationLoadMetadataByte metadata offset choice with
  | none => simp [pairedRepresentationLoadMetadataByte, hs] at hresult
  | some sourceResult =>
      cases ht : representationLoadMetadataByte (renameMetadata resolve id metadata)
          offset choice with
      | none => simp [pairedRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedRepresentationLoadMetadataByte, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨representationLoadMetadataByte_footprint _ _ _ _ hs,
            representationLoadMetadataByte_footprint _ _ _ _ ht⟩

theorem pairedRepresentationLoadMetadataByte_untyped_byte
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hbyteTarget : (renameMetadata resolve id metadata).allocation.bytes[offset]? =
      some (renameByte resolve byte))
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .untyped, initialized := true }) :
    pairedRepresentationLoadMetadataByte resolve id metadata offset choice =
      some ((byte, footprint .read { allocation := 0, offset := offset, width := 1 }),
        (renameByte resolve byte,
          footprint .read { allocation := 0, offset := offset, width := 1 })) := by
  have htargetLocation : (renameMetadata resolve id metadata).locations[offset]? = some
      { effectiveType := .untyped, initialized := true } := by
    simpa [renameMetadata] using hlocation
  simp [pairedRepresentationLoadMetadataByte,
    representationLoadMetadataByte, hbyte, hbyteTarget, hlocation, htargetLocation]

theorem pairedRepresentationLoadMetadataByte_padding_choice
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (bits : UInt8) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hbyteTarget : (renameMetadata resolve id metadata).allocation.bytes[offset]? =
      some (renameByte resolve byte))
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .padding, initialized := true }) :
    pairedRepresentationLoadMetadataByte resolve id metadata offset (.byte bits) =
      some ((.value bits none none,
          footprint .read { allocation := 0, offset := offset, width := 1 }),
        (.value bits none none,
          footprint .read { allocation := 0, offset := offset, width := 1 })) := by
  have htargetLocation : (renameMetadata resolve id metadata).locations[offset]? = some
      { effectiveType := .padding, initialized := true } := by
    simpa [renameMetadata] using hlocation
  simp [pairedRepresentationLoadMetadataByte,
    representationLoadMetadataByte, hbyte, hbyteTarget, hlocation, htargetLocation]

theorem pairedRepresentationLoadMetadataByte_indeterminate_choice
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (bits : UInt8) (byte : Byte Tag)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hbyteTarget : (renameMetadata resolve id metadata).allocation.bytes[offset]? =
      some (renameByte resolve byte))
    (hlocation : metadata.locations[offset]? = some
      { effectiveType := .indeterminate, initialized := false }) :
    pairedRepresentationLoadMetadataByte resolve id metadata offset (.byte bits) =
      some ((.value bits none none,
          footprint .read { allocation := 0, offset := offset, width := 1 }),
        (.value bits none none,
          footprint .read { allocation := 0, offset := offset, width := 1 })) := by
  have htargetLocation : (renameMetadata resolve id metadata).locations[offset]? = some
      { effectiveType := .indeterminate, initialized := false } := by
    simpa [renameMetadata] using hlocation
  simp [pairedRepresentationLoadMetadataByte,
    representationLoadMetadataByte, hbyte, hbyteTarget, hlocation, htargetLocation]

def pairedStoreRepresentationLoadMetadataByte
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice) :
    Option (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))) := do
  let sourceStore ← storeMetadataByte metadata offset byte
  let targetStore ← storeMetadataByte (renameMetadata resolve id metadata)
    offset (renameByte resolve byte)
  let sourceLoad ← representationLoadMetadataByte sourceStore.1 offset choice
  let targetLoad ← representationLoadMetadataByte targetStore.1 offset choice
  some ((sourceStore, sourceLoad), (targetStore, targetLoad))

theorem pairedStoreRepresentationLoadMetadataByte_empty_none
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (hbytes : metadata.allocation.bytes = []) :
    pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice = none := by
  simp [pairedStoreRepresentationLoadMetadataByte, storeMetadataByte,
    renameMetadata, hbytes]

theorem pairedStoreRepresentationLoadMetadataByte_decompose
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (result : (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))))
    (hresult : pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice =
      some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreRepresentationLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata) offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : representationLoadMetadataByte sourceStore.1 offset choice with
          | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : representationLoadMetadataByte targetStore.1 offset choice with
              | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  exact ⟨(sourceStore, sourceLoad), (targetStore, targetLoad), hresult.symm⟩

theorem pairedStoreRepresentationLoadMetadataByte_refusal
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (hrefusal :
      storeMetadataByte metadata offset byte = none ∨
      storeMetadataByte (renameMetadata resolve id metadata) offset
        (renameByte resolve byte) = none ∨
      (∃ sourceStore,
        storeMetadataByte metadata offset byte = some sourceStore ∧
        representationLoadMetadataByte sourceStore.1 offset choice = none) ∨
      (∃ targetStore,
        storeMetadataByte (renameMetadata resolve id metadata) offset
          (renameByte resolve byte) = some targetStore ∧
        representationLoadMetadataByte targetStore.1 offset choice = none)) :
    pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice = none := by
  rcases hrefusal with hsource | htarget | hsourceLoad | htargetLoad
  · simp [pairedStoreRepresentationLoadMetadataByte, hsource]
  · simp [pairedStoreRepresentationLoadMetadataByte, htarget]
  · rcases hsourceLoad with ⟨sourceStore, hstore, hload⟩
    simp [pairedStoreRepresentationLoadMetadataByte, hstore, hload]
  · rcases htargetLoad with ⟨targetStore, hstore, hload⟩
    simp [pairedStoreRepresentationLoadMetadataByte, hstore, hload]

theorem pairedStoreRepresentationLoadMetadataByte_refusal_source_store
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (hsource : storeMetadataByte metadata offset byte = none) :
    pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice = none := by
  simp [pairedStoreRepresentationLoadMetadataByte, hsource]

theorem pairedStoreRepresentationLoadMetadataByte_refusal_target_store
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (htarget : storeMetadataByte (renameMetadata resolve id metadata) offset
      (renameByte resolve byte) = none) :
    pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice = none := by
  simp [pairedStoreRepresentationLoadMetadataByte, htarget]

theorem pairedStoreRepresentationLoadMetadataByte_refusal_source_load
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (sourceStore : AllocationMetadata Tag State TypeId × Footprint)
    (hstore : storeMetadataByte metadata offset byte = some sourceStore)
    (hload : representationLoadMetadataByte sourceStore.1 offset choice = none) :
    pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice = none := by
  simp [pairedStoreRepresentationLoadMetadataByte, hstore, hload]

theorem pairedStoreRepresentationLoadMetadataByte_refusal_target_load
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (targetStore : AllocationMetadata Tag State TypeId × Footprint)
    (htarget : storeMetadataByte (renameMetadata resolve id metadata) offset
      (renameByte resolve byte) = some targetStore)
    (hload : representationLoadMetadataByte targetStore.1 offset choice = none) :
    pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice = none := by
  simp [pairedStoreRepresentationLoadMetadataByte, htarget, hload]

theorem pairedStoreRepresentationLoadMetadataByte_failure_contract
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice) :
    pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice = none ↔
      storeMetadataByte metadata offset byte = none ∨
      storeMetadataByte (renameMetadata resolve id metadata)
        offset (renameByte resolve byte) = none ∨
      (∃ sourceStore,
        storeMetadataByte metadata offset byte = some sourceStore ∧
        representationLoadMetadataByte sourceStore.1 offset choice = none) ∨
      (∃ targetStore,
        storeMetadataByte (renameMetadata resolve id metadata) offset
          (renameByte resolve byte) = some targetStore ∧
        representationLoadMetadataByte targetStore.1 offset choice = none) := by
  constructor
  · intro hnone
    cases hs : storeMetadataByte metadata offset byte with
    | none => exact Or.inl rfl
    | some sourceStore =>
        cases ht : storeMetadataByte (renameMetadata resolve id metadata) offset
            (renameByte resolve byte) with
        | none => exact Or.inr (Or.inl rfl)
        | some targetStore =>
            cases hsl : representationLoadMetadataByte sourceStore.1 offset choice with
            | none => exact Or.inr (Or.inr (Or.inl ⟨sourceStore, rfl, hsl⟩))
            | some sourceLoad =>
                cases htl : representationLoadMetadataByte targetStore.1 offset choice with
                | none => exact Or.inr (Or.inr (Or.inr ⟨targetStore, rfl, htl⟩))
                | some targetLoad =>
                    simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hnone
  · rintro (hsource | htarget | hsourceLoad | htargetLoad)
    · simp [pairedStoreRepresentationLoadMetadataByte, hsource]
    · simp [pairedStoreRepresentationLoadMetadataByte, htarget]
    · rcases hsourceLoad with ⟨sourceStore, hstore, hload⟩
      simp [pairedStoreRepresentationLoadMetadataByte, hstore, hload]
    · rcases htargetLoad with ⟨targetStore, hstore, hload⟩
      simp [pairedStoreRepresentationLoadMetadataByte, hstore, hload]

theorem pairedStoreRepresentationLoadMetadataByte_footprints
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (result : (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))))
    (hresult : pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice =
      some result) :
    result.1.1.2 = footprint .write { allocation := 0, offset := offset, width := 1 } ∧
      result.1.2.2 = footprint .read { allocation := 0, offset := offset, width := 1 } ∧
      result.2.1.2 = footprint .write { allocation := 0, offset := offset, width := 1 } ∧
      result.2.2.2 = footprint .read { allocation := 0, offset := offset, width := 1 } := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreRepresentationLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata)
          offset (renameByte resolve byte) with
      | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : representationLoadMetadataByte sourceStore.1 offset choice with
          | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : representationLoadMetadataByte targetStore.1 offset choice with
              | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : result = ((sourceStore, sourceLoad), (targetStore, targetLoad)) :=
                    hresult.symm
                  rcases hpair with rfl
                  exact ⟨(storeMetadataByte_success_shape _ _ _ _ hs).2.2,
                    representationLoadMetadataByte_footprint _ _ _ _ hsl,
                    (storeMetadataByte_success_shape _ _ _ _ ht).2.2,
                    representationLoadMetadataByte_footprint _ _ _ _ htl⟩

theorem pairedStoreRepresentationLoadMetadataByte_preserves_locations
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (result : (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))))
    (hresult : pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice =
      some result) :
    result.1.1.1.locations = metadata.locations ∧
      result.2.1.1.locations = (renameMetadata resolve id metadata).locations := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreRepresentationLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata)
          offset (renameByte resolve byte) with
      | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : representationLoadMetadataByte sourceStore.1 offset choice with
          | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : representationLoadMetadataByte targetStore.1 offset choice with
              | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : result = ((sourceStore, sourceLoad), (targetStore, targetLoad)) :=
                    hresult.symm
                  rcases hpair with rfl
                  exact ⟨storeMetadataByte_preserves_locations _ _ _ _ hs,
                    storeMetadataByte_preserves_locations _ _ _ _ ht⟩

theorem pairedStoreRepresentationLoadMetadataByte_preserves_lengths
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (result : (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))))
    (hresult : pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice =
      some result) :
    result.1.1.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
      result.1.1.1.locations.length = metadata.locations.length ∧
      result.2.1.1.allocation.bytes.length =
        (renameMetadata resolve id metadata).allocation.bytes.length ∧
      result.2.1.1.locations.length =
        (renameMetadata resolve id metadata).locations.length := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreRepresentationLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata)
          offset (renameByte resolve byte) with
      | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : representationLoadMetadataByte sourceStore.1 offset choice with
          | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : representationLoadMetadataByte targetStore.1 offset choice with
              | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult
                  rcases hpair with rfl
                  exact ⟨storeMetadataByte_preserves_byte_length _ _ _ _ hs,
                    congrArg List.length (storeMetadataByte_preserves_locations _ _ _ _ hs),
                    storeMetadataByte_preserves_byte_length _ _ _ _ ht,
                    congrArg List.length (storeMetadataByte_preserves_locations _ _ _ _ ht)⟩

theorem pairedStoreRepresentationLoadMetadataByte_preserves_payload
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (result : (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))))
    (hresult : pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice =
      some result) :
    result.1.1.1.allocation.live = metadata.allocation.live ∧
      result.1.1.1.allocation.address = metadata.allocation.address ∧
      result.1.1.1.allocation.state = metadata.allocation.state ∧
      result.2.1.1.allocation.live =
        (renameMetadata resolve id metadata).allocation.live ∧
      result.2.1.1.allocation.address =
        (renameMetadata resolve id metadata).allocation.address ∧
      result.2.1.1.allocation.state =
        (renameMetadata resolve id metadata).allocation.state := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreRepresentationLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata)
          offset (renameByte resolve byte) with
      | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : representationLoadMetadataByte sourceStore.1 offset choice with
          | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : representationLoadMetadataByte targetStore.1 offset choice with
              | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult
                  rcases hpair with rfl
                  have hsource := hs
                  have htarget := ht
                  simp [storeMetadataByte] at hsource htarget
                  rcases hsource with ⟨_, hsourceEq⟩
                  rcases htarget with ⟨_, htargetEq⟩
                  have hslive := congrArg (fun pair => pair.1.allocation.live) hsourceEq
                  have hsaddr := congrArg (fun pair => pair.1.allocation.address) hsourceEq
                  have hsstate := congrArg (fun pair => pair.1.allocation.state) hsourceEq
                  have htlive := congrArg (fun pair => pair.1.allocation.live) htargetEq
                  have htaddr := congrArg (fun pair => pair.1.allocation.address) htargetEq
                  have htstate := congrArg (fun pair => pair.1.allocation.state) htargetEq
                  simpa [storeMetadataByte] using
                    ⟨hslive.symm, hsaddr.symm, hsstate.symm,
                      htlive.symm, htaddr.symm, htstate.symm⟩

theorem pairedStoreRepresentationLoadMetadataByte_preserves_wellFormed
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (result : (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))))
    (hresult : pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice =
      some result)
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hbytesTarget : bytesWf 0 (listSet
      (renameMetadata resolve id metadata).allocation.bytes offset
      (renameByte resolve byte)))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length)
    (hlocationsTarget :
      (renameMetadata resolve id metadata).locations.length =
        (renameMetadata resolve id metadata).allocation.bytes.length) :
    result.1.1.1.wellFormed 0 ∧ result.2.1.1.wellFormed 0 := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreRepresentationLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata)
          offset (renameByte resolve byte) with
      | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : representationLoadMetadataByte sourceStore.1 offset choice with
          | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : representationLoadMetadataByte targetStore.1 offset choice with
              | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  have hpair : ((sourceStore, sourceLoad), (targetStore, targetLoad)) = result :=
                    hresult
                  rcases hpair with rfl
                  exact ⟨storeMetadataByte_preserves_wellFormed _ _ _ _ hs
                      hbytes hlocations,
                    storeMetadataByte_preserves_wellFormed _ _ _ _ ht
                      hbytesTarget hlocationsTarget⟩

def allocationsWf : List (AllocId × Allocation Tag State) → Prop
  | [] => True
  | (id, allocation) :: rest =>
      bytesWf id allocation.bytes ∧ allocationsWf rest

def WellFormed (store : Store Tag State) : Prop :=
  allocationsWf store.allocations

theorem bytesWf_empty
    {Tag : Type} (id : AllocId) :
    bytesWf (Tag := Tag) id [] := by
  simp [bytesWf]

theorem bytesWf_uninitialized
    {Tag : Type} (id : AllocId) (rest : List (Byte Tag))
    (h : bytesWf id rest) :
    bytesWf id (.uninitialized :: rest) := by
  simpa [bytesWf] using h

theorem bytesWf_value_unprovenanced
    {Tag : Type} (id : AllocId) (bits : UInt8)
    (fragment : Option Nat) (rest : List (Byte Tag))
    (h : bytesWf id rest) :
    bytesWf id (.value bits none fragment :: rest) := by
  simpa [bytesWf] using h

theorem bytesWf_value_provenanced
    {Tag : Type} (id : AllocId) (bits : UInt8)
    (provenance : Provenance Tag) (fragment : Option Nat)
    (rest : List (Byte Tag))
    (hprovenance : provenance.allocation = id)
    (h : bytesWf id rest) :
    bytesWf id (.value bits (some provenance) fragment :: rest) := by
  simp [bytesWf, hprovenance, h]

theorem wellFormed_empty
    {Tag State : Type} :
    WellFormed ({ allocations := [], nextId := 0 } : Store Tag State) := by
  simp [WellFormed, allocationsWf]

theorem bytesWf_rename (resolve : AllocId → Nat) (id : AllocId)
    (bytes : List (Byte Tag)) (h : bytesWf id bytes) :
    bytesWf id (bytes.map (renameByte resolve)) := by
  induction bytes with
  | nil => simp [bytesWf]
  | cons byte rest ih =>
      cases byte with
      | uninitialized =>
          simp [bytesWf] at h ⊢
          exact ih h
      | value bits provenance fragment =>
          cases provenance with
          | none =>
              simp [bytesWf, renameByte] at h ⊢
              exact ih h
          | some provenance =>
              cases fragment with
              | none =>
                  simp [bytesWf, renameByte] at h ⊢
                  exact And.intro h.1 (ih h.2)
              | some fragment =>
                  simp [bytesWf, renameByte] at h ⊢
                  exact And.intro h.1 (ih h.2)

theorem bytesWf_rename_contract (resolve : AllocId → Nat) (id : AllocId)
    (bytes : List (Byte Tag)) (h : bytesWf id bytes) :
    bytesWf id (bytes.map (renameByte resolve)) ∧
      (bytes.map (renameByte resolve)).length = bytes.length := by
  exact ⟨bytesWf_rename resolve id bytes h, by simp⟩

theorem renameMetadata_preserves_wellFormed
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (h : metadata.wellFormed id) :
    (renameMetadata resolve id metadata).wellFormed id := by
  unfold AllocationMetadata.wellFormed at h ⊢
  exact ⟨bytesWf_rename resolve id metadata.allocation.bytes h.1,
    by simpa [renameMetadata] using h.2⟩

theorem renameStore_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (h : WellFormed store) : WellFormed (renameStore resolve store) := by
  cases store with
  | mk allocations nextId =>
      induction allocations with
      | nil => simp [WellFormed, renameStore, allocationsWf]
      | cons entry rest ih =>
          cases entry with
          | mk id allocation =>
              simp [WellFormed, renameStore, allocationsWf] at h ⊢
              exact ⟨bytesWf_rename resolve id allocation.bytes h.1, ih h.2⟩

def intervalOverlap (leftBase leftSize rightBase rightSize : Nat) : Bool :=
  leftBase < rightBase + rightSize && rightBase < leftBase + leftSize

theorem intervalOverlap_contract
    (leftBase leftSize rightBase rightSize : Nat) :
    intervalOverlap leftBase leftSize rightBase rightSize = true ↔
      leftBase < rightBase + rightSize ∧
      rightBase < leftBase + leftSize := by
  simp only [intervalOverlap, Bool.and_eq_true]
  constructor
  · rintro ⟨hleft, hright⟩
    exact ⟨decide_eq_true_iff.mp hleft, decide_eq_true_iff.mp hright⟩
  · rintro ⟨hleft, hright⟩
    exact ⟨decide_eq_true hleft, decide_eq_true hright⟩

def placementAllowed (store : Store Tag State) (base size : Nat) : Bool :=
  store.allocations.all fun entry =>
    let allocation := entry.2
    match allocation.live, allocation.address with
    | true, some otherBase =>
        !intervalOverlap base size otherBase allocation.bytes.length
    | _, _ => true

theorem placementAllowed_result_contract
    (store : Store Tag State) (base size : Nat) :
    placementAllowed store base size = true ↔
      ∀ entry ∈ store.allocations,
        match entry.2.live, entry.2.address with
        | true, some otherBase =>
            intervalOverlap base size otherBase entry.2.bytes.length = false
        | _, _ => True := by
  simp only [placementAllowed, List.all_eq_true]
  constructor
  · intro h entry hmem
    have hentry := h entry hmem
    cases hstate : entry.2.live <;> cases haddress : entry.2.address <;>
      simp [hstate, haddress] at hentry ⊢
    exact hentry
  · intro h entry hmem
    have hentry := h entry hmem
    cases hstate : entry.2.live <;> cases haddress : entry.2.address <;>
      simp [hstate, haddress] at hentry ⊢
    exact hentry

theorem placementAllowed_empty
    (base size : Nat) :
    placementAllowed ({ allocations := [], nextId := 0 } : Store Tag State)
      base size = true := by
  rfl

def zeroSizePlacementAllowed (store : Store Tag State) (base : Nat) : Bool := true

theorem zeroSizePlacementAllowed_contract
    (store : Store Tag State) (base : Nat) :
    zeroSizePlacementAllowed store base = true := by
  rfl

theorem zeroSizePlacementAllowed_shape
    (store : Store Tag State) (base : Nat) :
    zeroSizePlacementAllowed store base = true := by
  rfl

theorem pairedZeroSizePlacementAllowed
    (resolve : AllocId → Nat) (store : Store Tag State) (base : Nat) :
    zeroSizePlacementAllowed store base =
      zeroSizePlacementAllowed (renameStore resolve store) (resolve store.nextId) := by
  rfl

theorem pairedZeroSizePlacementAllowed_contract
    (resolve : AllocId → Nat) (store : Store Tag State) (base : Nat) :
    zeroSizePlacementAllowed store base =
      zeroSizePlacementAllowed (renameStore resolve store) (resolve store.nextId) ∧
      zeroSizePlacementAllowed store base = true := by
  exact ⟨pairedZeroSizePlacementAllowed resolve store base,
    zeroSizePlacementAllowed_contract store base⟩

def pairedPlacementAllowed (resolve : AllocId → Nat)
    (store : Store Tag State) (base size : Nat) : Bool :=
  placementAllowed store base size ==
    placementAllowed (renameStore resolve store) (resolve store.nextId) size

theorem pairedPlacementAllowed_sound (resolve : AllocId → Nat)
    (store : Store Tag State) (base size : Nat)
    (h : pairedPlacementAllowed resolve store base size) :
    placementAllowed store base size =
      placementAllowed (renameStore resolve store) (resolve store.nextId) size := by
  simpa [pairedPlacementAllowed] using h

theorem pairedPlacementAllowed_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (base size : Nat)
    (hsource : placementAllowed store base size = false)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) size = true) :
    pairedPlacementAllowed resolve store base size = false := by
  simp [pairedPlacementAllowed, hsource, htarget]

theorem pairedPlacementAllowed_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (base size : Nat)
    (hsource : placementAllowed store base size = true)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) size = false) :
    pairedPlacementAllowed resolve store base size = false := by
  simp [pairedPlacementAllowed, hsource, htarget]

theorem pairedPlacementAllowed_both_refused
    (resolve : AllocId → Nat) (store : Store Tag State)
    (base size : Nat)
    (hsource : placementAllowed store base size = false)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) size = false) :
    pairedPlacementAllowed resolve store base size = true := by
  simp [pairedPlacementAllowed, hsource, htarget]

theorem pairedPlacementAllowed_both_allowed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (base size : Nat)
    (hsource : placementAllowed store base size = true)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) size = true) :
    pairedPlacementAllowed resolve store base size = true := by
  simp [pairedPlacementAllowed, hsource, htarget]

theorem pairedPlacementAllowed_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (base size : Nat)
    (hrefusal : placementAllowed store base size = false ∧
      placementAllowed (renameStore resolve store) (resolve store.nextId) size = true ∨
      placementAllowed store base size = true ∧
      placementAllowed (renameStore resolve store) (resolve store.nextId) size = false) :
    pairedPlacementAllowed resolve store base size = false := by
  rcases hrefusal with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · simp [pairedPlacementAllowed, hsource, htarget]
  · simp [pairedPlacementAllowed, hsource, htarget]

theorem pairedPlacementAllowed_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (base size : Nat) :
    pairedPlacementAllowed resolve store base size = false ↔
      placementAllowed store base size ≠
        placementAllowed (renameStore resolve store) (resolve store.nextId) size := by
  by_cases hsource : placementAllowed store base size = true
  · by_cases htarget : placementAllowed (renameStore resolve store)
        (resolve store.nextId) size = true
    · simp [pairedPlacementAllowed, hsource, htarget]
    · have htarget' : placementAllowed (renameStore resolve store)
          (resolve store.nextId) size = false := Bool.eq_false_iff.mpr htarget
      simp [pairedPlacementAllowed, hsource, htarget']
  · have hsource' : placementAllowed store base size = false := Bool.eq_false_iff.mpr hsource
    by_cases htarget : placementAllowed (renameStore resolve store)
        (resolve store.nextId) size = true
    · simp [pairedPlacementAllowed, hsource', htarget]
    · have htarget' : placementAllowed (renameStore resolve store)
          (resolve store.nextId) size = false := Bool.eq_false_iff.mpr htarget
      simp [pairedPlacementAllowed, hsource', htarget']

def alignmentAllowed (base alignment : Nat) : Bool :=
  alignment > 0 && base % alignment == 0

theorem alignmentAllowed_success
    (base alignment : Nat)
    (hpositive : 0 < alignment)
    (hmod : base % alignment = 0) :
    alignmentAllowed base alignment = true := by
  simp [alignmentAllowed, hpositive, hmod]

theorem alignmentAllowed_refusal_remainder
    (base alignment : Nat)
    (hpositive : 0 < alignment)
    (hremainder : base % alignment ≠ 0) :
    alignmentAllowed base alignment = false := by
  simp [alignmentAllowed, hpositive, hremainder]

theorem alignmentAllowed_contract
    (base alignment : Nat) :
    alignmentAllowed base alignment = true ↔
      0 < alignment ∧ base % alignment = 0 := by
  simp only [alignmentAllowed, Bool.and_eq_true]
  constructor
  · rintro ⟨hpositive, hmod⟩
    exact ⟨decide_eq_true_iff.mp hpositive, beq_iff_eq.mp hmod⟩
  · rintro ⟨hpositive, hmod⟩
    exact ⟨decide_eq_true hpositive, beq_iff_eq.mpr hmod⟩

def pairedAlignmentAllowed (resolve : AllocId → Nat)
    (id alignment : Nat) : Bool :=
  alignmentAllowed id alignment == alignmentAllowed (resolve id) alignment

theorem pairedAlignmentAllowed_both_allowed (resolve : AllocId → Nat)
    (id alignment : Nat)
    (hsource : alignmentAllowed id alignment = true)
    (htarget : alignmentAllowed (resolve id) alignment = true) :
    pairedAlignmentAllowed resolve id alignment = true := by
  simp [pairedAlignmentAllowed, hsource, htarget]

theorem pairedAlignmentAllowed_zero
    (resolve : AllocId → Nat) (id : Nat) :
    pairedAlignmentAllowed resolve id 0 = true := by
  simp [pairedAlignmentAllowed, alignmentAllowed]

theorem pairedAlignmentAllowed_sound (resolve : AllocId → Nat)
    (id alignment : Nat)
    (h : pairedAlignmentAllowed resolve id alignment = true) :
    alignmentAllowed id alignment = alignmentAllowed (resolve id) alignment := by
  simpa [pairedAlignmentAllowed] using h

theorem pairedAlignmentAllowed_both_refused (resolve : AllocId → Nat)
    (id alignment : Nat)
    (hsource : alignmentAllowed id alignment = false)
    (htarget : alignmentAllowed (resolve id) alignment = false) :
    pairedAlignmentAllowed resolve id alignment = true := by
  simp [pairedAlignmentAllowed, hsource, htarget]

theorem pairedAlignmentAllowed_refusal_source (resolve : AllocId → Nat)
    (id alignment : Nat)
    (hsource : alignmentAllowed id alignment = false)
    (htarget : alignmentAllowed (resolve id) alignment = true) :
    pairedAlignmentAllowed resolve id alignment = false := by
  simp [pairedAlignmentAllowed, hsource, htarget]

theorem pairedAlignmentAllowed_refusal_target (resolve : AllocId → Nat)
    (id alignment : Nat)
    (hsource : alignmentAllowed id alignment = true)
    (htarget : alignmentAllowed (resolve id) alignment = false) :
    pairedAlignmentAllowed resolve id alignment = false := by
  simp [pairedAlignmentAllowed, hsource, htarget]

theorem pairedAlignmentAllowed_refusal (resolve : AllocId → Nat)
    (id alignment : Nat)
    (hrefusal : alignmentAllowed id alignment = false ∧
      alignmentAllowed (resolve id) alignment = true ∨
      alignmentAllowed id alignment = true ∧
      alignmentAllowed (resolve id) alignment = false) :
    pairedAlignmentAllowed resolve id alignment = false := by
  rcases hrefusal with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · simp [pairedAlignmentAllowed, hsource, htarget]
  · simp [pairedAlignmentAllowed, hsource, htarget]

theorem pairedAlignmentAllowed_failure_contract (resolve : AllocId → Nat)
    (id alignment : Nat) :
    pairedAlignmentAllowed resolve id alignment = false ↔
      alignmentAllowed id alignment ≠ alignmentAllowed (resolve id) alignment := by
  by_cases hsource : alignmentAllowed id alignment = true
  · by_cases htarget : alignmentAllowed (resolve id) alignment = true
    · simp [pairedAlignmentAllowed, hsource, htarget]
    · have htarget' : alignmentAllowed (resolve id) alignment = false :=
          Bool.eq_false_iff.mpr htarget
      simp [pairedAlignmentAllowed, hsource, htarget']
  · have hsource' : alignmentAllowed id alignment = false := Bool.eq_false_iff.mpr hsource
    by_cases htarget : alignmentAllowed (resolve id) alignment = true
    · simp [pairedAlignmentAllowed, hsource', htarget]
    · have htarget' : alignmentAllowed (resolve id) alignment = false :=
          Bool.eq_false_iff.mpr htarget
      simp [pairedAlignmentAllowed, hsource', htarget']

def alignmentComposition (first second : AllocId → Nat)
    (id alignment : Nat) : Bool :=
  alignmentAllowed (first id) alignment == alignmentAllowed (second id) alignment

theorem alignmentComposition_both_allowed (first second : AllocId → Nat)
    (id alignment : Nat)
    (hfirst : alignmentAllowed (first id) alignment = true)
    (hsecond : alignmentAllowed (second id) alignment = true) :
    alignmentComposition first second id alignment = true := by
  simp [alignmentComposition, hfirst, hsecond]

theorem alignmentComposition_both_refused (first second : AllocId → Nat)
    (id alignment : Nat)
    (hfirst : alignmentAllowed (first id) alignment = false)
    (hsecond : alignmentAllowed (second id) alignment = false) :
    alignmentComposition first second id alignment = true := by
  simp [alignmentComposition, hfirst, hsecond]

theorem alignmentComposition_refusal_first (first second : AllocId → Nat)
    (id alignment : Nat)
    (hfirst : alignmentAllowed (first id) alignment = false)
    (hsecond : alignmentAllowed (second id) alignment = true) :
    alignmentComposition first second id alignment = false := by
  simp [alignmentComposition, hfirst, hsecond]

theorem alignmentComposition_refusal_second (first second : AllocId → Nat)
    (id alignment : Nat)
    (hfirst : alignmentAllowed (first id) alignment = true)
    (hsecond : alignmentAllowed (second id) alignment = false) :
    alignmentComposition first second id alignment = false := by
  simp [alignmentComposition, hfirst, hsecond]

theorem alignmentComposition_refusal (first second : AllocId → Nat)
    (id alignment : Nat)
    (hrefusal : alignmentAllowed (first id) alignment = false ∧
      alignmentAllowed (second id) alignment = true ∨
      alignmentAllowed (first id) alignment = true ∧
      alignmentAllowed (second id) alignment = false) :
    alignmentComposition first second id alignment = false := by
  rcases hrefusal with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · simp [alignmentComposition, hfirst, hsecond]
  · simp [alignmentComposition, hfirst, hsecond]

theorem alignmentComposition_sound (first second : AllocId → Nat)
    (id alignment : Nat)
    (h : alignmentComposition first second id alignment = true) :
    alignmentAllowed (first id) alignment = alignmentAllowed (second id) alignment := by
  simpa [alignmentComposition] using h

theorem alignmentComposition_contract (first second : AllocId → Nat)
    (id alignment : Nat) :
    alignmentComposition first second id alignment = true ↔
      alignmentAllowed (first id) alignment =
        alignmentAllowed (second id) alignment := by
  simp [alignmentComposition, beq_iff_eq]

theorem alignmentComposition_zero
    (first second : AllocId → Nat) (id : Nat) :
    alignmentComposition first second id 0 = true := by
  simp [alignmentComposition, alignmentAllowed]

theorem zeroAlignmentRefused (base : Nat) :
    alignmentAllowed base 0 = false := by
  simp [alignmentAllowed]


inductive EqualityChoice where
  | equal
  | unequal
deriving Repr, BEq

def pointerEqual (left right : Pointer Tag) (choice : EqualityChoice) : Bool :=
  match choice with
  | .equal => left.address == right.address
  | .unequal => false

theorem pointerEqual_choice (left right : Pointer Tag) :
    pointerEqual left right .equal = (left.address == right.address) := by
  rfl

theorem pointerEqual_unequal_choice (left right : Pointer Tag) :
    pointerEqual left right .unequal = false := by
  rfl

theorem pointerEqual_contract (left right : Pointer Tag) (choice : EqualityChoice) :
    match choice with
    | .equal =>
        pointerEqual left right choice = (left.address == right.address)
    | .unequal => pointerEqual left right choice = false := by
  cases choice <;> rfl

def pairedPointerEqual (resolve : AllocId → Nat)
    (left right : Pointer Tag) (choice : EqualityChoice) : Bool :=
  pointerEqual (renamePointer resolve left) (renamePointer resolve right) choice =
    pointerEqual left right choice

theorem pairedPointerEqual_self (resolve : AllocId → Nat)
    (pointer : Pointer Tag) (choice : EqualityChoice) :
    pairedPointerEqual resolve pointer pointer choice := by
  simp [pairedPointerEqual, pointerEqual]

theorem pairedPointerEqual_unequal_choice
    (resolve : AllocId → Nat) (left right : Pointer Tag) :
    pairedPointerEqual resolve left right .unequal = true := by
  simp [pairedPointerEqual, pointerEqual]

theorem pairedPointerEqual_equal_choice_agrees
    (resolve : AllocId → Nat) (left right : Pointer Tag)
    (hleft : (left.address == right.address) = true)
    (hright : ((renamePointer resolve left).address ==
      (renamePointer resolve right).address) = true) :
    pairedPointerEqual resolve left right .equal = true := by
  simp [pairedPointerEqual, pointerEqual, hleft, hright]

theorem pairedPointerEqual_equal_choice_unprovenanced
    (resolve : AllocId → Nat) (left right : Pointer Tag)
    (hleft : left.provenance = none)
    (hright : right.provenance = none) :
    pairedPointerEqual resolve left right .equal = true := by
  cases left with
  | mk leftProvenance leftAddress =>
      cases right with
      | mk rightProvenance rightAddress =>
          cases hleft' : leftProvenance with
          | none =>
              cases hright' : rightProvenance with
              | none =>
                  simp [pairedPointerEqual, pointerEqual, renamePointer,
                    hleft', hright']
              | some p => simp [hright'] at hright
          | some p => simp [hleft'] at hleft

theorem pairedPointerEqual_equal_choice_same_pointer
    (resolve : AllocId → Nat) (left right : Pointer Tag)
    (haddress : left.address = right.address)
    (hprovenance : left.provenance = right.provenance) :
    pairedPointerEqual resolve left right .equal = true := by
  cases left with
  | mk leftProvenance leftAddress =>
      cases right with
      | mk rightProvenance rightAddress =>
          have haddress' : leftAddress = rightAddress := by simpa using haddress
          have hprovenance' : leftProvenance = rightProvenance := by
            simpa using hprovenance
          cases haddress'
          cases hprovenance'
          exact pairedPointerEqual_self resolve
            { provenance := leftProvenance, address := leftAddress } .equal

theorem pairedPointerEqual_equal_choice_both_refused
    (resolve : AllocId → Nat) (left right : Pointer Tag)
    (hleft : (left.address == right.address) = false)
    (hright : ((renamePointer resolve left).address ==
      (renamePointer resolve right).address) = false) :
    pairedPointerEqual resolve left right .equal = true := by
  simp [pairedPointerEqual, pointerEqual, hleft, hright]

theorem pairedPointerEqual_equal_choice_refusal_left
    (resolve : AllocId → Nat) (left right : Pointer Tag)
    (hleft : (left.address == right.address) = false)
    (hright : ((renamePointer resolve left).address ==
      (renamePointer resolve right).address) = true) :
    pairedPointerEqual resolve left right .equal = false := by
  simp [pairedPointerEqual, pointerEqual, hleft, hright]

theorem pairedPointerEqual_equal_choice_refusal_right
    (resolve : AllocId → Nat) (left right : Pointer Tag)
    (hleft : (left.address == right.address) = true)
    (hright : ((renamePointer resolve left).address ==
      (renamePointer resolve right).address) = false) :
    pairedPointerEqual resolve left right .equal = false := by
  simp [pairedPointerEqual, pointerEqual, hleft, hright]

theorem pairedPointerEqual_equal_choice_refusal
    (resolve : AllocId → Nat) (left right : Pointer Tag)
    (hrefusal :
      ((left.address == right.address) = false ∧
        ((renamePointer resolve left).address ==
          (renamePointer resolve right).address) = true) ∨
      ((left.address == right.address) = true ∧
        ((renamePointer resolve left).address ==
          (renamePointer resolve right).address) = false)) :
    pairedPointerEqual resolve left right .equal = false := by
  rcases hrefusal with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · simp [pairedPointerEqual, pointerEqual, hleft, hright]
  · simp [pairedPointerEqual, pointerEqual, hleft, hright]

theorem pairedPointerEqual_equal_choice_failure_contract
    (resolve : AllocId → Nat) (left right : Pointer Tag) :
    pairedPointerEqual resolve left right .equal = false ↔
      ((left.address == right.address) ≠
        ((renamePointer resolve left).address ==
          (renamePointer resolve right).address)) := by
  by_cases hleft : (left.address == right.address) = true
  · by_cases hright : ((renamePointer resolve left).address ==
        (renamePointer resolve right).address) = true
    · simp [pairedPointerEqual, pointerEqual, hleft, hright]
    · simp [pairedPointerEqual, pointerEqual, hleft, hright]
  · by_cases hright : ((renamePointer resolve left).address ==
        (renamePointer resolve right).address) = true
    · simp [pairedPointerEqual, pointerEqual, hleft, hright]
    · simp [pairedPointerEqual, pointerEqual, hleft, hright]

theorem pairedPointerEqual_sound
    (resolve : AllocId → Nat) (left right : Pointer Tag)
    (choice : EqualityChoice)
    (h : pairedPointerEqual resolve left right choice = true) :
    pointerEqual (renamePointer resolve left) (renamePointer resolve right) choice =
      pointerEqual left right choice := by
  simpa [pairedPointerEqual] using h

inductive OffsetFault where
  | outOfBounds
  | alignment
deriving Repr, BEq

structure Exposure where
  exposed : Bool
deriving Repr, BEq

def expose (state : Exposure) : Exposure := { exposed := true }

theorem expose_idempotent (state : Exposure) :
    expose (expose state) = expose state := by
  rfl

theorem expose_contract (state : Exposure) :
    (expose state).exposed = true ∧
      expose (expose state) = expose state := by
  exact ⟨rfl, expose_idempotent state⟩

def renameExposure (resolve : AllocId → Nat) (state : Exposure) : Exposure := state

theorem renameExposure_identity (resolve : AllocId → Nat) (state : Exposure) :
    renameExposure resolve state = state := by
  rfl

theorem renameExposure_contract (resolve : AllocId → Nat) (state : Exposure) :
    renameExposure resolve state = state ∧
      (renameExposure resolve state).exposed = state.exposed := by
  exact ⟨renameExposure_identity resolve state, rfl⟩

theorem expose_renameExposure (resolve : AllocId → Nat) (state : Exposure) :
    renameExposure resolve (expose state) = expose (renameExposure resolve state) := by
  rfl

theorem expose_renameExposure_exposed
    (resolve : AllocId → Nat) (state : Exposure) :
    (renameExposure resolve (expose state)).exposed = true := by
  rfl

structure ReplayPlacement where
  allocation : AllocId
  base : Nat
  size : Nat
  exposed : Bool
deriving Repr, BEq

inductive ReplayEvent where
  | io (operation channel data : String)
  | volatileRead (data : List UInt8)
  | volatileWrite (data : List UInt8)
deriving Repr, BEq

def replayStdout (events : List ReplayEvent) : String :=
  events.foldl (fun output event =>
    match event with
    | .io _ "stdout" data => output ++ data
    | _ => output) ""

def renameReplayEvent (resolve : AllocId → Nat) : ReplayEvent → ReplayEvent
  | .io operation channel data => .io operation channel data
  | .volatileRead data => .volatileRead data
  | .volatileWrite data => .volatileWrite data

theorem renameReplayEvent_identity (resolve : AllocId → Nat) (event : ReplayEvent) :
    renameReplayEvent resolve event = event := by
  cases event <;> rfl

def renameReplayEvents (resolve : AllocId → Nat) (events : List ReplayEvent) :
    List ReplayEvent := events.map (renameReplayEvent resolve)

theorem renameReplayEvents_identity (resolve : AllocId → Nat)
    (events : List ReplayEvent) : renameReplayEvents resolve events = events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [renameReplayEvents, renameReplayEvent]
      all_goals simpa [renameReplayEvents] using ih

theorem renameReplayEvents_contract
    (resolve : AllocId → Nat) (events : List ReplayEvent) :
    renameReplayEvents resolve events = events ∧
      (renameReplayEvents resolve events).length = events.length := by
  exact ⟨renameReplayEvents_identity resolve events,
    by simp [renameReplayEvents]⟩

theorem renameReplayEvents_idempotent
    (resolve : AllocId → Nat) (events : List ReplayEvent) :
    renameReplayEvents resolve (renameReplayEvents resolve events) =
      renameReplayEvents resolve events := by
  rw [renameReplayEvents_identity resolve (renameReplayEvents resolve events)]

theorem renameReplayEvents_comp
    (first second : AllocId → Nat) (events : List ReplayEvent) :
    renameReplayEvents second (renameReplayEvents first events) =
      renameReplayEvents second events := by
  rw [renameReplayEvents_identity first events]

theorem renameReplayEvents_preserves_stdout
    (resolve : AllocId → Nat) (events : List ReplayEvent) :
    replayStdout (renameReplayEvents resolve events) = replayStdout events := by
  rw [renameReplayEvents_identity resolve events]

inductive ReplayEnding where
  | exit (status : Int)
  | signal (number : Nat)
  | exhausted
  | diverges
  | ub (clause operand : String)
  | refused (name : String)
deriving Repr, BEq

structure ReplayObservation where
  stdout : String
  ending : ReplayEnding
deriving Repr, BEq

structure ReplayFixture where
  sourceHash : String
  compilerVersion : String
  targetTriple : String
  placements : List ReplayPlacement
  events : List ReplayEvent
  ending : ReplayEnding
deriving Repr

def renameReplayPlacement (resolve : AllocId → Nat)
    (placement : ReplayPlacement) : ReplayPlacement :=
  { placement with base := resolve placement.allocation }

theorem renameReplayPlacement_shape
    (resolve : AllocId → Nat) (placement : ReplayPlacement) :
    (renameReplayPlacement resolve placement).allocation = placement.allocation ∧
      (renameReplayPlacement resolve placement).base = resolve placement.allocation ∧
      (renameReplayPlacement resolve placement).size = placement.size ∧
      (renameReplayPlacement resolve placement).exposed = placement.exposed := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem renameReplayPlacement_contract
    (resolve : AllocId → Nat) (placement : ReplayPlacement) :
    (renameReplayPlacement resolve placement).allocation = placement.allocation ∧
      (renameReplayPlacement resolve placement).base = resolve placement.allocation ∧
      (renameReplayPlacement resolve placement).size = placement.size ∧
      (renameReplayPlacement resolve placement).exposed = placement.exposed := by
  exact renameReplayPlacement_shape resolve placement

theorem renameReplayPlacement_idempotent
    (resolve : AllocId → Nat) (placement : ReplayPlacement) :
    renameReplayPlacement resolve (renameReplayPlacement resolve placement) =
      renameReplayPlacement resolve placement := by
  cases placement with
  | mk allocation base size exposed => rfl

theorem renameReplayPlacement_comp
    (first second : AllocId → Nat) (placement : ReplayPlacement) :
    renameReplayPlacement second (renameReplayPlacement first placement) =
      renameReplayPlacement second placement := by
  cases placement with
  | mk allocation base size exposed => rfl

def renameReplayFixture (resolve : AllocId → Nat)
    (fixture : ReplayFixture) : ReplayFixture :=
  { fixture with
    placements := fixture.placements.map (renameReplayPlacement resolve)
    events := renameReplayEvents resolve fixture.events }

def replayObservation (fixture : ReplayFixture) : ReplayObservation :=
  { stdout := replayStdout fixture.events
    ending := fixture.ending }

theorem renameReplayFixture_preserves_metadata
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).sourceHash = fixture.sourceHash ∧
      (renameReplayFixture resolve fixture).compilerVersion = fixture.compilerVersion ∧
      (renameReplayFixture resolve fixture).targetTriple = fixture.targetTriple ∧
      (renameReplayFixture resolve fixture).ending = fixture.ending := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem renameReplayFixture_events
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).events =
      fixture.events.map (renameReplayEvent resolve) := by
  rfl

theorem renameReplayFixture_events_contract
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).events =
        fixture.events.map (renameReplayEvent resolve) ∧
      (renameReplayFixture resolve fixture).events.length = fixture.events.length := by
  exact ⟨renameReplayFixture_events resolve fixture,
    by simp [renameReplayFixture, renameReplayEvents]⟩

theorem renameReplayFixture_placements
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).placements =
      fixture.placements.map (renameReplayPlacement resolve) := by
  rfl

theorem renameReplayFixture_placements_contract
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).placements =
        fixture.placements.map (renameReplayPlacement resolve) ∧
      (renameReplayFixture resolve fixture).placements.length =
        fixture.placements.length := by
  exact ⟨renameReplayFixture_placements resolve fixture,
    by simp [renameReplayFixture, renameReplayPlacement]⟩

theorem renameReplayFixture_placement_count
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).placements.length = fixture.placements.length := by
  simp [renameReplayFixture]

theorem renameReplayFixture_event_count
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).events.length = fixture.events.length := by
  simp [renameReplayFixture, renameReplayEvents]

theorem renameReplayFixture_preserves_stdout
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    replayStdout (renameReplayFixture resolve fixture).events =
      replayStdout fixture.events := by
  simpa [renameReplayFixture] using
    renameReplayEvents_preserves_stdout resolve fixture.events

theorem renameReplayFixture_preserves_observation
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    replayObservation (renameReplayFixture resolve fixture) =
      replayObservation fixture := by
  cases fixture with
  | mk sourceHash compilerVersion targetTriple placements events ending =>
      simp [replayObservation, renameReplayFixture, replayStdout,
        renameReplayEvents_identity]

theorem renameReplayFixture_contract
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).sourceHash = fixture.sourceHash ∧
      (renameReplayFixture resolve fixture).compilerVersion = fixture.compilerVersion ∧
      (renameReplayFixture resolve fixture).targetTriple = fixture.targetTriple ∧
      (renameReplayFixture resolve fixture).ending = fixture.ending ∧
      (renameReplayFixture resolve fixture).placements.length = fixture.placements.length ∧
      (renameReplayFixture resolve fixture).events.length = fixture.events.length := by
  rcases renameReplayFixture_preserves_metadata resolve fixture with
    ⟨hsource, hcompiler, htriple, hending⟩
  exact ⟨hsource, hcompiler, htriple, hending,
    renameReplayFixture_placement_count resolve fixture,
    renameReplayFixture_event_count resolve fixture⟩

def ReplayFixture.wellFormed (fixture : ReplayFixture) : Prop :=
  fixture.sourceHash ≠ "" ∧ fixture.compilerVersion ≠ "" ∧
    fixture.targetTriple ≠ "" ∧
    fixture.placements.Pairwise (fun left right =>
      left.base + left.size ≤ right.base ∨ right.base + right.size ≤ left.base)

inductive Recovery (Tag : Type) where
  | recovered (pointer : Pointer Tag)
  | empty (address : Nat)
  | ambiguousOnePastAdjacent
  | noLiveAllocation
deriving Repr, BEq

def recoverAddress (address : Nat) (live : List (AllocId × Nat × Nat × Tag)) : Recovery Tag :=
  match live.find? (fun entry => entry.2.1 ≤ address && address < entry.2.2.1) with
  | some entry => .recovered { provenance := some { allocation := entry.1, tag := entry.2.2.2 }, address := address }
  | none => .empty address

theorem recoverAddress_found
    (address : Nat) (live : List (AllocId × Nat × Nat × Tag))
    (entry : AllocId × Nat × Nat × Tag)
    (hfound : live.find? (fun candidate =>
      candidate.2.1 ≤ address && address < candidate.2.2.1) = some entry) :
    recoverAddress address live =
      .recovered { provenance := some { allocation := entry.1, tag := entry.2.2.2 },
                   address := address } := by
  simp [recoverAddress, hfound]

theorem recoverAddress_no_live_allocation
    (address : Nat) (live : List (AllocId × Nat × Nat × Tag))
    (hnone : live.find? (fun candidate =>
      candidate.2.1 ≤ address && address < candidate.2.2.1) = none) :
    recoverAddress address live = .empty address := by
  simp [recoverAddress, hnone]

theorem recoverAddress_result_contract
    (address : Nat) (live : List (AllocId × Nat × Nat × Tag))
    (result : Recovery Tag)
    (hresult : recoverAddress address live = result) :
    (∃ entry,
      live.find? (fun candidate =>
        candidate.2.1 ≤ address && address < candidate.2.2.1) = some entry ∧
      result = .recovered
        { provenance := some { allocation := entry.1, tag := entry.2.2.2 },
          address := address }) ∨
    (live.find? (fun candidate =>
        candidate.2.1 ≤ address && address < candidate.2.2.1) = none ∧
      result = .empty address) := by
  cases hfind : live.find? (fun candidate =>
      candidate.2.1 ≤ address && address < candidate.2.2.1) with
  | some entry =>
      left
      refine ⟨entry, rfl, ?_⟩
      simpa [recoverAddress, hfind] using hresult.symm
  | none =>
      right
      refine ⟨rfl, ?_⟩
      simpa [recoverAddress, hfind] using hresult.symm

def renameLiveRegion (resolve : AllocId → Nat)
    (entry : AllocId × Nat × Nat × Tag) : AllocId × Nat × Nat × Tag :=
  (entry.1, resolve entry.1, resolve entry.1 + (entry.2.2.1 - entry.2.1), entry.2.2.2)

theorem renameLiveRegion_shape
    (resolve : AllocId → Nat) (entry : AllocId × Nat × Nat × Tag) :
    (renameLiveRegion resolve entry).1 = entry.1 ∧
      (renameLiveRegion resolve entry).2.2.2 = entry.2.2.2 := by
  exact ⟨rfl, rfl⟩

theorem renameLiveRegion_base_shape
    (resolve : AllocId → Nat) (entry : AllocId × Nat × Nat × Tag) :
    (renameLiveRegion resolve entry).2.1 = resolve entry.1 := by
  rfl

theorem renameLiveRegion_end_shape
    (resolve : AllocId → Nat) (entry : AllocId × Nat × Nat × Tag) :
    (renameLiveRegion resolve entry).2.2.1 =
      resolve entry.1 + (entry.2.2.1 - entry.2.1) := by
  rfl

theorem renameLiveRegion_size_shape
    (resolve : AllocId → Nat) (entry : AllocId × Nat × Nat × Tag) :
    (renameLiveRegion resolve entry).2.2.1 -
        (renameLiveRegion resolve entry).2.1 = entry.2.2.1 - entry.2.1 := by
  simp [renameLiveRegion]

theorem renameLiveRegion_contract
    (resolve : AllocId → Nat) (entry : AllocId × Nat × Nat × Tag) :
    (renameLiveRegion resolve entry).1 = entry.1 ∧
      (renameLiveRegion resolve entry).2.1 = resolve entry.1 ∧
      (renameLiveRegion resolve entry).2.2.1 =
        resolve entry.1 + (entry.2.2.1 - entry.2.1) ∧
      (renameLiveRegion resolve entry).2.2.2 = entry.2.2.2 ∧
      (renameLiveRegion resolve entry).2.2.1 -
          (renameLiveRegion resolve entry).2.1 = entry.2.2.1 - entry.2.1 := by
  exact ⟨renameLiveRegion_shape resolve entry |>.1,
    renameLiveRegion_base_shape resolve entry,
    renameLiveRegion_end_shape resolve entry,
    renameLiveRegion_shape resolve entry |>.2,
    renameLiveRegion_size_shape resolve entry⟩

theorem renameLiveRegion_comp
    (first second : AllocId → Nat)
    (entry : AllocId × Nat × Nat × Tag) :
    renameLiveRegion second (renameLiveRegion first entry) =
      renameLiveRegion second entry := by
  cases entry with
  | mk id rest =>
      cases rest with
      | mk base rest =>
          cases rest with
          | mk ending tag =>
              simp [renameLiveRegion]

def renameRecovery (resolve : AllocId → Nat) : Recovery Tag → Recovery Tag
  | .recovered pointer => .recovered (renamePointer resolve pointer)
  | .empty address => .empty address
  | .ambiguousOnePastAdjacent => .ambiguousOnePastAdjacent
  | .noLiveAllocation => .noLiveAllocation

theorem renameRecovery_empty_shape
    {Tag : Type} (resolve : AllocId → Nat) (address : Nat) :
    renameRecovery (Tag := Tag) resolve (.empty address) =
      (.empty address : Recovery Tag) := by
  rfl

theorem renameRecovery_ambiguous_shape
    (resolve : AllocId → Nat) :
    renameRecovery (Tag := Tag) resolve .ambiguousOnePastAdjacent =
      .ambiguousOnePastAdjacent := by
  rfl

theorem renameRecovery_no_live_shape
    (resolve : AllocId → Nat) :
    renameRecovery (Tag := Tag) resolve .noLiveAllocation =
      .noLiveAllocation := by
  rfl

theorem renameRecovery_idempotent
    (resolve : AllocId → Nat) (recovery : Recovery Tag) :
    renameRecovery resolve (renameRecovery resolve recovery) =
      renameRecovery resolve recovery := by
  cases recovery with
  | recovered region => simp [renameRecovery, renamePointer_idempotent]
  | empty address => rfl
  | ambiguousOnePastAdjacent => rfl
  | noLiveAllocation => rfl

theorem renameRecovery_comp
    (first second : AllocId → Nat) (recovery : Recovery Tag) :
    renameRecovery second (renameRecovery first recovery) =
      renameRecovery second recovery := by
  cases recovery with
  | recovered region => simp [renameRecovery, renamePointer_comp]
  | empty address => rfl
  | ambiguousOnePastAdjacent => rfl
  | noLiveAllocation => rfl

theorem renameRecovery_kind_preserved
    (resolve : AllocId → Nat) (recovery : Recovery Tag) :
    match recovery, renameRecovery resolve recovery with
    | .recovered _, .recovered _ => True
    | .empty _, .empty _ => True
    | .ambiguousOnePastAdjacent, .ambiguousOnePastAdjacent => True
    | .noLiveAllocation, .noLiveAllocation => True
    | _, _ => False := by
  cases recovery <;> simp [renameRecovery]

theorem renameRecovery_contract
    (resolve : AllocId → Nat) (recovery : Recovery Tag) :
    match recovery with
    | .recovered pointer =>
        renameRecovery resolve recovery = .recovered (renamePointer resolve pointer)
    | .empty address => renameRecovery resolve recovery = .empty address
    | .ambiguousOnePastAdjacent =>
        renameRecovery resolve recovery = .ambiguousOnePastAdjacent
    | .noLiveAllocation => renameRecovery resolve recovery = .noLiveAllocation := by
  cases recovery <;> rfl

def pairedRecoverAddress (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag)) : Bool :=
  match recoverAddress address live,
    recoverAddress address (live.map (renameLiveRegion resolve)) with
  | .recovered _, .recovered _ => true
  | .empty _, .empty _ => true
  | _, _ => false

theorem pairedRecoverAddress_both_recovered
    (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag))
    (source target : Pointer Tag)
    (hsource : recoverAddress address live = .recovered source)
    (htarget : recoverAddress address (live.map (renameLiveRegion resolve)) =
      .recovered target) :
    pairedRecoverAddress resolve address live = true := by
  simp [pairedRecoverAddress, hsource, htarget]

theorem pairedRecoverAddress_both_empty
    (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag))
    (hsource : recoverAddress address live = .empty source)
    (htarget : recoverAddress address (live.map (renameLiveRegion resolve)) =
      .empty target) :
    pairedRecoverAddress resolve address live = true := by
  simp [pairedRecoverAddress, hsource, htarget]

theorem pairedRecoverAddress_empty_live
    {Tag : Type} (resolve : AllocId → Nat) (address : Nat) :
    pairedRecoverAddress (Tag := Tag) resolve address [] = true := by
  simp [pairedRecoverAddress, recoverAddress]

theorem pairedRecoverAddress_empty_recovered_refusal
    (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag))
    (source : Nat) (target : Pointer Tag)
    (hsource : recoverAddress address live = .empty source)
    (htarget : recoverAddress address (live.map (renameLiveRegion resolve)) =
      .recovered target) :
    pairedRecoverAddress resolve address live = false := by
  simp [pairedRecoverAddress, hsource, htarget]

theorem pairedRecoverAddress_recovered_empty_refusal
    (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag))
    (source : Pointer Tag) (target : Nat)
    (hsource : recoverAddress address live = .recovered source)
    (htarget : recoverAddress address (live.map (renameLiveRegion resolve)) =
      .empty target) :
    pairedRecoverAddress resolve address live = false := by
  simp [pairedRecoverAddress, hsource, htarget]

theorem pairedRecoverAddress_refusal
    (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag))
    (hrefusal :
      (∃ source target,
        recoverAddress address live = .empty source ∧
        recoverAddress address (live.map (renameLiveRegion resolve)) =
          .recovered target) ∨
      (∃ source target,
        recoverAddress address live = .recovered source ∧
        recoverAddress address (live.map (renameLiveRegion resolve)) =
          .empty target)) :
    pairedRecoverAddress resolve address live = false := by
  rcases hrefusal with ⟨source, target, hsource, htarget⟩ |
    ⟨source, target, hsource, htarget⟩
  · simp [pairedRecoverAddress, hsource, htarget]
  · simp [pairedRecoverAddress, hsource, htarget]

theorem pairedRecoverAddress_failure_contract
    (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag)) :
    pairedRecoverAddress resolve address live = false ↔
      match recoverAddress address live,
        recoverAddress address (live.map (renameLiveRegion resolve)) with
      | .recovered _, .recovered _ => False
      | .empty _, .empty _ => False
      | _, _ => True := by
  cases hs : recoverAddress address live <;>
    cases ht : recoverAddress address (live.map (renameLiveRegion resolve)) <;>
      simp [pairedRecoverAddress, hs, ht]

theorem pairedRecoverAddress_sound
    (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag))
    (h : pairedRecoverAddress resolve address live = true) :
    (∃ source target,
      recoverAddress address live = .recovered source ∧
      recoverAddress address (live.map (renameLiveRegion resolve)) = .recovered target) ∨
    (∃ source target,
      recoverAddress address live = .empty source ∧
      recoverAddress address (live.map (renameLiveRegion resolve)) = .empty target) := by
  cases hs : recoverAddress address live with
  | recovered source =>
      cases ht : recoverAddress address (live.map (renameLiveRegion resolve)) with
      | recovered target => exact Or.inl ⟨source, target, rfl, rfl⟩
      | empty target => simp [pairedRecoverAddress, hs, ht] at h
      | ambiguousOnePastAdjacent => simp [pairedRecoverAddress, hs, ht] at h
      | noLiveAllocation => simp [pairedRecoverAddress, hs, ht] at h
  | empty source =>
      cases ht : recoverAddress address (live.map (renameLiveRegion resolve)) with
      | recovered target => simp [pairedRecoverAddress, hs, ht] at h
      | empty target => exact Or.inr ⟨source, target, rfl, rfl⟩
      | ambiguousOnePastAdjacent => simp [pairedRecoverAddress, hs, ht] at h
      | noLiveAllocation => simp [pairedRecoverAddress, hs, ht] at h
  | ambiguousOnePastAdjacent => simp [pairedRecoverAddress, hs] at h
  | noLiveAllocation => simp [pairedRecoverAddress, hs] at h

def offsetPointer (pointer : Pointer Tag) (elementSize : Nat) (delta : Int)
    (bound : Nat) : Except OffsetFault (Pointer Tag) :=
  if elementSize == 0 then .error .alignment
  else
    let magnitude := Int.natAbs delta * elementSize
    let address := if delta < 0 then pointer.address - magnitude else pointer.address + magnitude
    if address > bound then .error .outOfBounds else .ok { pointer with address := address }

theorem offsetPointer_zero_element_size
    (pointer : Pointer Tag) (delta : Int) (bound : Nat) :
    offsetPointer pointer 0 delta bound = .error .alignment := by
  simp [offsetPointer]

theorem offsetPointer_success_nonnegative
    (pointer : Pointer Tag) (elementSize : Nat) (delta : Int) (bound : Nat)
    (hsize : elementSize ≠ 0) (hdelta : 0 ≤ delta)
    (hbound : pointer.address + Int.natAbs delta * elementSize ≤ bound) :
    offsetPointer pointer elementSize delta bound =
      .ok { pointer with address := pointer.address + Int.natAbs delta * elementSize } := by
  have hneg : ¬ delta < 0 := by omega
  simp [offsetPointer, hsize, hneg, hbound]

theorem offsetPointer_outOfBounds_nonnegative
    (pointer : Pointer Tag) (elementSize : Nat) (delta : Int) (bound : Nat)
    (hsize : elementSize ≠ 0) (hdelta : 0 ≤ delta)
    (hbound : bound < pointer.address + Int.natAbs delta * elementSize) :
    offsetPointer pointer elementSize delta bound = .error .outOfBounds := by
  have hneg : ¬ delta < 0 := by omega
  simp [offsetPointer, hsize, hneg, hbound]

theorem offsetPointer_success_negative
    (pointer : Pointer Tag) (elementSize : Nat) (delta : Int) (bound : Nat)
    (hsize : elementSize ≠ 0) (hdelta : delta < 0)
    (hwithin : Int.natAbs delta * elementSize ≤ pointer.address)
    (hbound : pointer.address - Int.natAbs delta * elementSize ≤ bound) :
    offsetPointer pointer elementSize delta bound =
      .ok { pointer with
        address := pointer.address - Int.natAbs delta * elementSize } := by
  simp [offsetPointer, hsize, hdelta, hwithin, hbound]

theorem offsetPointer_negative_underflow
    (pointer : Pointer Tag) (elementSize : Nat) (delta : Int) (bound : Nat)
    (hsize : elementSize ≠ 0) (hdelta : delta < 0)
    (hunderflow : pointer.address < Int.natAbs delta * elementSize) :
    offsetPointer pointer elementSize delta bound =
      .ok { pointer with address := 0 } := by
  have hzero : pointer.address - Int.natAbs delta * elementSize = 0 :=
    Nat.sub_eq_zero_of_le (Nat.le_of_lt hunderflow)
  simp [offsetPointer, hsize, hdelta, hzero]

theorem offsetPointer_result_contract
    (pointer : Pointer Tag) (elementSize : Nat) (delta : Int) (bound : Nat)
    (result : Except OffsetFault (Pointer Tag))
    (hresult : offsetPointer pointer elementSize delta bound = result) :
    result =
      if elementSize == 0 then
        .error .alignment
      else
        let magnitude := Int.natAbs delta * elementSize
        let address := if delta < 0 then
          pointer.address - magnitude
        else
          pointer.address + magnitude
        if address > bound then
          .error .outOfBounds
        else
          .ok { pointer with address := address } := by
  simpa [offsetPointer] using hresult.symm

def renameOffsetResult (resolve : AllocId → Nat) :
    Except OffsetFault (Pointer Tag) → Except OffsetFault (Pointer Tag)
  | .error fault => .error fault
  | .ok pointer => .ok (renamePointer resolve pointer)

theorem renameOffsetResult_error_shape
    {Tag : Type} (resolve : AllocId → Nat) (fault : OffsetFault) :
    renameOffsetResult (Tag := Tag) resolve
        (.error fault : Except OffsetFault (Pointer Tag)) =
      (.error fault : Except OffsetFault (Pointer Tag)) := by
  rfl

theorem renameOffsetResult_success_shape
    (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    renameOffsetResult resolve (.ok pointer) = .ok (renamePointer resolve pointer) := by
  rfl

theorem renameOffsetResult_kind_preserved
    (resolve : AllocId → Nat) (result : Except OffsetFault (Pointer Tag)) :
    match result, renameOffsetResult resolve result with
    | .ok _, .ok _ => True
    | .error _, .error _ => True
    | _, _ => False := by
  cases result <;> simp [renameOffsetResult]

theorem renameOffsetResult_contract
    (resolve : AllocId → Nat) (result : Except OffsetFault (Pointer Tag)) :
    match result with
    | .error fault => renameOffsetResult resolve result = .error fault
    | .ok pointer => renameOffsetResult resolve result = .ok (renamePointer resolve pointer) := by
  cases result <;> rfl

theorem renameOffsetResult_comp
    (first second : AllocId → Nat)
    (result : Except OffsetFault (Pointer Tag)) :
    renameOffsetResult second (renameOffsetResult first result) =
      renameOffsetResult second result := by
  cases result with
  | error fault => rfl
  | ok pointer =>
      simp [renameOffsetResult, renamePointer_comp]

def pairedOffsetPointer (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat) :
    Bool :=
  match offsetPointer pointer elementSize delta bound,
    offsetPointer (renamePointer resolve pointer) elementSize delta bound with
  | .ok source, .ok target => (renamePointer resolve source).address == target.address
  | .error .outOfBounds, .error .outOfBounds => true
  | .error .alignment, .error .alignment => true
  | _, _ => false

theorem pairedOffsetPointer_zero_element_size
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (delta : Int) (bound : Nat) :
    pairedOffsetPointer resolve pointer 0 delta bound = true := by
  simp [pairedOffsetPointer, offsetPointer]

theorem pairedOffsetPointer_zero_delta
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize bound : Nat)
    (hsource : pointer.address ≤ bound)
    (htarget : (renamePointer resolve pointer).address ≤ bound) :
    pairedOffsetPointer resolve pointer elementSize 0 bound = true := by
  cases hsize : elementSize with
  | zero => simp [pairedOffsetPointer, offsetPointer, hsize]
  | succ n =>
      have hsource' : ¬ bound < pointer.address := Nat.not_lt.mpr hsource
      have htarget' : ¬ bound < (renamePointer resolve pointer).address :=
        Nat.not_lt.mpr htarget
      simp [pairedOffsetPointer, offsetPointer, hsource', htarget']

theorem pairedOffsetPointer_success_nonnegative_unprovenanced
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (hprovenance : pointer.provenance = none)
    (hsize : elementSize ≠ 0) (hdelta : 0 ≤ delta)
    (hsourceBound : pointer.address + Int.natAbs delta * elementSize ≤ bound)
    (htargetBound : (renamePointer resolve pointer).address +
      Int.natAbs delta * elementSize ≤ bound) :
    pairedOffsetPointer resolve pointer elementSize delta bound = true := by
  cases pointer with
  | mk provenance address =>
      have hneg : ¬ delta < 0 := by omega
      have hbound : ¬ bound < address + Int.natAbs delta * elementSize :=
        Nat.not_lt.mpr hsourceBound
      cases hprov : provenance with
      | none => simp [renamePointer, pairedOffsetPointer, offsetPointer, hsize, hneg, hbound, hprov]
      | some p => simp [hprov] at hprovenance

theorem pairedOffsetPointer_outOfBounds_nonnegative_unprovenanced
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (hprovenance : pointer.provenance = none)
    (hsize : elementSize ≠ 0) (hdelta : 0 ≤ delta)
    (hsourceBound : bound < pointer.address + Int.natAbs delta * elementSize) :
    pairedOffsetPointer resolve pointer elementSize delta bound = true := by
  cases pointer with
  | mk provenance address =>
      have hneg : ¬ delta < 0 := by omega
      have hbound : bound < address + Int.natAbs delta * elementSize := by
        simpa using hsourceBound
      cases hprov : provenance with
      | none =>
          simp [renamePointer, pairedOffsetPointer, offsetPointer, hsize, hneg, hbound, hprov]
      | some p => simp [hprov] at hprovenance

theorem pairedOffsetPointer_negative_underflow_unprovenanced
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (hprovenance : pointer.provenance = none)
    (hsize : elementSize ≠ 0) (hdelta : delta < 0)
    (hunderflow : pointer.address < Int.natAbs delta * elementSize) :
    pairedOffsetPointer resolve pointer elementSize delta bound = true := by
  cases pointer with
  | mk provenance address =>
      cases hprov : provenance with
      | none =>
          by_cases hbound : bound < address - Int.natAbs delta * elementSize
          · simp [renamePointer, pairedOffsetPointer, offsetPointer, hsize, hdelta,
              hunderflow, hprov, hbound]
          · simp [renamePointer, pairedOffsetPointer, offsetPointer, hsize, hdelta,
              hunderflow, hprov, hbound]
      | some p => simp [hprov] at hprovenance

theorem pairedOffsetPointer_success_negative_unprovenanced
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (hprovenance : pointer.provenance = none)
    (hsize : elementSize ≠ 0) (hdelta : delta < 0)
    (hwithin : Int.natAbs delta * elementSize ≤ pointer.address)
    (hsourceBound : pointer.address - Int.natAbs delta * elementSize ≤ bound)
    (htargetBound : (renamePointer resolve pointer).address -
      Int.natAbs delta * elementSize ≤ bound) :
    pairedOffsetPointer resolve pointer elementSize delta bound = true := by
  cases pointer with
  | mk provenance address =>
      cases hprov : provenance with
      | none =>
          have hbound : ¬ bound < address - Int.natAbs delta * elementSize :=
            Nat.not_lt.mpr hsourceBound
          simp [renamePointer, pairedOffsetPointer, offsetPointer, hsize, hdelta,
            hwithin, hbound, hprov]
      | some p => simp [hprov] at hprovenance

theorem pairedOffsetPointer_outOfBounds_negative_unprovenanced
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (hprovenance : pointer.provenance = none)
    (hsize : elementSize ≠ 0) (hdelta : delta < 0)
    (hwithin : Int.natAbs delta * elementSize ≤ pointer.address)
    (hsourceBound : bound < pointer.address - Int.natAbs delta * elementSize) :
    pairedOffsetPointer resolve pointer elementSize delta bound = true := by
  cases pointer with
  | mk provenance address =>
      cases hprov : provenance with
      | none =>
          have hbound : bound < address - Int.natAbs delta * elementSize := by
            simpa using hsourceBound
          simp [renamePointer, pairedOffsetPointer, offsetPointer, hsize, hdelta,
            hwithin, hbound, hprov]
      | some p => simp [hprov] at hprovenance

theorem pairedOffsetPointer_both_success [BEq Tag]
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (source target : Pointer Tag)
    (hsource : offsetPointer pointer elementSize delta bound = .ok source)
    (htarget : offsetPointer (renamePointer resolve pointer) elementSize delta bound =
      .ok target)
    (hcorrespond : target = renamePointer resolve source) :
    pairedOffsetPointer resolve pointer elementSize delta bound = true := by
  simp [pairedOffsetPointer, hsource, htarget, hcorrespond]

theorem pairedOffsetPointer_matching_fault [BEq Tag]
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (fault : OffsetFault)
    (hsource : offsetPointer pointer elementSize delta bound = .error fault)
    (htarget : offsetPointer (renamePointer resolve pointer) elementSize delta bound =
      .error fault) :
    pairedOffsetPointer resolve pointer elementSize delta bound = true := by
  cases fault <;> simp [pairedOffsetPointer, hsource, htarget]

theorem pairedOffsetPointer_refusal_source
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (fault : OffsetFault) (target : Pointer Tag)
    (hsource : offsetPointer pointer elementSize delta bound = .error fault)
    (htarget : offsetPointer (renamePointer resolve pointer) elementSize delta bound =
      .ok target) :
    pairedOffsetPointer resolve pointer elementSize delta bound = false := by
  cases fault <;> simp [pairedOffsetPointer, hsource, htarget]

theorem pairedOffsetPointer_refusal_target
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (source : Pointer Tag) (fault : OffsetFault)
    (hsource : offsetPointer pointer elementSize delta bound = .ok source)
    (htarget : offsetPointer (renamePointer resolve pointer) elementSize delta bound =
      .error fault) :
    pairedOffsetPointer resolve pointer elementSize delta bound = false := by
  cases fault <;> simp [pairedOffsetPointer, hsource, htarget]

theorem pairedOffsetPointer_refusal
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (hrefusal :
      (∃ fault target,
        offsetPointer pointer elementSize delta bound = .error fault ∧
        offsetPointer (renamePointer resolve pointer) elementSize delta bound = .ok target) ∨
      (∃ source fault,
        offsetPointer pointer elementSize delta bound = .ok source ∧
        offsetPointer (renamePointer resolve pointer) elementSize delta bound = .error fault)) :
    pairedOffsetPointer resolve pointer elementSize delta bound = false := by
  rcases hrefusal with ⟨fault, target, hsource, htarget⟩ |
    ⟨source, fault, hsource, htarget⟩
  · cases fault <;> simp [pairedOffsetPointer, hsource, htarget]
  · cases fault <;> simp [pairedOffsetPointer, hsource, htarget]

theorem pairedOffsetPointer_failure_contract
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat) :
    pairedOffsetPointer resolve pointer elementSize delta bound = false ↔
      (∃ fault target,
        offsetPointer pointer elementSize delta bound = .error fault ∧
        offsetPointer (renamePointer resolve pointer) elementSize delta bound = .ok target) ∨
      (∃ source fault,
        offsetPointer pointer elementSize delta bound = .ok source ∧
        offsetPointer (renamePointer resolve pointer) elementSize delta bound = .error fault) ∨
      (∃ sourceFault targetFault,
        offsetPointer pointer elementSize delta bound = .error sourceFault ∧
        offsetPointer (renamePointer resolve pointer) elementSize delta bound = .error targetFault ∧
        sourceFault ≠ targetFault) ∨
      (∃ source target,
        offsetPointer pointer elementSize delta bound = .ok source ∧
        offsetPointer (renamePointer resolve pointer) elementSize delta bound = .ok target ∧
        (renamePointer resolve source).address ≠ target.address) := by
  cases hs : offsetPointer pointer elementSize delta bound with
  | error sourceFault =>
      cases ht : offsetPointer (renamePointer resolve pointer) elementSize delta bound with
      | error targetFault =>
          cases sourceFault <;> cases targetFault <;> simp [pairedOffsetPointer, hs, ht]
      | ok target =>
          simp [pairedOffsetPointer, hs, ht]
  | ok source =>
      cases ht : offsetPointer (renamePointer resolve pointer) elementSize delta bound with
      | error targetFault =>
          simp [pairedOffsetPointer, hs, ht]
      | ok target =>
          by_cases hsame : (renamePointer resolve source).address = target.address
          · simp [pairedOffsetPointer, hs, ht, hsame]
          · simp [pairedOffsetPointer, hs, ht, hsame]

theorem pairedOffsetPointer_sound
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (h : pairedOffsetPointer resolve pointer elementSize delta bound = true) :
    (∃ source target,
      offsetPointer pointer elementSize delta bound = .ok source ∧
      offsetPointer (renamePointer resolve pointer) elementSize delta bound = .ok target ∧
      target.address = (renamePointer resolve source).address) ∨
    (∃ fault,
      offsetPointer pointer elementSize delta bound = .error fault ∧
      offsetPointer (renamePointer resolve pointer) elementSize delta bound = .error fault) := by
  cases hs : offsetPointer pointer elementSize delta bound with
  | ok source =>
      cases ht : offsetPointer (renamePointer resolve pointer) elementSize delta bound with
      | ok target =>
          have haddr : ((renamePointer resolve source).address == target.address) = true := by
            simpa [pairedOffsetPointer, hs, ht] using h
          have hEq : (renamePointer resolve source).address = target.address := by
            exact (beq_iff_eq.mp haddr)
          exact Or.inl ⟨source, target, rfl, rfl, hEq.symm⟩
      | error fault => simp [pairedOffsetPointer, hs, ht] at h
  | error sourceFault =>
      cases ht : offsetPointer (renamePointer resolve pointer) elementSize delta bound with
      | ok target => simp [pairedOffsetPointer, hs, ht] at h
      | error targetFault =>
          cases sourceFault <;> cases targetFault <;>
            simp [pairedOffsetPointer, hs, ht] at h ⊢
          all_goals exact Or.inr ⟨_, rfl, rfl⟩

def allocate (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) : Option (Store Tag State × Footprint) :=
  match placement with
  | .fail => none
  | .address base =>
      if !placementAllowed store base request.bytes.length then none
      else
        let id := store.nextId
        let allocation : Allocation Tag State :=
          { live := true, address := some base, bytes := request.bytes, state := request.state }
        some ({ allocations := store.allocations ++ [(id, allocation)],
                nextId := id + 1 },
              footprint .metadata (Region.mk id 0 request.bytes.length))
  | .unaddressable =>
      let id := store.nextId
      let allocation : Allocation Tag State :=
        { live := true, address := none, bytes := request.bytes, state := request.state }
      some ({ allocations := store.allocations ++ [(id, allocation)],
              nextId := id + 1 },
            footprint .metadata (Region.mk id 0 request.bytes.length))

theorem allocate_result_contract
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (result : Store Tag State × Footprint) :
    allocate store request placement = some result ↔
      match placement with
      | .fail => False
      | .address base =>
          placementAllowed store base request.bytes.length = true ∧
          allocate store request (.address base) = some result
      | .unaddressable =>
          allocate store request .unaddressable = some result := by
  cases placement with
  | fail => simp [allocate]
  | address base =>
      by_cases hallowed : placementAllowed store base request.bytes.length = true <;>
        simp [allocate, hallowed]
  | unaddressable =>
      simp [allocate]

theorem allocate_preserves_wellFormed
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf store.nextId request.bytes)
    (hresult : allocate store request placement = some result) :
    WellFormed result.1 := by
  cases placement with
  | fail => simp [allocate] at hresult
  | address base =>
      cases hallowed : placementAllowed store base request.bytes.length with
      | false => simp [allocate, hallowed] at hresult
      | true =>
          simp [allocate, hallowed] at hresult
          rcases hresult with ⟨rfl, rfl⟩
          change allocationsWf store.allocations at hstore
          unfold WellFormed
          have append_wf : ∀ entries : List (AllocId × Allocation Tag State),
              allocationsWf entries →
              allocationsWf (entries ++
                [(store.nextId,
                  { live := true, address := some base,
                    bytes := request.bytes, state := request.state })]) := by
            intro entries
            induction entries with
            | nil => intro _; simp [allocationsWf, hbytes]
            | cons entry rest ih =>
                intro hentries
                simp [allocationsWf] at hentries ⊢
                exact ⟨hentries.1, ih hentries.2⟩
          exact append_wf store.allocations hstore
  | unaddressable =>
      simp [allocate] at hresult
      rcases hresult with ⟨rfl, rfl⟩
      change allocationsWf store.allocations at hstore
      unfold WellFormed
      have append_wf : ∀ entries : List (AllocId × Allocation Tag State),
          allocationsWf entries →
          allocationsWf (entries ++
            [(store.nextId,
              { live := true, address := none,
                bytes := request.bytes, state := request.state })]) := by
        intro entries
        induction entries with
        | nil => intro _; simp [allocationsWf, hbytes]
        | cons entry rest ih =>
            intro hentries
            simp [allocationsWf] at hentries ⊢
            exact ⟨hentries.1, ih hentries.2⟩
      exact append_wf store.allocations hstore

theorem allocate_failure_shape
    (store : Store Tag State) (request : AllocationRequest Tag State) :
    allocate store request .fail = none := by
  rfl

theorem allocate_address_success
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base : Nat)
    (hallowed : placementAllowed store base request.bytes.length = true) :
    allocate store request (.address base) =
      some ({ allocations := store.allocations ++
                [(store.nextId,
                  { live := true, address := some base,
                    bytes := request.bytes, state := request.state })],
              nextId := store.nextId + 1 },
            footprint .metadata
              (Region.mk store.nextId 0 request.bytes.length)) := by
  simp [allocate, hallowed]

theorem allocate_address_result_counters
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base : Nat) (result : Store Tag State × Footprint)
    (hallowed : placementAllowed store base request.bytes.length = true)
    (hresult : allocate store request (.address base) = some result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  simp [allocate, hallowed] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  simp

theorem allocate_address_result_footprint
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base : Nat) (result : Store Tag State × Footprint)
    (hallowed : placementAllowed store base request.bytes.length = true)
    (hresult : allocate store request (.address base) = some result) :
    result.2 = footprint .metadata
      (Region.mk store.nextId 0 request.bytes.length) := by
  simp [allocate, hallowed] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  rfl

theorem allocate_address_rejects_placement
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base : Nat)
    (hrejected : placementAllowed store base request.bytes.length = false) :
    allocate store request (.address base) = none := by
  simp [allocate, hrejected]

theorem allocate_unaddressable_success
    (store : Store Tag State) (request : AllocationRequest Tag State) :
    allocate store request .unaddressable =
      some ({ allocations := store.allocations ++
                [(store.nextId,
                  { live := true, address := none,
                    bytes := request.bytes, state := request.state })],
              nextId := store.nextId + 1 },
            footprint .metadata
              (Region.mk store.nextId 0 request.bytes.length)) := by
  rfl

theorem allocate_unaddressable_result_counters
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (result : Store Tag State × Footprint)
    (hresult : allocate store request .unaddressable = some result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  simp [allocate] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  simp

theorem allocate_unaddressable_result_footprint
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (result : Store Tag State × Footprint)
    (hresult : allocate store request .unaddressable = some result) :
    result.2 = footprint .metadata
      (Region.mk store.nextId 0 request.bytes.length) := by
  simp [allocate] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  rfl

theorem allocate_empty_result_shape
    (store : Store Tag State) (state : State) (placement : Placement)
    (result : Store Tag State × Footprint)
    (hresult : allocate store { bytes := [], state := state } placement = some result) :
    match placement with
    | .address base =>
        result =
          ({ allocations := store.allocations ++
                [(store.nextId,
                  { live := true, address := some base,
                    bytes := [], state := state })],
              nextId := store.nextId + 1 },
            footprint .metadata (Region.mk store.nextId 0 0))
    | .unaddressable =>
        result =
          ({ allocations := store.allocations ++
                [(store.nextId,
                  { live := true, address := none,
                    bytes := [], state := state })],
              nextId := store.nextId + 1 },
            footprint .metadata (Region.mk store.nextId 0 0))
    | .fail => False := by
  cases placement with
  | address base =>
      simp [allocate] at hresult
      rcases hresult with ⟨hallowed, rfl⟩
      rfl
  | unaddressable =>
      simp [allocate] at hresult
      rcases hresult with ⟨rfl, rfl⟩
      rfl
  | fail =>
      simp [allocate] at hresult

theorem allocate_empty_result_counters
    (store : Store Tag State) (state : State) (placement : Placement)
    (result : Store Tag State × Footprint)
    (hresult : allocate store { bytes := [], state := state } placement = some result) :
    match placement with
    | .address _ =>
        result.1.nextId = store.nextId + 1 ∧
          result.1.allocations.length = store.allocations.length + 1
    | .unaddressable =>
        result.1.nextId = store.nextId + 1 ∧
          result.1.allocations.length = store.allocations.length + 1
    | .fail => False := by
  cases placement with
  | address base =>
      simp [allocate] at hresult
      rcases hresult with ⟨_, rfl⟩
      simp
  | unaddressable =>
      simp [allocate] at hresult
      rcases hresult with ⟨rfl, rfl⟩
      simp
  | fail =>
      simp [allocate] at hresult

theorem allocate_empty_result_wellFormed
    (store : Store Tag State) (state : State) (placement : Placement)
    (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hresult : allocate store { bytes := [], state := state } placement = some result) :
    WellFormed result.1 := by
  exact allocate_preserves_wellFormed store { bytes := [], state := state }
    placement result hstore (by simp [bytesWf]) hresult

theorem allocate_empty_result_footprint
    (store : Store Tag State) (state : State) (placement : Placement)
    (result : Store Tag State × Footprint)
    (hresult : allocate store { bytes := [], state := state } placement = some result) :
    result.2 = footprint .metadata (Region.mk store.nextId 0 0) := by
  cases placement with
  | address base =>
      simp [allocate] at hresult
      rcases hresult with ⟨_, rfl⟩
      rfl
  | unaddressable =>
      simp [allocate] at hresult
      rcases hresult with ⟨rfl, rfl⟩
      rfl
  | fail =>
      simp [allocate] at hresult

def allocateAligned (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment : Nat) : Option (Store Tag State × Footprint) :=
  match placement with
  | .address base =>
      if !alignmentAllowed base alignment then none
      else allocate store request placement
  | _ => allocate store request placement

theorem allocateAligned_failure_shape
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment : Nat) :
    allocateAligned store request .fail alignment = none := by
  rfl

theorem allocateAligned_result_contract
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment : Nat)
    (result : Store Tag State × Footprint) :
    allocateAligned store request placement alignment = some result ↔
      match placement with
      | .address base =>
          alignmentAllowed base alignment = true ∧
            allocate store request (.address base) = some result
      | .unaddressable =>
          allocate store request .unaddressable = some result
      | .fail => False := by
  cases placement with
  | address base =>
      by_cases haligned : alignmentAllowed base alignment = true <;>
        simp [allocateAligned, haligned]
  | unaddressable =>
      simp [allocateAligned]
  | fail =>
      simp [allocateAligned, allocate_failure_shape]

theorem allocateAligned_rejects_misaligned
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment : Nat)
    (hrejected : alignmentAllowed base alignment = false) :
    allocateAligned store request (.address base) alignment = none := by
  simp [allocateAligned, hrejected]

theorem allocateAligned_address_success
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment : Nat)
    (haligned : alignmentAllowed base alignment = true)
    (hresult : allocate store request (.address base) = some result) :
    allocateAligned store request (.address base) alignment = some result := by
  simp [allocateAligned, haligned, hresult]

theorem allocateAligned_address_result_counters
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment : Nat) (result : Store Tag State × Footprint)
    (haligned : alignmentAllowed base alignment = true)
    (hresult : allocateAligned store request (.address base) alignment = some result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  simp [allocateAligned, haligned, allocate] at hresult
  by_cases hallowed : placementAllowed store base request.bytes.length = true
  · simp [hallowed] at hresult
    rcases hresult with ⟨rfl, rfl⟩
    simp
  · simp [hallowed] at hresult

theorem allocateAligned_empty_address_result_counters
    (store : Store Tag State) (state : State)
    (base alignment : Nat) (result : Store Tag State × Footprint)
    (haligned : alignmentAllowed base alignment = true)
    (hresult : allocateAligned store { bytes := [], state := state }
      (.address base) alignment = some result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  exact allocateAligned_address_result_counters store
    { bytes := [], state := state } base alignment result haligned hresult

theorem allocateAligned_address_result_footprint
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment : Nat) (result : Store Tag State × Footprint)
    (haligned : alignmentAllowed base alignment = true)
    (hresult : allocateAligned store request (.address base) alignment = some result) :
    result.2 = footprint .metadata
      (Region.mk store.nextId 0 request.bytes.length) := by
  simp [allocateAligned, haligned, allocate] at hresult
  by_cases hallowed : placementAllowed store base request.bytes.length = true
  · simp [hallowed] at hresult
    rcases hresult with ⟨rfl, rfl⟩
    rfl
  · simp [hallowed] at hresult

theorem allocateAligned_empty_address_result_footprint
    (store : Store Tag State) (state : State)
    (base alignment : Nat) (result : Store Tag State × Footprint)
    (haligned : alignmentAllowed base alignment = true)
    (hresult : allocateAligned store { bytes := [], state := state }
      (.address base) alignment = some result) :
    result.2 = footprint .metadata (Region.mk store.nextId 0 0) := by
  exact allocateAligned_address_result_footprint store
    { bytes := [], state := state } base alignment result haligned hresult

theorem allocateAligned_address_result_payload
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment : Nat) (result : Store Tag State × Footprint)
    (haligned : alignmentAllowed base alignment = true)
    (hresult : allocateAligned store request (.address base) alignment = some result) :
    ∃ hallowed : placementAllowed store base request.bytes.length = true,
      result.1 =
        { allocations := store.allocations ++
            [(store.nextId,
              { live := true, address := some base,
                bytes := request.bytes, state := request.state })]
          nextId := store.nextId + 1 } := by
  simp [allocateAligned, haligned, allocate] at hresult
  by_cases hallowed : placementAllowed store base request.bytes.length = true
  · simp [hallowed] at hresult
    rcases hresult with ⟨rfl, rfl⟩
    exact ⟨hallowed, rfl⟩
  · simp [hallowed] at hresult

theorem allocateAligned_empty_address_result_payload
    (store : Store Tag State) (state : State)
    (base alignment : Nat) (result : Store Tag State × Footprint)
    (haligned : alignmentAllowed base alignment = true)
    (hresult : allocateAligned store { bytes := [], state := state }
      (.address base) alignment = some result) :
    ∃ hallowed : placementAllowed store base 0 = true,
      result.1 =
        { allocations := store.allocations ++
            [(store.nextId,
              { live := true, address := some base,
                bytes := [], state := state })]
          nextId := store.nextId + 1 } := by
  exact allocateAligned_address_result_payload store
    { bytes := [], state := state } base alignment result haligned hresult

theorem allocateAligned_address_preserves_wellFormed
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment : Nat) (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf store.nextId request.bytes)
    (haligned : alignmentAllowed base alignment = true)
    (hresult : allocateAligned store request (.address base) alignment = some result) :
    WellFormed result.1 := by
  have hpayload := allocateAligned_address_result_payload store request
    base alignment result haligned hresult
  rcases hpayload with ⟨hallowed, hpayload⟩
  rw [hpayload]
  change allocationsWf store.allocations at hstore
  unfold WellFormed
  have append_wf : ∀ entries : List (AllocId × Allocation Tag State),
      allocationsWf entries →
      allocationsWf (entries ++
        [(store.nextId,
          { live := true, address := some base,
            bytes := request.bytes, state := request.state })]) := by
    intro entries
    induction entries with
    | nil => intro _; simp [allocationsWf, hbytes]
    | cons entry rest ih =>
        intro hentries
        simp [allocationsWf] at hentries ⊢
        exact ⟨hentries.1, ih hentries.2⟩
  exact append_wf store.allocations hstore

theorem allocateAligned_empty_address_preserves_wellFormed
    (store : Store Tag State) (state : State)
    (base alignment : Nat) (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (haligned : alignmentAllowed base alignment = true)
    (hresult : allocateAligned store { bytes := [], state := state }
      (.address base) alignment = some result) :
    WellFormed result.1 := by
  exact allocateAligned_address_preserves_wellFormed store
    { bytes := [], state := state } base alignment result hstore
    (by simp [bytesWf]) haligned hresult

theorem allocateAligned_unaddressable_result_counters
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateAligned store request .unaddressable alignment = some result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  simp [allocateAligned, allocate] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  simp

theorem allocateAligned_unaddressable_result_footprint
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateAligned store request .unaddressable alignment = some result) :
    result.2 = footprint .metadata
      (Region.mk store.nextId 0 request.bytes.length) := by
  simp [allocateAligned, allocate] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  rfl

theorem allocateAligned_empty_unaddressable_result_counters
    (store : Store Tag State) (state : State) (alignment : Nat)
    (result : Store Tag State × Footprint)
    (hresult : allocateAligned store { bytes := [], state := state }
      .unaddressable alignment = some result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  exact allocateAligned_unaddressable_result_counters store
    { bytes := [], state := state } alignment result hresult

theorem allocateAligned_empty_unaddressable_result_footprint
    (store : Store Tag State) (state : State) (alignment : Nat)
    (result : Store Tag State × Footprint)
    (hresult : allocateAligned store { bytes := [], state := state }
      .unaddressable alignment = some result) :
    result.2 = footprint .metadata (Region.mk store.nextId 0 0) := by
  exact allocateAligned_unaddressable_result_footprint store
    { bytes := [], state := state } alignment result hresult

theorem allocateAligned_unaddressable_result_payload
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateAligned store request .unaddressable alignment = some result) :
    result.1 =
      { allocations := store.allocations ++
          [(store.nextId,
            { live := true, address := none,
              bytes := request.bytes, state := request.state })]
        nextId := store.nextId + 1 } := by
  simp [allocateAligned, allocate] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  rfl

theorem allocateAligned_empty_unaddressable_result_payload
    (store : Store Tag State) (state : State) (alignment : Nat)
    (result : Store Tag State × Footprint)
    (hresult : allocateAligned store { bytes := [], state := state }
      .unaddressable alignment = some result) :
    result.1 =
      { allocations := store.allocations ++
          [(store.nextId,
            { live := true, address := none,
              bytes := [], state := state })]
        nextId := store.nextId + 1 } := by
  exact allocateAligned_unaddressable_result_payload store
    { bytes := [], state := state } alignment result hresult

theorem allocateAligned_unaddressable_preserves_wellFormed
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment : Nat) (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf store.nextId request.bytes)
    (hresult : allocateAligned store request .unaddressable alignment = some result) :
    WellFormed result.1 := by
  have hpayload := allocateAligned_unaddressable_result_payload store request
    alignment result hresult
  rw [hpayload]
  change allocationsWf store.allocations at hstore
  unfold WellFormed
  have append_wf : ∀ entries : List (AllocId × Allocation Tag State),
      allocationsWf entries →
      allocationsWf (entries ++
        [(store.nextId,
          { live := true, address := none,
            bytes := request.bytes, state := request.state })]) := by
    intro entries
    induction entries with
    | nil => intro _; simp [allocationsWf, hbytes]
    | cons entry rest ih =>
        intro hentries
        simp [allocationsWf] at hentries ⊢
        exact ⟨hentries.1, ih hentries.2⟩
  exact append_wf store.allocations hstore

theorem allocateAligned_empty_unaddressable_preserves_wellFormed
    (store : Store Tag State) (state : State) (alignment : Nat)
    (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hresult : allocateAligned store { bytes := [], state := state }
      .unaddressable alignment = some result) :
    WellFormed result.1 := by
  exact allocateAligned_unaddressable_preserves_wellFormed store
    { bytes := [], state := state } alignment result hstore
    (by simp [bytesWf]) hresult

def renamedPlacement (resolve : AllocId → Nat) (id : AllocId) :
    Placement → Placement
  | .address _ => .address (resolve id)
  | .unaddressable => .unaddressable
  | .fail => .fail

theorem renamedPlacement_comp
    (first second : AllocId → Nat) (id : AllocId)
    (placement : Placement) :
    renamedPlacement second id (renamedPlacement first id placement) =
      renamedPlacement second id placement := by
  cases placement <;> rfl

def pairedAllocateAligned (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment : Nat) : Bool :=
  match allocateAligned store request placement alignment,
    allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment with
  | some _, some _ => true
  | none, none => true
  | _, _ => false

theorem pairedAllocateAligned_fail_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (alignment : Nat) :
    pairedAllocateAligned resolve store request .fail alignment = true := by
  simp [pairedAllocateAligned, allocateAligned, allocate, renamedPlacement]

theorem pairedAllocateAligned_empty_fail_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment : Nat) :
    pairedAllocateAligned resolve store { bytes := [], state := state }
      .fail alignment = true := by
  exact pairedAllocateAligned_fail_true resolve store
    { bytes := [], state := state } alignment

theorem pairedAllocateAligned_unaddressable_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (alignment : Nat) :
    pairedAllocateAligned resolve store request .unaddressable alignment = true := by
  simp [pairedAllocateAligned, allocateAligned, allocate, renamedPlacement,
    renameAllocationRequest]

theorem pairedAllocateAligned_empty_unaddressable_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment : Nat) :
    pairedAllocateAligned resolve store { bytes := [], state := state }
      .unaddressable alignment = true := by
  exact pairedAllocateAligned_unaddressable_true resolve store
    { bytes := [], state := state } alignment

theorem pairedAllocateAligned_address_misaligned_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (base alignment : Nat)
    (hsource : alignmentAllowed base alignment = false)
    (htarget : alignmentAllowed (resolve store.nextId) alignment = false) :
    pairedAllocateAligned resolve store request (.address base) alignment = true := by
  simp [pairedAllocateAligned, allocateAligned, renamedPlacement, hsource, htarget]

theorem pairedAllocateAligned_empty_address_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment : Nat)
    (hsourceAligned : alignmentAllowed base alignment = true)
    (htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true)
    (hsourcePlacement : placementAllowed store base 0 = true)
    (htargetPlacement : placementAllowed (renameStore resolve store)
      (resolve store.nextId) 0 = true) :
    pairedAllocateAligned resolve store { bytes := [], state := state }
      (.address base) alignment = true := by
  simp [pairedAllocateAligned, allocateAligned, allocate, renamedPlacement,
    hsourceAligned, htargetAligned, hsourcePlacement, htargetPlacement,
    renameAllocationRequest]

theorem pairedAllocateAligned_empty_address_misaligned_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment : Nat)
    (hsource : alignmentAllowed base alignment = false)
    (htarget : alignmentAllowed (resolve store.nextId) alignment = false) :
    pairedAllocateAligned resolve store { bytes := [], state := state }
      (.address base) alignment = true := by
  exact pairedAllocateAligned_address_misaligned_true resolve store
    { bytes := [], state := state } base alignment hsource htarget

theorem pairedAllocateAligned_empty_address_result_payload
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateAligned store { bytes := [], state := state }
      (.address base) alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment = some target) :
    source.1 =
        { allocations := store.allocations ++
            [(store.nextId,
              { live := true, address := some base,
                bytes := [], state := state })]
          nextId := store.nextId + 1 } ∧
      target.1 =
        { allocations := (renameStore resolve store).allocations ++
            [((renameStore resolve store).nextId,
              { live := true, address := some (resolve store.nextId),
                bytes := [], state := state })]
          nextId := (renameStore resolve store).nextId + 1 } := by
  have hsourceAligned : alignmentAllowed base alignment = true := by
    by_cases h : alignmentAllowed base alignment = true
    · exact h
    · simp [allocateAligned, h] at hsource
  have htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true := by
    by_cases h : alignmentAllowed (resolve store.nextId) alignment = true
    · exact h
    · simp [allocateAligned, renamedPlacement, h] at htarget
  have hsourcePayload := allocateAligned_empty_address_result_payload store
    state base alignment source hsourceAligned hsource
  have htargetPayload := allocateAligned_empty_address_result_payload
    (renameStore resolve store) state (resolve store.nextId) alignment target
    (by simpa [renameAllocationRequest, renamedPlacement] using htargetAligned)
    (by simpa [renameAllocationRequest, renamedPlacement] using htarget)
  rcases hsourcePayload with ⟨_, hs⟩
  rcases htargetPayload with ⟨_, ht⟩
  exact ⟨hs, ht⟩

theorem pairedAllocateAligned_empty_address_result_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateAligned store { bytes := [], state := state }
      (.address base) alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment = some target) :
    source.2 = footprint .metadata (Region.mk store.nextId 0 0) ∧
      target.2 = footprint .metadata
        (Region.mk (renameStore resolve store).nextId 0 0) := by
  have hsourceAligned : alignmentAllowed base alignment = true := by
    by_cases h : alignmentAllowed base alignment = true
    · exact h
    · simp [allocateAligned, h] at hsource
  have htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true := by
    by_cases h : alignmentAllowed (resolve store.nextId) alignment = true
    · exact h
    · simp [allocateAligned, renamedPlacement, h] at htarget
  exact ⟨allocateAligned_empty_address_result_footprint store state
      base alignment source hsourceAligned hsource,
    allocateAligned_empty_address_result_footprint (renameStore resolve store)
      state (resolve store.nextId) alignment target
      (by simpa [renameAllocationRequest, renamedPlacement] using htargetAligned)
      (by simpa [renameAllocationRequest, renamedPlacement] using htarget)⟩

theorem pairedAllocateAligned_empty_address_result_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateAligned store { bytes := [], state := state }
      (.address base) alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment = some target) :
    source.1.nextId = store.nextId + 1 ∧
      target.1.nextId = (renameStore resolve store).nextId + 1 ∧
      source.1.allocations.length = store.allocations.length + 1 ∧
      target.1.allocations.length = (renameStore resolve store).allocations.length + 1 := by
  have hsourceAligned : alignmentAllowed base alignment = true := by
    by_cases h : alignmentAllowed base alignment = true
    · exact h
    · simp [allocateAligned, h] at hsource
  have htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true := by
    by_cases h : alignmentAllowed (resolve store.nextId) alignment = true
    · exact h
    · simp [allocateAligned, renamedPlacement, h] at htarget
  exact ⟨allocateAligned_empty_address_result_counters store state base alignment
      source hsourceAligned hsource |>.1,
    allocateAligned_empty_address_result_counters (renameStore resolve store)
      state (resolve store.nextId) alignment target
      (by simpa [renameAllocationRequest, renamedPlacement] using htargetAligned)
      (by simpa [renameAllocationRequest, renamedPlacement] using htarget) |>.1,
    allocateAligned_empty_address_result_counters store state base alignment
      source hsourceAligned hsource |>.2,
    allocateAligned_empty_address_result_counters (renameStore resolve store)
      state (resolve store.nextId) alignment target
      (by simpa [renameAllocationRequest, renamedPlacement] using htargetAligned)
      (by simpa [renameAllocationRequest, renamedPlacement] using htarget) |>.2⟩

theorem pairedAllocateAligned_empty_address_result_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment : Nat)
    (source target : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hsource : allocateAligned store { bytes := [], state := state }
      (.address base) alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment = some target) :
    WellFormed source.1 ∧ WellFormed target.1 := by
  have hsourceAligned : alignmentAllowed base alignment = true := by
    by_cases h : alignmentAllowed base alignment = true
    · exact h
    · simp [allocateAligned, h] at hsource
  have htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true := by
    by_cases h : alignmentAllowed (resolve store.nextId) alignment = true
    · exact h
    · simp [allocateAligned, renamedPlacement, h] at htarget
  exact ⟨allocateAligned_empty_address_preserves_wellFormed store state
      base alignment source hstore hsourceAligned hsource,
    allocateAligned_empty_address_preserves_wellFormed (renameStore resolve store)
      state (resolve store.nextId) alignment target (renameStore_preserves_wellFormed resolve store hstore)
      (by simpa [renameAllocationRequest, renamedPlacement] using htargetAligned)
      (by simpa [renameAllocationRequest, renamedPlacement] using htarget)⟩

theorem pairedAllocateAligned_empty_unaddressable_result_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateAligned store { bytes := [], state := state }
      .unaddressable alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      .unaddressable alignment = some target) :
    source.2 = footprint .metadata (Region.mk store.nextId 0 0) ∧
      target.2 = footprint .metadata
        (Region.mk (renameStore resolve store).nextId 0 0) := by
  exact ⟨allocateAligned_empty_unaddressable_result_footprint store state
      alignment source hsource,
    allocateAligned_empty_unaddressable_result_footprint (renameStore resolve store)
      state alignment target
      (by simpa [renameAllocationRequest] using htarget)⟩

theorem pairedAllocateAligned_empty_unaddressable_result_payload
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateAligned store { bytes := [], state := state }
      .unaddressable alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      .unaddressable alignment = some target) :
    source.1 =
        { allocations := store.allocations ++
            [(store.nextId,
              { live := true, address := none,
                bytes := [], state := state })]
          nextId := store.nextId + 1 } ∧
      target.1 =
        { allocations := (renameStore resolve store).allocations ++
            [((renameStore resolve store).nextId,
              { live := true, address := none,
                bytes := [], state := state })]
          nextId := (renameStore resolve store).nextId + 1 } := by
  exact ⟨allocateAligned_empty_unaddressable_result_payload store state
      alignment source hsource,
    allocateAligned_empty_unaddressable_result_payload (renameStore resolve store)
      state alignment target
      (by simpa [renameAllocationRequest] using htarget)⟩

theorem pairedAllocateAligned_empty_unaddressable_result_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateAligned store { bytes := [], state := state }
      .unaddressable alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      .unaddressable alignment = some target) :
    source.1.nextId = store.nextId + 1 ∧
      target.1.nextId = (renameStore resolve store).nextId + 1 ∧
      source.1.allocations.length = store.allocations.length + 1 ∧
      target.1.allocations.length = (renameStore resolve store).allocations.length + 1 := by
  exact ⟨allocateAligned_empty_unaddressable_result_counters store state
      alignment source hsource |>.1,
    allocateAligned_empty_unaddressable_result_counters (renameStore resolve store)
      state alignment target
      (by simpa [renameAllocationRequest] using htarget) |>.1,
    allocateAligned_empty_unaddressable_result_counters store state alignment
      source hsource |>.2,
    allocateAligned_empty_unaddressable_result_counters (renameStore resolve store)
      state alignment target
      (by simpa [renameAllocationRequest] using htarget) |>.2⟩

theorem pairedAllocateAligned_empty_unaddressable_result_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment : Nat)
    (source target : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hsource : allocateAligned store { bytes := [], state := state }
      .unaddressable alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      .unaddressable alignment = some target) :
    WellFormed source.1 ∧ WellFormed target.1 := by
  exact ⟨allocateAligned_empty_unaddressable_preserves_wellFormed store state
      alignment source hstore hsource,
    allocateAligned_empty_unaddressable_preserves_wellFormed (renameStore resolve store)
      state alignment target (renameStore_preserves_wellFormed resolve store hstore)
      (by simpa [renameAllocationRequest] using htarget)⟩

theorem pairedAllocateAligned_empty_unaddressable_result_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment : Nat) :
    pairedAllocateAligned resolve store { bytes := [], state := state }
      .unaddressable alignment = true := by
  exact pairedAllocateAligned_empty_unaddressable_true resolve store state alignment

theorem pairedAllocateAligned_both_success
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat)
    (hsource : allocateAligned store request placement alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment = some target) :
    pairedAllocateAligned resolve store request placement alignment = true := by
  simp [pairedAllocateAligned, hsource, htarget]

theorem pairedAllocateAligned_both_refused
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat)
    (hsource : allocateAligned store request placement alignment = none)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment = none) :
    pairedAllocateAligned resolve store request placement alignment = true := by
  simp [pairedAllocateAligned, hsource, htarget]

theorem pairedAllocateAligned_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat) :
    pairedAllocateAligned resolve store request placement alignment = false ↔
      (allocateAligned store request placement alignment = none ∧
        allocateAligned (renameStore resolve store)
          (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment ≠ none) ∨
      (allocateAligned store request placement alignment ≠ none ∧
        allocateAligned (renameStore resolve store)
          (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment = none) := by
  cases hs : allocateAligned store request placement alignment with
  | none =>
      cases ht : allocateAligned (renameStore resolve store)
          (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment with
      | none => simp [pairedAllocateAligned, hs, ht]
      | some target => simp [pairedAllocateAligned, hs, ht]
  | some source =>
      cases ht : allocateAligned (renameStore resolve store)
          (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment with
      | none => simp [pairedAllocateAligned, hs, ht]
      | some target => simp [pairedAllocateAligned, hs, ht]

theorem pairedAllocateAligned_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat) (h : pairedAllocateAligned resolve store request placement alignment = true) :
    (∃ source target,
      allocateAligned store request placement alignment = some source ∧
      allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment = some target) ∨
    (allocateAligned store request placement alignment = none ∧
      allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment = none) := by
  cases hs : allocateAligned store request placement alignment with
  | none =>
      cases ht : allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment with
      | none => exact Or.inr ⟨rfl, rfl⟩
      | some target => simp [pairedAllocateAligned, hs, ht] at h
  | some source =>
      cases ht : allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment with
      | none => simp [pairedAllocateAligned, hs, ht] at h
      | some target => exact Or.inl ⟨source, target, rfl, rfl⟩

theorem pairedAllocateAligned_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat) (source target : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hsourceBytes : bytesWf store.nextId request.bytes)
    (htargetBytes : bytesWf (renameStore resolve store).nextId
      (renameAllocationRequest resolve request).bytes)
    (hsource : allocateAligned store request placement alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment = some target) :
    WellFormed source.1 ∧ WellFormed target.1 := by
  cases placement with
  | address base =>
      have hsourceAligned : alignmentAllowed base alignment = true := by
        by_cases h : alignmentAllowed base alignment = true
        · exact h
        · simp [allocateAligned, h] at hsource
      have htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true := by
        have htarget' := htarget
        simp [allocateAligned, renamedPlacement] at htarget'
        by_cases h : alignmentAllowed (resolve store.nextId) alignment = true
        · exact h
        · simp [h] at htarget'
      exact ⟨allocateAligned_address_preserves_wellFormed store request base alignment
          source hstore hsourceBytes hsourceAligned hsource,
        allocateAligned_address_preserves_wellFormed (renameStore resolve store)
          (renameAllocationRequest resolve request) (resolve store.nextId) alignment target
          (renameStore_preserves_wellFormed resolve store hstore) htargetBytes
          htargetAligned htarget⟩
  | unaddressable =>
      exact ⟨allocateAligned_unaddressable_preserves_wellFormed store request alignment
          source hstore hsourceBytes hsource,
        allocateAligned_unaddressable_preserves_wellFormed (renameStore resolve store)
          (renameAllocationRequest resolve request) alignment target
          (renameStore_preserves_wellFormed resolve store hstore) htargetBytes htarget⟩
  | fail =>
      simp [allocateAligned, allocate] at hsource

theorem pairedAllocateAligned_empty_result_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (placement : Placement) (alignment : Nat)
    (source target : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hsource : allocateAligned store { bytes := [], state := state }
      placement alignment = some source)
    (htarget : allocateAligned (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId placement) alignment = some target) :
    WellFormed source.1 ∧ WellFormed target.1 := by
  exact pairedAllocateAligned_preserves_wellFormed resolve store
    { bytes := [], state := state } placement alignment source target hstore
    (by simp [bytesWf]) (by simp [bytesWf, renameAllocationRequest]) hsource htarget

theorem pairedAllocateAligned_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat)
    (hsource : allocateAligned store request placement alignment = some source)
    (htarget : allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment = none) :
    pairedAllocateAligned resolve store request placement alignment = false := by
  simp [pairedAllocateAligned, hsource, htarget]

theorem pairedAllocateAligned_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat)
    (hsource : allocateAligned store request placement alignment = none)
    (htarget : allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment = some target) :
    pairedAllocateAligned resolve store request placement alignment = false := by
  simp [pairedAllocateAligned, hsource, htarget]

theorem pairedAllocateAligned_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat)
    (hrefusal : allocateAligned store request placement alignment = none ∧
      allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment = some target ∨
      allocateAligned store request placement alignment = some source ∧
      allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment = none) :
    pairedAllocateAligned resolve store request placement alignment = false := by
  rcases hrefusal with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · simp [pairedAllocateAligned, hsource, htarget]
  · simp [pairedAllocateAligned, hsource, htarget]

def placementWithin (base size limit : Nat) : Bool :=
  base ≤ limit && size ≤ limit - base

theorem placementWithin_success
    (base size limit : Nat)
    (hbase : base ≤ limit)
    (hsize : size ≤ limit - base) :
    placementWithin base size limit = true := by
  simp [placementWithin, hbase, hsize]

theorem placementWithin_refusal_base
    (base size limit : Nat)
    (hrejected : limit < base) :
    placementWithin base size limit = false := by
  simp [placementWithin, Nat.not_le.mpr hrejected]

theorem placementWithin_refusal_size
    (base size limit : Nat)
    (hbase : base ≤ limit)
    (hrejected : limit - base < size) :
    placementWithin base size limit = false := by
  simp [placementWithin, hbase, Nat.not_le.mpr hrejected]

theorem placementWithin_contract
    (base size limit : Nat) :
    placementWithin base size limit = true ↔
      base ≤ limit ∧ size ≤ limit - base := by
  simp only [placementWithin, Bool.and_eq_true]
  constructor
  · rintro ⟨hbase, hsize⟩
    exact ⟨decide_eq_true_iff.mp hbase, decide_eq_true_iff.mp hsize⟩
  · rintro ⟨hbase, hsize⟩
    exact ⟨decide_eq_true hbase, decide_eq_true hsize⟩

def pairedPlacementWithin (resolve : AllocId → Nat)
    (id size limit : Nat) (base : Nat) : Bool :=
  placementWithin base size limit == placementWithin (resolve id) size limit

theorem pairedPlacementWithin_sound (resolve : AllocId → Nat)
    (id size limit base : Nat)
    (h : pairedPlacementWithin resolve id size limit base) :
    placementWithin base size limit == placementWithin (resolve id) size limit := by
  simpa [pairedPlacementWithin] using h

theorem pairedPlacementWithin_success
    (resolve : AllocId → Nat) (id size limit base : Nat)
    (hbase : placementWithin base size limit = true)
    (htarget : placementWithin (resolve id) size limit = true) :
    pairedPlacementWithin resolve id size limit base = true := by
  simp [pairedPlacementWithin, hbase, htarget]

theorem pairedPlacementWithin_zero
    (resolve : AllocId → Nat) (id limit base : Nat)
    (hbase : base ≤ limit)
    (htarget : resolve id ≤ limit) :
    pairedPlacementWithin resolve id 0 limit base = true := by
  simp [pairedPlacementWithin, placementWithin, hbase, htarget]

theorem pairedPlacementWithin_refusal_source
    (resolve : AllocId → Nat) (id size limit base : Nat)
    (hsource : placementWithin base size limit = false)
    (htarget : placementWithin (resolve id) size limit = true) :
    pairedPlacementWithin resolve id size limit base = false := by
  simp [pairedPlacementWithin, hsource, htarget]

theorem pairedPlacementWithin_refusal_target
    (resolve : AllocId → Nat) (id size limit base : Nat)
    (hsource : placementWithin base size limit = true)
    (htarget : placementWithin (resolve id) size limit = false) :
    pairedPlacementWithin resolve id size limit base = false := by
  simp [pairedPlacementWithin, hsource, htarget]

theorem pairedPlacementWithin_refusal
    (resolve : AllocId → Nat) (id size limit base : Nat)
    (hrefusal : placementWithin base size limit = false ∧
      placementWithin (resolve id) size limit = true ∨
      placementWithin base size limit = true ∧
      placementWithin (resolve id) size limit = false) :
    pairedPlacementWithin resolve id size limit base = false := by
  rcases hrefusal with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · simp [pairedPlacementWithin, hsource, htarget]
  · simp [pairedPlacementWithin, hsource, htarget]

theorem pairedPlacementWithin_contract
    (resolve : AllocId → Nat) (id size limit base : Nat) :
    pairedPlacementWithin resolve id size limit base = true ↔
      placementWithin base size limit = placementWithin (resolve id) size limit := by
  simp [pairedPlacementWithin, beq_iff_eq]

def placementWithinComposition (first second : AllocId → Nat)
    (id size limit base : Nat) : Bool :=
  placementWithin (first id) size limit == placementWithin (second id) size limit

theorem placementWithinComposition_both_allowed
    (first second : AllocId → Nat) (id size limit base : Nat)
    (hfirst : placementWithin (first id) size limit = true)
    (hsecond : placementWithin (second id) size limit = true) :
    placementWithinComposition first second id size limit base = true := by
  simp [placementWithinComposition, hfirst, hsecond]

theorem placementWithinComposition_zero
    (first second : AllocId → Nat) (id limit : Nat)
    (hfirst : first id ≤ limit)
    (hsecond : second id ≤ limit) :
    placementWithinComposition first second id 0 limit 0 = true := by
  simp [placementWithinComposition, placementWithin, hfirst, hsecond]

theorem placementWithinComposition_both_refused
    (first second : AllocId → Nat) (id size limit base : Nat)
    (hfirst : placementWithin (first id) size limit = false)
    (hsecond : placementWithin (second id) size limit = false) :
    placementWithinComposition first second id size limit base = true := by
  simp [placementWithinComposition, hfirst, hsecond]

theorem placementWithinComposition_refusal_first
    (first second : AllocId → Nat) (id size limit base : Nat)
    (hfirst : placementWithin (first id) size limit = false)
    (hsecond : placementWithin (second id) size limit = true) :
    placementWithinComposition first second id size limit base = false := by
  simp [placementWithinComposition, hfirst, hsecond]

theorem placementWithinComposition_refusal_second
    (first second : AllocId → Nat) (id size limit base : Nat)
    (hfirst : placementWithin (first id) size limit = true)
    (hsecond : placementWithin (second id) size limit = false) :
    placementWithinComposition first second id size limit base = false := by
  simp [placementWithinComposition, hfirst, hsecond]

theorem placementWithinComposition_refusal
    (first second : AllocId → Nat) (id size limit base : Nat)
    (hrefusal : placementWithin (first id) size limit = false ∧
      placementWithin (second id) size limit = true ∨
      placementWithin (first id) size limit = true ∧
      placementWithin (second id) size limit = false) :
    placementWithinComposition first second id size limit base = false := by
  rcases hrefusal with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · simp [placementWithinComposition, hfirst, hsecond]
  · simp [placementWithinComposition, hfirst, hsecond]

theorem placementWithinComposition_contract
    (first second : AllocId → Nat) (id size limit base : Nat) :
    placementWithinComposition first second id size limit base = true ↔
      placementWithin (first id) size limit =
        placementWithin (second id) size limit := by
  simp [placementWithinComposition, beq_iff_eq]

theorem placementWithin_zero (base limit : Nat) :
    placementWithin base 0 limit = (base ≤ limit) := by
  simp [placementWithin]

structure PlacementAgreement where
  left : AllocId → Option Nat
  right : AllocId → Option Nat
  exposed : AllocId → Bool

def PlacementAgreement.agrees (agreement : PlacementAgreement) : Prop :=
  ∀ id, agreement.left id = agreement.right id

def PlacementAgreement.agreesAt (agreement : PlacementAgreement) (id : AllocId) : Bool :=
  agreement.left id == agreement.right id

theorem PlacementAgreement.agreesAt_sound
    (agreement : PlacementAgreement) (id : AllocId)
    (h : agreement.agreesAt id = true) :
    agreement.left id = agreement.right id := by
  simpa [PlacementAgreement.agreesAt] using h

theorem PlacementAgreement.agrees_of_agreesAt
    (agreement : PlacementAgreement)
    (h : ∀ id, agreement.agreesAt id = true) :
    agreement.agrees := by
  intro id
  exact agreement.agreesAt_sound id (h id)

theorem PlacementAgreement.agrees_contract
    (agreement : PlacementAgreement) :
    agreement.agrees ↔ ∀ id, agreement.agreesAt id = true := by
  constructor
  · intro hagrees id
    simp [PlacementAgreement.agreesAt, hagrees id]
  · exact agreement.agrees_of_agreesAt

theorem PlacementAgreement.agreesAt_refusal
    (agreement : PlacementAgreement) (id : AllocId)
    (h : agreement.left id ≠ agreement.right id) :
    agreement.agreesAt id = false := by
  simp [PlacementAgreement.agreesAt, h]

theorem PlacementAgreement.agrees_refusal
    (agreement : PlacementAgreement)
    (hrefusal : ∃ id, agreement.left id ≠ agreement.right id) :
    ¬ agreement.agrees := by
  intro hagrees
  rcases hrefusal with ⟨id, hneq⟩
  exact hneq (hagrees id)

def zeroTokenPlacementAgreement (left right : AllocationMetadata Tag State TypeId) :
    PlacementAgreement :=
  { left := fun _ => left.allocation.address
    right := fun _ => right.allocation.address
    exposed := fun _ => false }

theorem zeroTokenPlacementAgreement_agreesAt
    (left right : AllocationMetadata Tag State TypeId)
    (id : AllocId) (haddress : left.allocation.address = right.allocation.address) :
    (zeroTokenPlacementAgreement left right).agreesAt id = true := by
  simp [zeroTokenPlacementAgreement, PlacementAgreement.agreesAt, haddress]

theorem zeroTokenPlacementAgreement_agrees
    (left right : AllocationMetadata Tag State TypeId)
    (haddress : left.allocation.address = right.allocation.address) :
    (zeroTokenPlacementAgreement left right).agrees := by
  intro id
  simp [zeroTokenPlacementAgreement, haddress]

theorem zeroTokenPlacementAgreement_refusal
    (left right : AllocationMetadata Tag State TypeId)
    (id : AllocId)
    (haddress : left.allocation.address ≠ right.allocation.address) :
    (zeroTokenPlacementAgreement left right).agreesAt id = false := by
  simp [zeroTokenPlacementAgreement, PlacementAgreement.agreesAt, haddress]

theorem zeroTokenPlacementAgreement_agreesAt_contract
    (left right : AllocationMetadata Tag State TypeId) (id : AllocId) :
    (zeroTokenPlacementAgreement left right).agreesAt id = true ↔
      left.allocation.address = right.allocation.address := by
  simp [zeroTokenPlacementAgreement, PlacementAgreement.agreesAt, beq_iff_eq]

def placementOf (store : Store Tag State) (id : AllocId) : Option Nat :=
  (lookup store id).bind Allocation.address

theorem placementOf_result_contract
    (store : Store Tag State) (id : AllocId) (result : Option Nat)
    (hresult : placementOf store id = result) :
    (∃ allocation,
      lookup store id = some allocation ∧
      result = allocation.address) ∨
    (lookup store id = none ∧ result = none) := by
  cases hlookup : lookup store id with
  | none =>
      right
      exact ⟨rfl, by simpa [placementOf, hlookup] using hresult.symm⟩
  | some allocation =>
      left
      exact ⟨allocation, rfl, by simpa [placementOf, hlookup] using hresult.symm⟩

theorem placementOf_empty
    {Tag State : Type} (id : AllocId) :
    placementOf (Tag := Tag) (State := State)
      { allocations := [], nextId := 0 } id = none := by
  rfl

theorem placementOf_renameStore
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId) :
    placementOf (renameStore resolve store) id =
      (placementOf store id).map (fun _ => resolve id) := by
  simp only [placementOf]
  rw [lookup_renameStore]
  cases hlookup : lookup store id with
  | none => simp [placementOf, hlookup]
  | some allocation =>
      simp [placementOf, hlookup, renameAllocationValue]

theorem placementOf_renameStore_contract
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId) :
    placementOf (renameStore resolve store) id =
        (placementOf store id).map (fun _ => resolve id) ∧
      (placementOf store id = none → placementOf (renameStore resolve store) id = none) := by
  constructor
  · exact placementOf_renameStore resolve store id
  · intro hplacement
    rw [placementOf_renameStore, hplacement]
    rfl

def placementAgreementOfStores (left right : Store Tag State)
    (exposed : AllocId → Bool) : PlacementAgreement :=
  { left := placementOf left
    right := placementOf right
    exposed := exposed }

theorem placementAgreementOfStores_empty_agrees
    {Tag State : Type} (exposed : AllocId → Bool) :
    (placementAgreementOfStores
      ({ allocations := [], nextId := 0 } : Store Tag State)
      ({ allocations := [], nextId := 0 } : Store Tag State)
      exposed).agrees := by
  intro id
  rfl

def exposedPlacementAgreement (resolve : AllocId → Nat)
    (store : Store Tag State) (exposed : AllocId → Bool) : PlacementAgreement :=
  { left := placementOf store
    right := fun id => (placementOf store id).map (fun _ => resolve id)
    exposed := exposed }

theorem exposedPlacementAgreement_agreesAt_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (exposed : AllocId → Bool) (id : AllocId) :
    (exposedPlacementAgreement resolve store exposed).agreesAt id = true ↔
      placementOf store id = (placementOf store id).map (fun _ => resolve id) := by
  simp [exposedPlacementAgreement, PlacementAgreement.agreesAt, beq_iff_eq]

theorem exposedPlacementAgreement_empty_agrees
    {Tag State : Type} (resolve : AllocId → Nat)
    (exposed : AllocId → Bool) :
    (exposedPlacementAgreement (Tag := Tag) (State := State) resolve
      ({ allocations := [], nextId := 0 } : Store Tag State) exposed).agrees := by
  intro id
  rfl

theorem placementAgreementOfStores_rename_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (exposed : AllocId → Bool) :
    placementAgreementOfStores store (renameStore resolve store) exposed =
      exposedPlacementAgreement resolve store exposed := by
  simp only [placementAgreementOfStores, exposedPlacementAgreement]
  congr
  funext id
  exact placementOf_renameStore resolve store id

def pairedAllocate (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement) :
    Option ((Store Tag State × Footprint) × (Store Tag State × Footprint)) := do
  let sourceResult ← allocate store request placement
  let targetResult ← allocate (renameStore resolve store)
    (renameAllocationRequest resolve request)
    (renamedPlacement resolve store.nextId placement)
  some (sourceResult, targetResult)

theorem pairedAllocate_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (hrefusal : allocate store request placement = none ∨
      allocate (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) = none) :
    pairedAllocate resolve store request placement = none := by
  cases hrefusal with
  | inl hsource => simp [pairedAllocate, hsource]
  | inr htarget => simp [pairedAllocate, htarget]

theorem pairedAllocate_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (hsource : allocate store request placement = none) :
    pairedAllocate resolve store request placement = none := by
  simp [pairedAllocate, hsource]

theorem pairedAllocate_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (htarget : allocate (renameStore resolve store) (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) = none) :
    pairedAllocate resolve store request placement = none := by
  simp [pairedAllocate, htarget]

theorem pairedAllocate_decompose
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedAllocate resolve store request placement = some result) :
    ∃ sourceResult targetResult, result = (sourceResult, targetResult) := by
  cases hs : allocate store request placement with
  | none => simp [pairedAllocate, hs] at hresult
  | some sourceResult =>
      cases ht : allocate (renameStore resolve store) (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) with
      | none => simp [pairedAllocate, hs, ht] at hresult
      | some targetResult =>
          simp [pairedAllocate, hs, ht] at hresult
          exact ⟨sourceResult, targetResult, hresult.symm⟩

theorem pairedAllocate_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedAllocate resolve store request placement = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      allocate store request placement = some sourceResult ∧
      allocate (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) = some targetResult := by
  cases hs : allocate store request placement with
  | none => simp [pairedAllocate, hs] at hresult
  | some sourceResult =>
      cases ht : allocate (renameStore resolve store) (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) with
      | none => simp [pairedAllocate, hs, ht] at hresult
      | some targetResult =>
          simp [pairedAllocate, hs, ht] at hresult
          exact ⟨sourceResult, targetResult, hresult.symm,
            by simpa using hs, by simpa using ht⟩

theorem pairedAllocate_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hsourceStore : WellFormed store)
    (hsourceBytes : bytesWf store.nextId request.bytes)
    (htargetBytes : bytesWf
      (renameStore resolve store).nextId
        (renameAllocationRequest resolve request).bytes)
    (hresult : pairedAllocate resolve store request placement = some result) :
    WellFormed result.1.1 ∧ WellFormed result.2.1 := by
  cases hs : allocate store request placement with
  | none => simp [pairedAllocate, hs] at hresult
  | some sourceResult =>
      cases ht : allocate (renameStore resolve store)
          (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) with
      | none => simp [pairedAllocate, hs, ht] at hresult
      | some targetResult =>
          simp [pairedAllocate, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨allocate_preserves_wellFormed store request placement sourceResult
              hsourceStore hsourceBytes hs,
            allocate_preserves_wellFormed (renameStore resolve store)
              (renameAllocationRequest resolve request)
              (renamedPlacement resolve store.nextId placement) targetResult
              (renameStore_preserves_wellFormed resolve store hsourceStore)
              htargetBytes ht⟩

theorem pairedAllocate_empty_result_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (placement : Placement)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hstore : WellFormed store)
    (hresult : pairedAllocate resolve store { bytes := [], state := state }
      placement = some result) :
    WellFormed result.1.1 ∧ WellFormed result.2.1 := by
  exact pairedAllocate_preserves_wellFormed resolve store
    { bytes := [], state := state } placement result hstore
    (by simp [bytesWf]) (by simp [bytesWf, renameAllocationRequest]) hresult

theorem pairedAllocate_preserves_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedAllocate resolve store request placement = some result) :
    result.1.1.nextId = store.nextId + 1 ∧
      result.2.1.nextId = (renameStore resolve store).nextId + 1 ∧
      result.1.1.allocations.length = store.allocations.length + 1 ∧
      result.2.1.allocations.length = (renameStore resolve store).allocations.length + 1 := by
  cases placement with
  | fail => simp [pairedAllocate, allocate] at hresult
  | address base =>
      cases hallowed : placementAllowed store base request.bytes.length with
      | false => simp [pairedAllocate, allocate, hallowed] at hresult
      | true =>
          cases htarget : placementAllowed (renameStore resolve store)
              (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length with
          | false => simp [pairedAllocate, allocate, renamedPlacement, hallowed, htarget] at hresult
          | true =>
              simp [pairedAllocate, allocate, renamedPlacement, hallowed, htarget] at hresult
              rcases hresult with ⟨rfl, rfl⟩
              exact ⟨by simp, by simp, by simp, by simp⟩
  | unaddressable =>
      simp [pairedAllocate, allocate] at hresult
      rcases hresult with ⟨rfl, rfl⟩
      exact ⟨by simp, by simp, by simp, by simp⟩

theorem pairedAllocate_empty_result_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (placement : Placement)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedAllocate resolve store { bytes := [], state := state }
      placement = some result) :
    result.1.1.nextId = store.nextId + 1 ∧
      result.2.1.nextId = (renameStore resolve store).nextId + 1 ∧
      result.1.1.allocations.length = store.allocations.length + 1 ∧
      result.2.1.allocations.length = (renameStore resolve store).allocations.length + 1 := by
  exact pairedAllocate_preserves_counts resolve store
    { bytes := [], state := state } placement result hresult

theorem pairedAllocate_preserves_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedAllocate resolve store request placement = some result) :
    result.1.2 = footprint .metadata
        (Region.mk store.nextId 0 request.bytes.length) ∧
      result.2.2 = footprint .metadata
        (Region.mk (renameStore resolve store).nextId 0 request.bytes.length) := by
  cases placement with
  | fail => simp [pairedAllocate, allocate] at hresult
  | address base =>
      cases hallowed : placementAllowed store base request.bytes.length with
      | false => simp [pairedAllocate, allocate, hallowed] at hresult
      | true =>
          cases htarget : placementAllowed (renameStore resolve store)
              (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length with
          | false => simp [pairedAllocate, allocate, renamedPlacement, hallowed, htarget] at hresult
          | true =>
              simp [pairedAllocate, allocate, renamedPlacement, hallowed, htarget] at hresult
              rcases hresult with ⟨rfl, rfl⟩
              exact ⟨by rfl, by simp [renameAllocationRequest]⟩
  | unaddressable =>
      simp [pairedAllocate, allocate] at hresult
      rcases hresult with ⟨rfl, rfl⟩
      exact ⟨by rfl, by simp [renameAllocationRequest]⟩

theorem pairedAllocate_empty_result_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (placement : Placement)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedAllocate resolve store { bytes := [], state := state }
      placement = some result) :
    result.1.2 = footprint .metadata (Region.mk store.nextId 0 0) ∧
      result.2.2 = footprint .metadata
        (Region.mk (renameStore resolve store).nextId 0 0) := by
  exact pairedAllocate_preserves_footprints resolve store
    { bytes := [], state := state } placement result hresult

theorem pairedAllocate_address_success_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (base : Nat)
    (hsource : placementAllowed store base request.bytes.length = true)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length = true) :
    pairedAllocate resolve store request (.address base) =
      some (
        ({ allocations := store.allocations ++
              [(store.nextId,
                { live := true, address := some base,
                  bytes := request.bytes, state := request.state })],
            nextId := store.nextId + 1 },
          footprint .metadata
            (Region.mk store.nextId 0 request.bytes.length)),
        ({ allocations := (renameStore resolve store).allocations ++
              [((renameStore resolve store).nextId,
                { live := true, address := some (resolve store.nextId),
                  bytes := (renameAllocationRequest resolve request).bytes,
                  state := request.state })],
            nextId := (renameStore resolve store).nextId + 1 },
          footprint .metadata
            (Region.mk (renameStore resolve store).nextId 0
              (renameAllocationRequest resolve request).bytes.length))) := by
  have htarget' : placementAllowed (renameStore resolve store)
      (resolve store.nextId) request.bytes.length = true := by
    simpa [renameAllocationRequest] using htarget
  simp [pairedAllocate, allocate, renamedPlacement, hsource, htarget,
    htarget', renameAllocationRequest]

theorem pairedAllocate_empty_address_success_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base : Nat)
    (hsource : placementAllowed store base 0 = true)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) 0 = true) :
    pairedAllocate resolve store { bytes := [], state := state } (.address base) =
      some (
        ({ allocations := store.allocations ++
              [(store.nextId,
                { live := true, address := some base,
                  bytes := [], state := state })],
            nextId := store.nextId + 1 },
          footprint .metadata (Region.mk store.nextId 0 0)),
        ({ allocations := (renameStore resolve store).allocations ++
              [((renameStore resolve store).nextId,
                { live := true, address := some (resolve store.nextId),
                  bytes := [], state := state })],
            nextId := (renameStore resolve store).nextId + 1 },
          footprint .metadata
            (Region.mk (renameStore resolve store).nextId 0 0))) := by
  simpa [renameAllocationRequest] using
    pairedAllocate_address_success_shape resolve store
      { bytes := [], state := state } base hsource htarget

theorem pairedAllocate_unaddressable_success_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) :
    pairedAllocate resolve store request .unaddressable =
      some (
        ({ allocations := store.allocations ++
              [(store.nextId,
                { live := true, address := none,
                  bytes := request.bytes, state := request.state })],
            nextId := store.nextId + 1 },
          footprint .metadata
            (Region.mk store.nextId 0 request.bytes.length)),
        ({ allocations := (renameStore resolve store).allocations ++
              [((renameStore resolve store).nextId,
                { live := true, address := none,
                  bytes := (renameAllocationRequest resolve request).bytes,
                  state := request.state })],
            nextId := (renameStore resolve store).nextId + 1 },
          footprint .metadata
            (Region.mk (renameStore resolve store).nextId 0
              (renameAllocationRequest resolve request).bytes.length))) := by
  simp [pairedAllocate, allocate, renamedPlacement, renameAllocationRequest]

theorem pairedAllocate_empty_unaddressable_success_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) :
    pairedAllocate resolve store { bytes := [], state := state } .unaddressable =
      some (
        ({ allocations := store.allocations ++
              [(store.nextId,
                { live := true, address := none,
                  bytes := [], state := state })],
            nextId := store.nextId + 1 },
          footprint .metadata (Region.mk store.nextId 0 0)),
        ({ allocations := (renameStore resolve store).allocations ++
              [((renameStore resolve store).nextId,
                { live := true, address := none,
                  bytes := [], state := state })],
            nextId := (renameStore resolve store).nextId + 1 },
          footprint .metadata
            (Region.mk (renameStore resolve store).nextId 0 0))) := by
  simp [pairedAllocate, allocate, renamedPlacement, renameAllocationRequest]

def pairedAllocateFailure (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement) : Bool :=
  (allocate store request placement).isNone &&
    (allocate (renameStore resolve store) (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement)).isNone

theorem pairedAllocateFailure_fail_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) :
    pairedAllocateFailure resolve store request .fail = true := by
  simp [pairedAllocateFailure, allocate, renamedPlacement]

theorem pairedAllocateFailure_unaddressable_false
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) :
    pairedAllocateFailure resolve store request .unaddressable = false := by
  simp [pairedAllocateFailure, allocate, renamedPlacement]

theorem pairedAllocateFailure_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (h : pairedAllocateFailure resolve store request placement = true) :
    allocate store request placement = none ∧
      allocate (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) = none := by
  simpa [pairedAllocateFailure] using h

theorem pairedAllocateFailure_both_refused
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (hsource : allocate store request placement = none)
    (htarget : allocate (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) = none) :
    pairedAllocateFailure resolve store request placement = true := by
  simp [pairedAllocateFailure, hsource, htarget]

theorem pairedAllocateFailure_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (hsource : allocate store request placement = some source) :
    pairedAllocateFailure resolve store request placement = false := by
  simp [pairedAllocateFailure, hsource]

theorem pairedAllocateFailure_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (htarget : allocate (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) = some target) :
    pairedAllocateFailure resolve store request placement = false := by
  simp [pairedAllocateFailure, htarget]

theorem pairedAllocateFailure_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (hrefusal :
      allocate store request placement = some source ∨
      allocate (renameStore resolve store)
        (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) = some target) :
    pairedAllocateFailure resolve store request placement = false := by
  rcases hrefusal with hsource | htarget
  · simp [pairedAllocateFailure, hsource]
  · simp [pairedAllocateFailure, htarget]

def unaddressableToken (store : Store Tag State) (id : AllocId) : Bool :=
  match lookup store id with
  | some allocation => allocation.live && allocation.address.isNone
  | none => false

theorem unaddressableToken_sound
    (store : Store Tag State) (id : AllocId)
    (h : unaddressableToken store id = true) :
    ∃ allocation,
      lookup store id = some allocation ∧
      allocation.live = true ∧ allocation.address = none := by
  cases hlookup : lookup store id with
  | none => simp [unaddressableToken, hlookup] at h
  | some allocation =>
      simp [unaddressableToken, hlookup] at h
      exact ⟨allocation, rfl, h.1, by simpa using h.2⟩

theorem unaddressableToken_true
    (store : Store Tag State) (id : AllocId)
    (allocation : Allocation Tag State)
    (hlookup : lookup store id = some allocation)
    (hlive : allocation.live = true)
    (haddress : allocation.address = none) :
    unaddressableToken store id = true := by
  simp [unaddressableToken, hlookup, hlive, haddress]

theorem unaddressableToken_contract
    (store : Store Tag State) (id : AllocId) :
    unaddressableToken store id = true ↔
      ∃ allocation,
        lookup store id = some allocation ∧
        allocation.live = true ∧ allocation.address = none := by
  constructor
  · exact unaddressableToken_sound store id
  · rintro ⟨allocation, hlookup, hlive, haddress⟩
    exact unaddressableToken_true store id allocation hlookup hlive haddress

theorem unaddressableToken_empty_false
    {Tag State : Type} (id : AllocId) :
    unaddressableToken ({ allocations := [], nextId := 0 } : Store Tag State) id = false := by
  rfl

def pairedUnaddressableAllocation (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State) :
    Bool :=
  match allocate store request .unaddressable,
    allocate (renameStore resolve store) (renameAllocationRequest resolve request)
      .unaddressable with
  | some _, some _ => true
  | none, none => true
  | _, _ => false

theorem pairedUnaddressableAllocation_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) :
    pairedUnaddressableAllocation resolve store request = true := by
  simp [pairedUnaddressableAllocation, allocate]

theorem pairedUnaddressableAllocation_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) :
    pairedUnaddressableAllocation resolve store request = false ↔ False := by
  simp [pairedUnaddressableAllocation, allocate]

theorem pairedUnaddressableAllocation_both_success
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State)
    (hsource : allocate store request .unaddressable = some source)
    (htarget : allocate (renameStore resolve store)
      (renameAllocationRequest resolve request) .unaddressable = some target) :
    pairedUnaddressableAllocation resolve store request = true := by
  simp [pairedUnaddressableAllocation, hsource, htarget]

theorem pairedUnaddressableAllocation_both_refused
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State)
    (hsource : allocate store request .unaddressable = none)
    (htarget : allocate (renameStore resolve store)
      (renameAllocationRequest resolve request) .unaddressable = none) :
    pairedUnaddressableAllocation resolve store request = true := by
  simp [pairedUnaddressableAllocation, hsource, htarget]

theorem pairedUnaddressableAllocation_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State)
    (h : pairedUnaddressableAllocation resolve store request = true) :
    (∃ source target,
      allocate store request .unaddressable = some source ∧
      allocate (renameStore resolve store)
        (renameAllocationRequest resolve request) .unaddressable = some target) ∨
    (allocate store request .unaddressable = none ∧
      allocate (renameStore resolve store)
        (renameAllocationRequest resolve request) .unaddressable = none) := by
  cases hs : allocate store request .unaddressable with
  | none =>
      cases ht : allocate (renameStore resolve store)
          (renameAllocationRequest resolve request) .unaddressable with
      | none => exact Or.inr ⟨rfl, rfl⟩
      | some target => simp [pairedUnaddressableAllocation, hs, ht] at h
  | some source =>
      cases ht : allocate (renameStore resolve store)
          (renameAllocationRequest resolve request) .unaddressable with
      | none => simp [pairedUnaddressableAllocation, hs, ht] at h
      | some target => exact Or.inl ⟨source, target, rfl, rfl⟩

theorem pairedUnaddressableAllocation_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State)
    (hsource : allocate store request .unaddressable = some source)
    (htarget : allocate (renameStore resolve store)
      (renameAllocationRequest resolve request) .unaddressable = none) :
    pairedUnaddressableAllocation resolve store request = false := by
  simp [pairedUnaddressableAllocation, hsource, htarget]

theorem pairedUnaddressableAllocation_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State)
    (hsource : allocate store request .unaddressable = none)
    (htarget : allocate (renameStore resolve store)
      (renameAllocationRequest resolve request) .unaddressable = some target) :
    pairedUnaddressableAllocation resolve store request = false := by
  simp [pairedUnaddressableAllocation, hsource, htarget]

theorem pairedUnaddressableAllocation_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State)
    (hrefusal : allocate store request .unaddressable = none ∧
      allocate (renameStore resolve store)
        (renameAllocationRequest resolve request) .unaddressable = some target ∨
      allocate store request .unaddressable = some source ∧
      allocate (renameStore resolve store)
        (renameAllocationRequest resolve request) .unaddressable = none) :
    pairedUnaddressableAllocation resolve store request = false := by
  rcases hrefusal with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · simp [pairedUnaddressableAllocation, hsource, htarget]
  · simp [pairedUnaddressableAllocation, hsource, htarget]

theorem footprintAgrees_rename (resolve : AllocId → Nat) (footprint : Footprint) :
    footprintAgrees (renameFootprint resolve footprint) footprint := by
  simp [renameFootprint, renameRegion, footprintAgrees]

theorem footprintAgrees_refl (footprint : Footprint) :
    footprintAgrees footprint footprint := by
  simp [footprintAgrees]

theorem footprintAgrees_comp (first second : AllocId → Nat)
    (footprint : Footprint) :
    footprintAgrees (renameFootprint second (renameFootprint first footprint))
      (renameFootprint second footprint) := by
  rw [renameFootprint_comp]
  exact footprintAgrees_refl _

inductive PlacementFault where
  | exhausted
  | overlap
  | misaligned
deriving Repr, BEq, DecidableEq

theorem placementFault_beq_iff (left right : PlacementFault) :
    (left == right) = true ↔ left = right := by
  cases left <;> cases right <;> decide


def allocateBounded (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment limit : Nat) :
    Except PlacementFault (Store Tag State × Footprint) :=
  match placement with
  | .fail => .error .exhausted
  | .unaddressable =>
      match allocate store request placement with
      | some result => .ok result
      | none => .error .overlap
  | .address base =>
      if !placementWithin base request.bytes.length limit then .error .exhausted
      else if !alignmentAllowed base alignment then .error .misaligned
      else if !placementAllowed store base request.bytes.length then .error .overlap
      else
        match allocate store request placement with
        | some result => .ok result
        | none => .error .overlap

theorem allocateBounded_error_contract
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment limit : Nat) (fault : PlacementFault) :
    allocateBounded store request placement alignment limit = .error fault ↔
      match placement with
      | .fail => .exhausted = fault
      | .unaddressable =>
          allocate store request .unaddressable = none ∧ .overlap = fault
      | .address base =>
          (placementWithin base request.bytes.length limit = false ∧
              .exhausted = fault) ∨
          (placementWithin base request.bytes.length limit = true ∧
              alignmentAllowed base alignment = false ∧ .misaligned = fault) ∨
          (placementWithin base request.bytes.length limit = true ∧
              alignmentAllowed base alignment = true ∧
              placementAllowed store base request.bytes.length = false ∧
              .overlap = fault) ∨
          (placementWithin base request.bytes.length limit = true ∧
              alignmentAllowed base alignment = true ∧
              placementAllowed store base request.bytes.length = true ∧
              allocate store request (.address base) = none ∧
              .overlap = fault) := by
  cases placement with
  | fail => simp [allocateBounded]
  | unaddressable =>
      cases halloc : allocate store request .unaddressable with
      | none => simp [allocateBounded, halloc]
      | some result => simp [allocateBounded, halloc]
  | address base =>
      cases hwithin : placementWithin base request.bytes.length limit with
      | false => simp [allocateBounded, hwithin]
      | true =>
          cases haligned : alignmentAllowed base alignment with
          | false => simp [allocateBounded, hwithin, haligned]
          | true =>
              cases hallowed : placementAllowed store base request.bytes.length with
              | false => simp [allocateBounded, hwithin, haligned, hallowed]
              | true =>
                  cases halloc : allocate store request (.address base) with
                  | none => simp [allocateBounded, hwithin, haligned, hallowed, halloc]
                  | some result => simp [allocateBounded, hwithin, haligned, hallowed, halloc]

theorem allocateBounded_success_contract
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment limit : Nat)
    (result : Store Tag State × Footprint) :
    allocateBounded store request placement alignment limit = .ok result ↔
      match placement with
      | .fail => False
      | .unaddressable =>
          allocate store request .unaddressable = some result
      | .address base =>
          placementWithin base request.bytes.length limit = true ∧
          alignmentAllowed base alignment = true ∧
          placementAllowed store base request.bytes.length = true ∧
          allocate store request (.address base) = some result := by
  cases placement with
  | fail => simp [allocateBounded]
  | unaddressable =>
      cases halloc : allocate store request .unaddressable with
      | none => simp [allocateBounded, halloc]
      | some allocationResult => simp [allocateBounded, halloc]
  | address base =>
      cases hwithin : placementWithin base request.bytes.length limit with
      | false => simp [allocateBounded, hwithin]
      | true =>
          cases haligned : alignmentAllowed base alignment with
          | false => simp [allocateBounded, hwithin, haligned]
          | true =>
              cases hallowed : placementAllowed store base request.bytes.length with
              | false => simp [allocateBounded, hwithin, haligned, hallowed]
              | true =>
                  cases halloc : allocate store request (.address base) with
                  | none => simp [allocateBounded, hwithin, haligned, hallowed, halloc]
                  | some allocationResult =>
                      simp [allocateBounded, hwithin, haligned, hallowed, halloc]

theorem allocateBounded_failure_shape
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment limit : Nat) :
    allocateBounded store request .fail alignment limit = .error .exhausted := by
  rfl

theorem allocateBounded_empty_failure_shape
    (store : Store Tag State) (state : State) (alignment limit : Nat) :
    allocateBounded store { bytes := [], state := state }
      .fail alignment limit = .error .exhausted := by
  exact allocateBounded_failure_shape store
    { bytes := [], state := state } alignment limit

theorem allocateBounded_address_exhausted
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat)
    (hrejected : placementWithin base request.bytes.length limit = false) :
    allocateBounded store request (.address base) alignment limit =
      .error .exhausted := by
  simp [allocateBounded, hrejected]

theorem allocateBounded_empty_address_exhausted
    (store : Store Tag State) (state : State)
    (base alignment limit : Nat)
    (hrejected : placementWithin base 0 limit = false) :
    allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .error .exhausted := by
  exact allocateBounded_address_exhausted store
    { bytes := [], state := state } base alignment limit hrejected

theorem allocateBounded_address_misaligned
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat)
    (hwithin : placementWithin base request.bytes.length limit = true)
    (hrejected : alignmentAllowed base alignment = false) :
    allocateBounded store request (.address base) alignment limit =
      .error .misaligned := by
  simp [allocateBounded, hwithin, hrejected]

theorem allocateBounded_empty_address_misaligned
    (store : Store Tag State) (state : State)
    (base alignment limit : Nat)
    (hwithin : placementWithin base 0 limit = true)
    (hrejected : alignmentAllowed base alignment = false) :
    allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .error .misaligned := by
  exact allocateBounded_address_misaligned store
    { bytes := [], state := state } base alignment limit hwithin hrejected

theorem allocateBounded_address_overlap
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat)
    (hwithin : placementWithin base request.bytes.length limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hrejected : placementAllowed store base request.bytes.length = false) :
    allocateBounded store request (.address base) alignment limit =
      .error .overlap := by
  simp [allocateBounded, hwithin, haligned, hrejected]

theorem allocateBounded_empty_address_overlap
    (store : Store Tag State) (state : State)
    (base alignment limit : Nat)
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hrejected : placementAllowed store base 0 = false) :
    allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .error .overlap := by
  exact allocateBounded_address_overlap store
    { bytes := [], state := state } base alignment limit hwithin haligned hrejected

theorem allocateBounded_unaddressable_success
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment limit : Nat)
    (hresult : allocate store request .unaddressable = some result) :
    allocateBounded store request .unaddressable alignment limit = .ok result := by
  simp [allocateBounded, hresult]

theorem allocateBounded_empty_unaddressable_success
    (store : Store Tag State) (state : State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hresult : allocate store { bytes := [], state := state }
      .unaddressable = some result) :
    allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result := by
  exact allocateBounded_unaddressable_success store
    { bytes := [], state := state } alignment limit hresult

theorem allocateBounded_unaddressable_result_counters
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateBounded store request .unaddressable alignment limit = .ok result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  cases halloc : allocate store request .unaddressable with
  | none => simp [allocateBounded, halloc] at hresult
  | some allocationResult =>
      simp [allocateBounded, halloc] at hresult
      rcases hresult with rfl
      exact allocate_unaddressable_result_counters store request allocationResult halloc

theorem allocateBounded_empty_unaddressable_result_counters
    (store : Store Tag State) (state : State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  exact allocateBounded_unaddressable_result_counters store
    { bytes := [], state := state } alignment limit result hresult

theorem allocateBounded_unaddressable_result_payload
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateBounded store request .unaddressable alignment limit = .ok result) :
    result.1 =
      { allocations := store.allocations ++
          [(store.nextId,
            { live := true, address := none,
              bytes := request.bytes, state := request.state })]
        nextId := store.nextId + 1 } := by
  cases halloc : allocate store request .unaddressable with
  | none => simp [allocateBounded, halloc] at hresult
  | some allocationResult =>
      simp [allocateBounded, halloc] at hresult
      rcases hresult with rfl
      have hinj := Option.some.inj
        ((allocate_unaddressable_success store request).symm.trans halloc)
      exact congrArg (fun pair : Store Tag State × Footprint => pair.1) hinj.symm

theorem allocateBounded_empty_unaddressable_result_payload
    (store : Store Tag State) (state : State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    result.1 =
      { allocations := store.allocations ++
          [(store.nextId,
            { live := true, address := none,
              bytes := [], state := state })]
        nextId := store.nextId + 1 } := by
  exact allocateBounded_unaddressable_result_payload store
    { bytes := [], state := state } alignment limit result hresult

theorem allocateBounded_unaddressable_result_footprint
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateBounded store request .unaddressable alignment limit = .ok result) :
    result.2 = footprint .metadata
      (Region.mk store.nextId 0 request.bytes.length) := by
  cases halloc : allocate store request .unaddressable with
  | none => simp [allocateBounded, halloc] at hresult
  | some allocationResult =>
      simp [allocateBounded, halloc] at hresult
      rcases hresult with rfl
      exact allocate_unaddressable_result_footprint store request allocationResult halloc

theorem allocateBounded_empty_unaddressable_result_footprint
    (store : Store Tag State) (state : State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    result.2 = footprint .metadata (Region.mk store.nextId 0 0) := by
  exact allocateBounded_unaddressable_result_footprint store
    { bytes := [], state := state } alignment limit result hresult

theorem allocateBounded_empty_unaddressable_result_shape
    (store : Store Tag State) (state : State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    result.1 =
        { allocations := store.allocations ++
            [(store.nextId,
              { live := true, address := none,
                bytes := [], state := state })]
          nextId := store.nextId + 1 } ∧
      result.2 = footprint .metadata (Region.mk store.nextId 0 0) := by
  exact ⟨allocateBounded_empty_unaddressable_result_payload store state
      alignment limit result hresult,
    allocateBounded_empty_unaddressable_result_footprint store state
      alignment limit result hresult⟩

theorem allocateBounded_unaddressable_preserves_wellFormed
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf store.nextId request.bytes)
    (hresult : allocateBounded store request .unaddressable alignment limit = .ok result) :
    WellFormed result.1 := by
  have hpayload := allocateBounded_unaddressable_result_payload store request
    alignment limit result hresult
  rw [hpayload]
  change allocationsWf store.allocations at hstore
  unfold WellFormed
  have append_wf : ∀ entries : List (AllocId × Allocation Tag State),
      allocationsWf entries →
      allocationsWf (entries ++
        [(store.nextId,
          { live := true, address := none,
            bytes := request.bytes, state := request.state })]) := by
    intro entries
    induction entries with
    | nil => intro _; simp [allocationsWf, hbytes]
    | cons entry rest ih =>
        intro hentries
        simp [allocationsWf] at hentries ⊢
        exact ⟨hentries.1, ih hentries.2⟩
  exact append_wf store.allocations hstore

theorem allocateBounded_empty_unaddressable_preserves_wellFormed
    (store : Store Tag State) (state : State)
    (alignment limit : Nat) (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf (Tag := Tag) store.nextId [])
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    WellFormed result.1 := by
  exact allocateBounded_unaddressable_preserves_wellFormed store
    { bytes := [], state := state } alignment limit result hstore hbytes hresult

theorem allocateBounded_address_result_counters
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat) (result : Store Tag State × Footprint)
    (hwithin : placementWithin base request.bytes.length limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base request.bytes.length = true)
    (hresult : allocateBounded store request (.address base) alignment limit = .ok result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  simp [allocateBounded, hwithin, haligned, hallowed, allocate] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  simp

theorem allocateBounded_empty_address_result_counters
    (store : Store Tag State) (state : State)
    (base alignment limit : Nat) (result : Store Tag State × Footprint)
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    result.1.nextId = store.nextId + 1 ∧
      result.1.allocations.length = store.allocations.length + 1 := by
  exact allocateBounded_address_result_counters store
    { bytes := [], state := state } base alignment limit result
    hwithin haligned hallowed hresult

theorem allocateBounded_address_result_footprint
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat) (result : Store Tag State × Footprint)
    (hwithin : placementWithin base request.bytes.length limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base request.bytes.length = true)
    (hresult : allocateBounded store request (.address base) alignment limit = .ok result) :
    result.2 = footprint .metadata
      (Region.mk store.nextId 0 request.bytes.length) := by
  simp [allocateBounded, hwithin, haligned, hallowed, allocate] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  rfl

theorem allocateBounded_empty_address_result_footprint
    (store : Store Tag State) (state : State)
    (base alignment limit : Nat) (result : Store Tag State × Footprint)
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    result.2 = footprint .metadata (Region.mk store.nextId 0 0) := by
  exact allocateBounded_address_result_footprint store
    { bytes := [], state := state } base alignment limit result
    hwithin haligned hallowed hresult

theorem allocateBounded_address_result_payload
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat) (result : Store Tag State × Footprint)
    (hwithin : placementWithin base request.bytes.length limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base request.bytes.length = true)
    (hresult : allocateBounded store request (.address base) alignment limit = .ok result) :
    result.1 =
      { allocations := store.allocations ++
          [(store.nextId,
            { live := true, address := some base,
              bytes := request.bytes, state := request.state })]
        nextId := store.nextId + 1 } := by
  simp [allocateBounded, hwithin, haligned, hallowed, allocate] at hresult
  rcases hresult with rfl
  rfl

theorem allocateBounded_empty_address_result_payload
    (store : Store Tag State) (state : State)
    (base alignment limit : Nat) (result : Store Tag State × Footprint)
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    result.1 =
      { allocations := store.allocations ++
          [(store.nextId,
            { live := true, address := some base,
              bytes := [], state := state })]
        nextId := store.nextId + 1 } := by
  exact allocateBounded_address_result_payload store
    { bytes := [], state := state } base alignment limit result
    hwithin haligned hallowed hresult

theorem allocateBounded_empty_address_result_shape
    (store : Store Tag State) (state : State)
    (base alignment limit : Nat) (result : Store Tag State × Footprint)
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    result.1 =
        { allocations := store.allocations ++
            [(store.nextId,
              { live := true, address := some base,
                bytes := [], state := state })]
          nextId := store.nextId + 1 } ∧
      result.2 = footprint .metadata (Region.mk store.nextId 0 0) := by
  exact ⟨allocateBounded_empty_address_result_payload store state
      base alignment limit result hwithin haligned hallowed hresult,
    allocateBounded_empty_address_result_footprint store state
      base alignment limit result hwithin haligned hallowed hresult⟩

theorem allocateBounded_address_preserves_wellFormed
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat) (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf store.nextId request.bytes)
    (hwithin : placementWithin base request.bytes.length limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base request.bytes.length = true)
    (hresult : allocateBounded store request (.address base) alignment limit = .ok result) :
    WellFormed result.1 := by
  have hpayload := allocateBounded_address_result_payload store request
    base alignment limit result hwithin haligned hallowed hresult
  rw [hpayload]
  change allocationsWf store.allocations at hstore
  unfold WellFormed
  have append_wf : ∀ entries : List (AllocId × Allocation Tag State),
      allocationsWf entries →
      allocationsWf (entries ++
        [(store.nextId,
          { live := true, address := some base,
            bytes := request.bytes, state := request.state })]) := by
    intro entries
    induction entries with
    | nil => intro _; simp [allocationsWf, hbytes]
    | cons entry rest ih =>
        intro hentries
        simp [allocationsWf] at hentries ⊢
        exact ⟨hentries.1, ih hentries.2⟩
  exact append_wf store.allocations hstore

theorem allocateBounded_empty_address_preserves_wellFormed
    (store : Store Tag State) (state : State)
    (base alignment limit : Nat) (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf (Tag := Tag) store.nextId [])
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    WellFormed result.1 := by
  exact allocateBounded_address_preserves_wellFormed store
    { bytes := [], state := state } base alignment limit result
    hstore hbytes hwithin haligned hallowed hresult

def renameBoundedResult (resolve : AllocId → Nat) :
    Except PlacementFault (Store Tag State × Footprint) →
      Except PlacementFault (Store Tag State × Footprint)
  | .error fault => .error fault
  | .ok (store, footprint) =>
      .ok (renameStore resolve store, footprint)

theorem renameBoundedResult_error_shape
    {Tag State : Type} (resolve : AllocId → Nat) (fault : PlacementFault) :
    renameBoundedResult (Tag := Tag) (State := State) resolve
        (.error fault : Except PlacementFault (Store Tag State × Footprint)) =
      (.error fault : Except PlacementFault (Store Tag State × Footprint)) := by
  rfl

theorem renameBoundedResult_success_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (footprint : Footprint) :
    renameBoundedResult resolve (.ok (store, footprint)) =
      .ok (renameStore resolve store, footprint) := by
  rfl

theorem renameBoundedResult_kind_preserved
    (resolve : AllocId → Nat)
    (result : Except PlacementFault (Store Tag State × Footprint)) :
    match result, renameBoundedResult resolve result with
    | .ok _, .ok _ => True
    | .error _, .error _ => True
    | _, _ => False := by
  cases result <;> simp [renameBoundedResult]

theorem renameBoundedResult_success_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (footprint : Footprint) (hstore : WellFormed store) :
    match renameBoundedResult resolve (.ok (store, footprint)) with
    | .ok (target, _) => WellFormed target
    | .error _ => True := by
  simp [renameBoundedResult]
  exact renameStore_preserves_wellFormed resolve store hstore

theorem renameBoundedResult_success_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (footprint : Footprint) :
    match renameBoundedResult resolve (.ok (store, footprint)) with
    | .ok (target, _) =>
        target.nextId = store.nextId ∧
          target.allocations.length = store.allocations.length
    | .error _ => True := by
  simp [renameBoundedResult, renameStore,
    renameStore_nextId, renameStore_allocation_count]

theorem renameBoundedResult_comp
    (first second : AllocId → Nat)
    (result : Except PlacementFault (Store Tag State × Footprint)) :
    renameBoundedResult second (renameBoundedResult first result) =
      renameBoundedResult second result := by
  cases result with
  | error fault => rfl
  | ok value =>
      cases value with
      | mk store footprint =>
          simp [renameBoundedResult, renameStore_comp]

theorem renameBoundedResult_preserves_footprint
    (resolve : AllocId → Nat)
    (result : Except PlacementFault (Store Tag State × Footprint)) :
    match result, renameBoundedResult resolve result with
    | .ok (_, source), .ok (_, target) => target = source
    | .error _, .error _ => True
    | _, _ => False := by
  cases result with
  | error fault => simp [renameBoundedResult]
  | ok value =>
      cases value with
      | mk store footprint => simp [renameBoundedResult]

theorem renameBoundedResult_empty_unaddressable_result_footprint
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (_, fp) =>
        fp = footprint .metadata (Region.mk store.nextId 0 0)
    | .error _ => False := by
  have hfootprint := allocateBounded_empty_unaddressable_result_footprint
    store state alignment limit result hresult
  simp [renameBoundedResult, hfootprint]

theorem renameBoundedResult_empty_unaddressable_result_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (target, _) =>
        target.nextId = store.nextId + 1 ∧
          target.allocations.length = store.allocations.length + 1
    | .error _ => False := by
  have hcounts := allocateBounded_empty_unaddressable_result_counters
    store state alignment limit result hresult
  simp [renameBoundedResult, hcounts, renameStore,
    renameStore_nextId, renameStore_allocation_count]

theorem renameBoundedResult_empty_address_result_footprint
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (_, fp) =>
        fp = footprint .metadata (Region.mk store.nextId 0 0)
    | .error _ => False := by
  have hfootprint := allocateBounded_empty_address_result_footprint
    store state base alignment limit result hwithin haligned hallowed hresult
  simp [renameBoundedResult, hfootprint]

theorem renameBoundedResult_empty_address_result_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (target, _) =>
        target.nextId = store.nextId + 1 ∧
          target.allocations.length = store.allocations.length + 1
    | .error _ => False := by
  have hcounts := allocateBounded_empty_address_result_counters
    store state base alignment limit result hwithin haligned hallowed hresult
  simp [renameBoundedResult, hcounts, renameStore,
    renameStore_nextId, renameStore_allocation_count]

theorem renameBoundedResult_empty_address_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf (Tag := Tag) store.nextId [])
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (target, _) => WellFormed target
    | .error _ => False := by
  have hsourceWf := allocateBounded_empty_address_preserves_wellFormed
    store state base alignment limit result hstore hbytes hwithin haligned hallowed hresult
  simp [renameBoundedResult]
  exact renameStore_preserves_wellFormed resolve result.1 hsourceWf

theorem renameBoundedResult_empty_unaddressable_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf (Tag := Tag) store.nextId [])
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (target, _) => WellFormed target
    | .error _ => False := by
  have hsourceWf := allocateBounded_empty_unaddressable_preserves_wellFormed
    store state alignment limit result hstore hbytes hresult
  simp [renameBoundedResult]
  exact renameStore_preserves_wellFormed resolve result.1 hsourceWf

theorem renameBoundedResult_empty_unaddressable_result_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (target, fp) =>
        target = renameStore resolve result.1 ∧
          fp = footprint .metadata (Region.mk store.nextId 0 0)
    | .error _ => False := by
  have hfootprint := allocateBounded_empty_unaddressable_result_footprint
    store state alignment limit result hresult
  simp [renameBoundedResult, hfootprint]

theorem renameBoundedResult_empty_address_result_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (target, fp) =>
        target = renameStore resolve result.1 ∧
          fp = footprint .metadata (Region.mk store.nextId 0 0)
    | .error _ => False := by
  have hfootprint := allocateBounded_empty_address_result_footprint
    store state base alignment limit result hwithin haligned hallowed hresult
  simp [renameBoundedResult, hfootprint]

theorem renameBoundedResult_empty_unaddressable_result_payload
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hresult : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (target, _) =>
        target = renameStore resolve
          { allocations := store.allocations ++
              [(store.nextId,
                { live := true, address := none,
                  bytes := [], state := state })]
            nextId := store.nextId + 1 }
    | .error _ => False := by
  have hpayload := allocateBounded_empty_unaddressable_result_payload
    store state alignment limit result hresult
  simp [renameBoundedResult, hpayload]

theorem renameBoundedResult_empty_address_result_payload
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (result : Store Tag State × Footprint)
    (hwithin : placementWithin base 0 limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hallowed : placementAllowed store base 0 = true)
    (hresult : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok result) :
    match renameBoundedResult resolve (.ok result) with
    | .ok (target, _) =>
        target = renameStore resolve
          { allocations := store.allocations ++
              [(store.nextId,
                { live := true, address := some base,
                  bytes := [], state := state })]
            nextId := store.nextId + 1 }
    | .error _ => False := by
  have hpayload := allocateBounded_empty_address_result_payload
    store state base alignment limit result hwithin haligned hallowed hresult
  simp [renameBoundedResult, hpayload]

def pairedAllocateBounded (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment limit : Nat) : Bool :=
  match allocateBounded store request placement alignment limit,
    allocateBounded (renameStore resolve store) (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment limit with
  | .ok _, .ok _ => true
  | .error sourceFault, .error targetFault => sourceFault == targetFault
  | _, _ => false

theorem pairedAllocateBounded_fail_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (alignment limit : Nat) :
    pairedAllocateBounded resolve store request .fail alignment limit = true := by
  simp only [pairedAllocateBounded]
  rw [show renamedPlacement resolve store.nextId .fail = .fail by rfl]
  simp [allocateBounded] <;> decide

theorem pairedAllocateBounded_unaddressable_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (alignment limit : Nat) :
    pairedAllocateBounded resolve store request .unaddressable alignment limit = true := by
  simp [pairedAllocateBounded, allocateBounded, allocate, renamedPlacement,
    renameAllocationRequest]

theorem pairedAllocateBounded_empty_unaddressable_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      .unaddressable alignment limit = true := by
  exact pairedAllocateBounded_unaddressable_true resolve store
    { bytes := [], state := state } alignment limit

theorem pairedAllocateBounded_address_success_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (base : Nat)
    (alignment limit : Nat)
    (hwithin : placementWithin base request.bytes.length limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (htargetWithin : placementWithin (resolve store.nextId)
      (renameAllocationRequest resolve request).bytes.length limit = true)
    (htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true)
    (hsource : placementAllowed store base request.bytes.length = true)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length = true) :
    pairedAllocateBounded resolve store request (.address base) alignment limit = true := by
  have htarget' : placementAllowed (renameStore resolve store)
      (resolve store.nextId) request.bytes.length = true := by
    simpa [renameAllocationRequest] using htarget
  have htargetWithin' : placementWithin (resolve store.nextId)
      request.bytes.length limit = true := by
    simpa [renameAllocationRequest] using htargetWithin
  simp [pairedAllocateBounded, allocateBounded, renamedPlacement, hwithin, haligned,
    htargetWithin, htargetWithin', htargetAligned, hsource, htarget, htarget', allocate,
    renameAllocationRequest]

theorem pairedAllocateBounded_empty_address_success_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (hsourceWithin : placementWithin base 0 limit = true)
    (hsourceAligned : alignmentAllowed base alignment = true)
    (htargetWithin : placementWithin (resolve store.nextId) 0 limit = true)
    (htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true)
    (hsource : placementAllowed store base 0 = true)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) 0 = true) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = true := by
  exact pairedAllocateBounded_address_success_shape resolve store
    { bytes := [], state := state } base alignment limit
    hsourceWithin hsourceAligned htargetWithin htargetAligned hsource htarget

theorem pairedAllocateBounded_address_exhausted_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (base alignment limit : Nat)
    (hsource : placementWithin base request.bytes.length limit = false)
    (htarget : placementWithin (resolve store.nextId)
      (renameAllocationRequest resolve request).bytes.length limit = false) :
    pairedAllocateBounded resolve store request (.address base) alignment limit = true := by
  have htarget' : placementWithin (resolve store.nextId)
      request.bytes.length limit = false := by
    simpa [renameAllocationRequest] using htarget
  simp [pairedAllocateBounded, allocateBounded, renamedPlacement, hsource,
    htarget, htarget', renameAllocationRequest] <;> decide

theorem pairedAllocateBounded_empty_address_exhausted_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (hsource : placementWithin base 0 limit = false)
    (htarget : placementWithin (resolve store.nextId) 0 limit = false) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = true := by
  simpa [renameAllocationRequest] using
    pairedAllocateBounded_address_exhausted_true resolve store
      { bytes := [], state := state } base alignment limit hsource htarget

theorem pairedAllocateBounded_address_misaligned_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (base alignment limit : Nat)
    (hsourceWithin : placementWithin base request.bytes.length limit = true)
    (htargetWithin : placementWithin (resolve store.nextId)
      (renameAllocationRequest resolve request).bytes.length limit = true)
    (hsource : alignmentAllowed base alignment = false)
    (htarget : alignmentAllowed (resolve store.nextId) alignment = false) :
    pairedAllocateBounded resolve store request (.address base) alignment limit = true := by
  have htargetWithin' : placementWithin (resolve store.nextId)
      request.bytes.length limit = true := by
    simpa [renameAllocationRequest] using htargetWithin
  simp [pairedAllocateBounded, allocateBounded, renamedPlacement, hsourceWithin,
    htargetWithin, htargetWithin', hsource, htarget, renameAllocationRequest] <;> decide

theorem pairedAllocateBounded_empty_address_misaligned_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (hsourceWithin : placementWithin base 0 limit = true)
    (htargetWithin : placementWithin (resolve store.nextId) 0 limit = true)
    (hsource : alignmentAllowed base alignment = false)
    (htarget : alignmentAllowed (resolve store.nextId) alignment = false) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = true := by
  simpa [renameAllocationRequest] using
    pairedAllocateBounded_address_misaligned_true resolve store
      { bytes := [], state := state } base alignment limit
      hsourceWithin htargetWithin hsource htarget

theorem pairedAllocateBounded_address_overlap_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (base alignment limit : Nat)
    (hsourceWithin : placementWithin base request.bytes.length limit = true)
    (htargetWithin : placementWithin (resolve store.nextId)
      (renameAllocationRequest resolve request).bytes.length limit = true)
    (hsourceAligned : alignmentAllowed base alignment = true)
    (htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true)
    (hsource : placementAllowed store base request.bytes.length = false)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length = false) :
    pairedAllocateBounded resolve store request (.address base) alignment limit = true := by
  have htargetWithin' : placementWithin (resolve store.nextId)
      request.bytes.length limit = true := by
    simpa [renameAllocationRequest] using htargetWithin
  have htarget' : placementAllowed (renameStore resolve store)
      (resolve store.nextId) request.bytes.length = false := by
    simpa [renameAllocationRequest] using htarget
  simp [pairedAllocateBounded, allocateBounded, renamedPlacement, hsourceWithin,
    htargetWithin, htargetWithin', hsourceAligned, htargetAligned, hsource,
    htarget, htarget', renameAllocationRequest] <;> decide

theorem pairedAllocateBounded_empty_address_overlap_true
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (hsourceWithin : placementWithin base 0 limit = true)
    (htargetWithin : placementWithin (resolve store.nextId) 0 limit = true)
    (hsourceAligned : alignmentAllowed base alignment = true)
    (htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true)
    (hsource : placementAllowed store base 0 = false)
    (htarget : placementAllowed (renameStore resolve store)
      (resolve store.nextId) 0 = false) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = true := by
  simpa [renameAllocationRequest] using
    pairedAllocateBounded_address_overlap_true resolve store
      { bytes := [], state := state } base alignment limit
      hsourceWithin htargetWithin hsourceAligned htargetAligned hsource htarget

theorem pairedAllocateBounded_both_success
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat)
    (hsource : allocateBounded store request placement alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment limit = .ok target) :
    pairedAllocateBounded resolve store request placement alignment limit = true := by
  simp [pairedAllocateBounded, hsource, htarget]

theorem pairedAllocateBounded_empty_unaddressable_both_success
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
        .ok target) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      .unaddressable alignment limit = true := by
  exact pairedAllocateBounded_both_success resolve store
    { bytes := [], state := state } .unaddressable alignment limit hsource htarget

theorem pairedAllocateBounded_empty_unaddressable_result_shapes
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
        .ok target) :
    source.1 =
        { allocations := store.allocations ++
            [(store.nextId,
              { live := true, address := none,
                bytes := [], state := state })]
          nextId := store.nextId + 1 } ∧
      source.2 = footprint .metadata (Region.mk store.nextId 0 0) ∧
      target.1 =
        { allocations := (renameStore resolve store).allocations ++
            [((renameStore resolve store).nextId,
              { live := true, address := none,
                bytes := [], state := state })]
          nextId := (renameStore resolve store).nextId + 1 } ∧
      target.2 = footprint .metadata
        (Region.mk (renameStore resolve store).nextId 0 0) := by
  have hsourcePayload := allocateBounded_empty_unaddressable_result_payload
    store state alignment limit source hsource
  have hsourceFootprint := allocateBounded_empty_unaddressable_result_footprint
    store state alignment limit source hsource
  have htargetPayload := allocateBounded_unaddressable_result_payload
    (renameStore resolve store)
    (renameAllocationRequest resolve { bytes := [], state := state })
    alignment limit target htarget
  have htargetFootprint := allocateBounded_unaddressable_result_footprint
    (renameStore resolve store)
    (renameAllocationRequest resolve { bytes := [], state := state })
    alignment limit target htarget
  exact ⟨hsourcePayload, hsourceFootprint,
    by simpa [renameAllocationRequest] using htargetPayload,
    by simpa [renameAllocationRequest] using htargetFootprint⟩

theorem pairedAllocateBounded_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat) (source target : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hsourceBytes : bytesWf store.nextId request.bytes)
    (htargetBytes : bytesWf (renameStore resolve store).nextId
      (renameAllocationRequest resolve request).bytes)
    (hsource : allocateBounded store request placement alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment limit = .ok target) :
    WellFormed source.1 ∧ WellFormed target.1 := by
  cases placement with
  | address base =>
      have hsourceWithin : placementWithin base request.bytes.length limit = true := by
        by_cases h : placementWithin base request.bytes.length limit = true
        · exact h
        · simp [allocateBounded, h] at hsource
      have hsourceAligned : alignmentAllowed base alignment = true := by
        by_cases h : alignmentAllowed base alignment = true
        · exact h
        · simp [allocateBounded, hsourceWithin, h] at hsource
      have hsourceAllowed : placementAllowed store base request.bytes.length = true := by
        by_cases h : placementAllowed store base request.bytes.length = true
        · exact h
        · simp [allocateBounded, hsourceWithin, hsourceAligned, h] at hsource
      have htargetWithin : placementWithin (resolve store.nextId)
          (renameAllocationRequest resolve request).bytes.length limit = true := by
        by_cases h : placementWithin (resolve store.nextId)
            (renameAllocationRequest resolve request).bytes.length limit = true
        · exact h
        · simp [allocateBounded, renamedPlacement, h] at htarget
      have htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true := by
        by_cases h : alignmentAllowed (resolve store.nextId) alignment = true
        · exact h
        · simp [allocateBounded, renamedPlacement, htargetWithin, h] at htarget
      have htargetAllowed : placementAllowed (renameStore resolve store)
          (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length = true := by
        by_cases h : placementAllowed (renameStore resolve store)
            (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length = true
        · exact h
        · simp [allocateBounded, renamedPlacement, htargetWithin, htargetAligned, h] at htarget
      exact ⟨allocateBounded_address_preserves_wellFormed store request base alignment limit
          source hstore hsourceBytes hsourceWithin hsourceAligned hsourceAllowed hsource,
        allocateBounded_address_preserves_wellFormed (renameStore resolve store)
          (renameAllocationRequest resolve request) (resolve store.nextId) alignment limit target
          (renameStore_preserves_wellFormed resolve store hstore) htargetBytes htargetWithin
          htargetAligned htargetAllowed htarget⟩
  | unaddressable =>
      exact ⟨allocateBounded_unaddressable_preserves_wellFormed store request alignment limit
          source hstore hsourceBytes hsource,
        allocateBounded_unaddressable_preserves_wellFormed (renameStore resolve store)
          (renameAllocationRequest resolve request) alignment limit target
          (renameStore_preserves_wellFormed resolve store hstore) htargetBytes htarget⟩
  | fail =>
      simp [allocateBounded] at hsource

theorem pairedAllocateBounded_preserves_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat) (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store request placement alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment limit = .ok target) :
    source.1.nextId = store.nextId + 1 ∧
      source.1.allocations.length = store.allocations.length + 1 ∧
      target.1.nextId = (renameStore resolve store).nextId + 1 ∧
      target.1.allocations.length = (renameStore resolve store).allocations.length + 1 := by
  cases placement with
  | address base =>
      have hsourceWithin : placementWithin base request.bytes.length limit = true := by
        by_cases h : placementWithin base request.bytes.length limit = true
        · exact h
        · simp [allocateBounded, h] at hsource
      have hsourceAligned : alignmentAllowed base alignment = true := by
        by_cases h : alignmentAllowed base alignment = true
        · exact h
        · simp [allocateBounded, hsourceWithin, h] at hsource
      have hsourceAllowed : placementAllowed store base request.bytes.length = true := by
        by_cases h : placementAllowed store base request.bytes.length = true
        · exact h
        · simp [allocateBounded, hsourceWithin, hsourceAligned, h] at hsource
      have htargetWithin : placementWithin (resolve store.nextId)
          (renameAllocationRequest resolve request).bytes.length limit = true := by
        by_cases h : placementWithin (resolve store.nextId)
            (renameAllocationRequest resolve request).bytes.length limit = true
        · exact h
        · simp [allocateBounded, renamedPlacement, h] at htarget
      have htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true := by
        by_cases h : alignmentAllowed (resolve store.nextId) alignment = true
        · exact h
        · simp [allocateBounded, renamedPlacement, htargetWithin, h] at htarget
      have htargetAllowed : placementAllowed (renameStore resolve store)
          (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length = true := by
        by_cases h : placementAllowed (renameStore resolve store)
            (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length = true
        · exact h
        · simp [allocateBounded, renamedPlacement, htargetWithin, htargetAligned, h] at htarget
      have hsourceCounts := allocateBounded_address_result_counters store request
        base alignment limit source hsourceWithin hsourceAligned hsourceAllowed hsource
      have htargetCounts := allocateBounded_address_result_counters
        (renameStore resolve store) (renameAllocationRequest resolve request)
        (resolve store.nextId) alignment limit target
        (by simpa [renameAllocationRequest] using htargetWithin)
        (by simpa [renameAllocationRequest] using htargetAligned)
        (by simpa [renameAllocationRequest] using htargetAllowed)
        (by simpa [renamedPlacement] using htarget)
      exact ⟨hsourceCounts.1, hsourceCounts.2,
        htargetCounts.1, htargetCounts.2⟩
  | unaddressable =>
      have hsourceCounts := allocateBounded_unaddressable_result_counters
        store request alignment limit source hsource
      have htargetCounts := allocateBounded_unaddressable_result_counters
        (renameStore resolve store) (renameAllocationRequest resolve request)
        alignment limit target (by simpa [renamedPlacement] using htarget)
      exact ⟨hsourceCounts.1, hsourceCounts.2,
        htargetCounts.1, htargetCounts.2⟩
  | fail =>
      simp [allocateBounded] at hsource

theorem pairedAllocateBounded_empty_address_result_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment limit =
        .ok target) :
    source.1.nextId = store.nextId + 1 ∧
      source.1.allocations.length = store.allocations.length + 1 ∧
      target.1.nextId = (renameStore resolve store).nextId + 1 ∧
      target.1.allocations.length = (renameStore resolve store).allocations.length + 1 := by
  exact pairedAllocateBounded_preserves_counts resolve store
    { bytes := [], state := state } (.address base) alignment limit source target
    hsource htarget

theorem pairedAllocateBounded_empty_unaddressable_result_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
        .ok target) :
    source.1.nextId = store.nextId + 1 ∧
      source.1.allocations.length = store.allocations.length + 1 ∧
      target.1.nextId = (renameStore resolve store).nextId + 1 ∧
      target.1.allocations.length = (renameStore resolve store).allocations.length + 1 := by
  exact pairedAllocateBounded_preserves_counts resolve store
    { bytes := [], state := state } .unaddressable alignment limit source target
    hsource htarget

theorem pairedAllocateBounded_preserves_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat) (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store request placement alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment limit = .ok target) :
    source.2 = footprint .metadata (Region.mk store.nextId 0 request.bytes.length) ∧
      target.2 = footprint .metadata
        (Region.mk (renameStore resolve store).nextId 0
          (renameAllocationRequest resolve request).bytes.length) := by
  cases placement with
  | address base =>
      have hsourceWithin : placementWithin base request.bytes.length limit = true := by
        by_cases h : placementWithin base request.bytes.length limit = true
        · exact h
        · simp [allocateBounded, h] at hsource
      have hsourceAligned : alignmentAllowed base alignment = true := by
        by_cases h : alignmentAllowed base alignment = true
        · exact h
        · simp [allocateBounded, hsourceWithin, h] at hsource
      have hsourceAllowed : placementAllowed store base request.bytes.length = true := by
        by_cases h : placementAllowed store base request.bytes.length = true
        · exact h
        · simp [allocateBounded, hsourceWithin, hsourceAligned, h] at hsource
      have htargetWithin : placementWithin (resolve store.nextId)
          (renameAllocationRequest resolve request).bytes.length limit = true := by
        by_cases h : placementWithin (resolve store.nextId)
            (renameAllocationRequest resolve request).bytes.length limit = true
        · exact h
        · simp [allocateBounded, renamedPlacement, h] at htarget
      have htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true := by
        by_cases h : alignmentAllowed (resolve store.nextId) alignment = true
        · exact h
        · simp [allocateBounded, renamedPlacement, htargetWithin, h] at htarget
      have htargetAllowed : placementAllowed (renameStore resolve store)
          (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length = true := by
        by_cases h : placementAllowed (renameStore resolve store)
            (resolve store.nextId) (renameAllocationRequest resolve request).bytes.length = true
        · exact h
        · simp [allocateBounded, renamedPlacement, htargetWithin, htargetAligned, h] at htarget
      have hsourceFootprint := allocateBounded_address_result_footprint store request
        base alignment limit source hsourceWithin hsourceAligned hsourceAllowed hsource
      have htargetFootprint := allocateBounded_address_result_footprint
        (renameStore resolve store) (renameAllocationRequest resolve request)
        (resolve store.nextId) alignment limit target
        (by simpa [renameAllocationRequest] using htargetWithin)
        (by simpa [renameAllocationRequest] using htargetAligned)
        (by simpa [renameAllocationRequest] using htargetAllowed)
        (by simpa [renamedPlacement] using htarget)
      exact ⟨hsourceFootprint,
        by simpa [renameAllocationRequest] using htargetFootprint⟩
  | unaddressable =>
      have hsourceFootprint := allocateBounded_unaddressable_result_footprint
        store request alignment limit source hsource
      have htargetFootprint := allocateBounded_unaddressable_result_footprint
        (renameStore resolve store) (renameAllocationRequest resolve request)
        alignment limit target (by simpa [renamedPlacement] using htarget)
      exact ⟨hsourceFootprint,
        by simpa [renameAllocationRequest] using htargetFootprint⟩
  | fail =>
      simp [allocateBounded] at hsource

theorem pairedAllocateBounded_empty_address_result_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment limit =
        .ok target) :
    source.2 = footprint .metadata (Region.mk store.nextId 0 0) ∧
      target.2 = footprint .metadata
        (Region.mk (renameStore resolve store).nextId 0 0) := by
  exact pairedAllocateBounded_preserves_footprints resolve store
    { bytes := [], state := state } (.address base) alignment limit source target
    hsource htarget

theorem pairedAllocateBounded_empty_unaddressable_result_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
        .ok target) :
    source.2 = footprint .metadata (Region.mk store.nextId 0 0) ∧
      target.2 = footprint .metadata
        (Region.mk (renameStore resolve store).nextId 0 0) := by
  exact pairedAllocateBounded_preserves_footprints resolve store
    { bytes := [], state := state } .unaddressable alignment limit source target
    hsource htarget

theorem pairedAllocateBounded_empty_unaddressable_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hsource : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
        .ok target) :
    WellFormed source.1 ∧ WellFormed target.1 := by
  exact pairedAllocateBounded_preserves_wellFormed resolve store
    { bytes := [], state := state } .unaddressable alignment limit source target
    hstore (by simp [bytesWf]) (by simp [bytesWf, renameAllocationRequest]) hsource htarget

theorem pairedAllocateBounded_empty_address_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hsource : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment limit =
        .ok target) :
    WellFormed source.1 ∧ WellFormed target.1 := by
  exact pairedAllocateBounded_preserves_wellFormed resolve store
    { bytes := [], state := state } (.address base) alignment limit source target
    hstore (by simp [bytesWf]) (by simp [bytesWf, renameAllocationRequest]) hsource htarget

theorem pairedAllocateBounded_empty_address_both_success
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment limit =
        .ok target) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = true := by
  exact pairedAllocateBounded_both_success resolve store
    { bytes := [], state := state } (.address base) alignment limit hsource htarget

theorem pairedAllocateBounded_empty_address_result_shapes
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (source target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment limit =
        .ok target) :
    source.1 =
        { allocations := store.allocations ++
            [(store.nextId,
              { live := true, address := some base,
                bytes := [], state := state })]
          nextId := store.nextId + 1 } ∧
      source.2 = footprint .metadata (Region.mk store.nextId 0 0) ∧
      target.1 =
        { allocations := (renameStore resolve store).allocations ++
            [((renameStore resolve store).nextId,
              { live := true, address := some (resolve store.nextId),
                bytes := [], state := state })]
          nextId := (renameStore resolve store).nextId + 1 } ∧
      target.2 = footprint .metadata
        (Region.mk (renameStore resolve store).nextId 0 0) := by
  have hsourceWithin : placementWithin base 0 limit = true := by
    by_cases h : placementWithin base 0 limit = true
    · exact h
    · simp [allocateBounded, h] at hsource
  have hsourceAligned : alignmentAllowed base alignment = true := by
    by_cases h : alignmentAllowed base alignment = true
    · exact h
    · simp [allocateBounded, hsourceWithin, h] at hsource
  have hsourceAllowed : placementAllowed store base 0 = true := by
    by_cases h : placementAllowed store base 0 = true
    · exact h
    · simp [allocateBounded, hsourceWithin, hsourceAligned, h] at hsource
  have hsourcePayload := allocateBounded_empty_address_result_payload
    store state base alignment limit source hsourceWithin hsourceAligned hsourceAllowed hsource
  have hsourceFootprint := allocateBounded_empty_address_result_footprint
    store state base alignment limit source hsourceWithin hsourceAligned hsourceAllowed hsource
  have htarget' : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (.address (resolve store.nextId)) alignment limit = .ok target := by
    simpa [renamedPlacement] using htarget
  have htargetWithin : placementWithin (resolve store.nextId) 0 limit = true := by
    by_cases h : placementWithin (resolve store.nextId) 0 limit = true
    · exact h
    · simp [allocateBounded, renameAllocationRequest, h] at htarget'
  have htargetAligned : alignmentAllowed (resolve store.nextId) alignment = true := by
    by_cases h : alignmentAllowed (resolve store.nextId) alignment = true
    · exact h
    · simp [allocateBounded, renameAllocationRequest, htargetWithin, h] at htarget'
  have htargetAllowed : placementAllowed (renameStore resolve store)
      (resolve store.nextId) 0 = true := by
    by_cases h : placementAllowed (renameStore resolve store)
        (resolve store.nextId) 0 = true
    · exact h
    · simp [allocateBounded, renameAllocationRequest, htargetWithin, htargetAligned, h] at htarget'
  have htargetPayload := allocateBounded_empty_address_result_payload
    (renameStore resolve store) state (resolve store.nextId) alignment limit target
    htargetWithin htargetAligned htargetAllowed htarget'
  have htargetFootprint := allocateBounded_empty_address_result_footprint
    (renameStore resolve store) state (resolve store.nextId) alignment limit target
    htargetWithin htargetAligned htargetAllowed htarget'
  exact ⟨hsourcePayload, hsourceFootprint,
    htargetPayload, htargetFootprint⟩

theorem pairedAllocateBounded_matching_fault
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat) (fault : PlacementFault)
    (hsource : allocateBounded store request placement alignment limit = .error fault)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment limit = .error fault) :
    pairedAllocateBounded resolve store request placement alignment limit = true := by
  cases fault <;> simp [pairedAllocateBounded, hsource, htarget] <;> rfl

theorem pairedAllocateBounded_empty_unaddressable_matching_fault
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat) (fault : PlacementFault)
    (hsource : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .error fault)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
        .error fault) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      .unaddressable alignment limit = true := by
  exact pairedAllocateBounded_matching_fault resolve store
    { bytes := [], state := state } .unaddressable alignment limit fault hsource htarget

theorem pairedAllocateBounded_empty_address_matching_fault
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat) (fault : PlacementFault)
    (hsource : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .error fault)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment limit =
        .error fault) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = true := by
  exact pairedAllocateBounded_matching_fault resolve store
    { bytes := [], state := state } (.address base) alignment limit fault hsource htarget

theorem pairedAllocateBounded_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat)
    (h : pairedAllocateBounded resolve store request placement alignment limit = true) :
    (∃ source target,
      allocateBounded store request placement alignment limit = .ok source ∧
      allocateBounded (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment limit = .ok target) ∨
    (∃ fault,
      allocateBounded store request placement alignment limit = .error fault ∧
      allocateBounded (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment limit = .error fault) := by
  cases hs : allocateBounded store request placement alignment limit with
  | ok source =>
      cases ht : allocateBounded (renameStore resolve store) (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment limit with
      | ok target => exact Or.inl ⟨source, target, rfl, rfl⟩
      | error targetFault => simp [pairedAllocateBounded, hs, ht] at h
  | error sourceFault =>
      cases ht : allocateBounded (renameStore resolve store) (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment limit with
      | ok target => simp [pairedAllocateBounded, hs, ht] at h
      | error targetFault =>
          have hEqBool : (sourceFault == targetFault) = true := by
            simpa [pairedAllocateBounded, hs, ht] using h
          have heq : sourceFault = targetFault :=
            (placementFault_beq_iff sourceFault targetFault).mp hEqBool
          exact Or.inr ⟨sourceFault, rfl, by simpa [heq] using ht⟩

theorem pairedAllocateBounded_empty_unaddressable_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (h : pairedAllocateBounded resolve store { bytes := [], state := state }
      .unaddressable alignment limit = true) :
    (∃ source target,
      allocateBounded store { bytes := [], state := state }
        .unaddressable alignment limit = .ok source ∧
      allocateBounded (renameStore resolve store)
        (renameAllocationRequest resolve { bytes := [], state := state })
        (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
          .ok target) ∨
    (∃ fault,
      allocateBounded store { bytes := [], state := state }
        .unaddressable alignment limit = .error fault ∧
      allocateBounded (renameStore resolve store)
        (renameAllocationRequest resolve { bytes := [], state := state })
        (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
          .error fault) := by
  exact pairedAllocateBounded_sound resolve store
    { bytes := [], state := state } .unaddressable alignment limit h

theorem pairedAllocateBounded_empty_address_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (h : pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = true) :
    (∃ source target,
      allocateBounded store { bytes := [], state := state }
        (.address base) alignment limit = .ok source ∧
      allocateBounded (renameStore resolve store)
        (renameAllocationRequest resolve { bytes := [], state := state })
        (renamedPlacement resolve store.nextId (.address base)) alignment limit =
          .ok target) ∨
    (∃ fault,
      allocateBounded store { bytes := [], state := state }
        (.address base) alignment limit = .error fault ∧
      allocateBounded (renameStore resolve store)
        (renameAllocationRequest resolve { bytes := [], state := state })
        (renamedPlacement resolve store.nextId (.address base)) alignment limit =
          .error fault) := by
  apply pairedAllocateBounded_sound resolve store
    { bytes := [], state := state } (.address base) alignment limit
  exact h

theorem pairedAllocateBounded_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat)
    (hsource : allocateBounded store request placement alignment limit = .error sourceFault)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment limit = .ok target) :
    pairedAllocateBounded resolve store request placement alignment limit = false := by
  simp [pairedAllocateBounded, hsource, htarget]

theorem pairedAllocateBounded_empty_address_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (sourceFault : PlacementFault) (target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .error sourceFault)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment limit =
        .ok target) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = false := by
  exact pairedAllocateBounded_refusal_source resolve store
    { bytes := [], state := state } (.address base) alignment limit hsource htarget

theorem pairedAllocateBounded_empty_unaddressable_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (sourceFault : PlacementFault) (target : Store Tag State × Footprint)
    (hsource : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .error sourceFault)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
        .ok target) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      .unaddressable alignment limit = false := by
  exact pairedAllocateBounded_refusal_source resolve store
    { bytes := [], state := state } .unaddressable alignment limit hsource htarget

theorem pairedAllocateBounded_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat)
    (hsource : allocateBounded store request placement alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve request)
      (renamedPlacement resolve store.nextId placement) alignment limit = .error targetFault) :
    pairedAllocateBounded resolve store request placement alignment limit = false := by
  simp [pairedAllocateBounded, hsource, htarget]

theorem pairedAllocateBounded_empty_unaddressable_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (source : Store Tag State × Footprint) (targetFault : PlacementFault)
    (hsource : allocateBounded store { bytes := [], state := state }
      .unaddressable alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
        .error targetFault) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      .unaddressable alignment limit = false := by
  exact pairedAllocateBounded_refusal_target resolve store
    { bytes := [], state := state } .unaddressable alignment limit hsource htarget

theorem pairedAllocateBounded_empty_address_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (source : Store Tag State × Footprint) (targetFault : PlacementFault)
    (hsource : allocateBounded store { bytes := [], state := state }
      (.address base) alignment limit = .ok source)
    (htarget : allocateBounded (renameStore resolve store)
      (renameAllocationRequest resolve { bytes := [], state := state })
      (renamedPlacement resolve store.nextId (.address base)) alignment limit =
        .error targetFault) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = false := by
  exact pairedAllocateBounded_refusal_target resolve store
    { bytes := [], state := state } (.address base) alignment limit hsource htarget

theorem pairedAllocateBounded_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat)
    (hrefusal :
      (∃ sourceFault target,
        allocateBounded store request placement alignment limit = .error sourceFault ∧
        allocateBounded (renameStore resolve store) (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment limit = .ok target) ∨
      (∃ source targetFault,
        allocateBounded store request placement alignment limit = .ok source ∧
        allocateBounded (renameStore resolve store) (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) alignment limit = .error targetFault)) :
    pairedAllocateBounded resolve store request placement alignment limit = false := by
  rcases hrefusal with ⟨sourceFault, target, hsource, htarget⟩ |
    ⟨source, targetFault, hsource, htarget⟩
  · simp [pairedAllocateBounded, hsource, htarget]
  · simp [pairedAllocateBounded, hsource, htarget]

theorem pairedAllocateBounded_empty_address_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (base alignment limit : Nat)
    (hrefusal :
      (∃ sourceFault target,
        allocateBounded store { bytes := [], state := state }
          (.address base) alignment limit = .error sourceFault ∧
        allocateBounded (renameStore resolve store)
          (renameAllocationRequest resolve { bytes := [], state := state })
          (renamedPlacement resolve store.nextId (.address base)) alignment limit =
            .ok target) ∨
      (∃ source targetFault,
        allocateBounded store { bytes := [], state := state }
          (.address base) alignment limit = .ok source ∧
        allocateBounded (renameStore resolve store)
          (renameAllocationRequest resolve { bytes := [], state := state })
          (renamedPlacement resolve store.nextId (.address base)) alignment limit =
            .error targetFault)) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      (.address base) alignment limit = false := by
  apply pairedAllocateBounded_refusal resolve store
    { bytes := [], state := state } (.address base) alignment limit
  simpa using hrefusal

theorem pairedAllocateBounded_empty_unaddressable_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (state : State) (alignment limit : Nat)
    (hrefusal :
      (∃ sourceFault target,
        allocateBounded store { bytes := [], state := state }
          .unaddressable alignment limit = .error sourceFault ∧
        allocateBounded (renameStore resolve store)
          (renameAllocationRequest resolve { bytes := [], state := state })
          (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
            .ok target) ∨
      (∃ source targetFault,
        allocateBounded store { bytes := [], state := state }
          .unaddressable alignment limit = .ok source ∧
        allocateBounded (renameStore resolve store)
          (renameAllocationRequest resolve { bytes := [], state := state })
          (renamedPlacement resolve store.nextId .unaddressable) alignment limit =
            .error targetFault)) :
    pairedAllocateBounded resolve store { bytes := [], state := state }
      .unaddressable alignment limit = false := by
  apply pairedAllocateBounded_refusal resolve store
    { bytes := [], state := state } .unaddressable alignment limit
  simpa using hrefusal

def allocateMetadata (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    Option (AllocationMetadata Tag State TypeId × Footprint) :=
  match placement with
  | .fail => none
  | .address base =>
      if locations.length != request.bytes.length then none
      else
        some (AllocationMetadata.mk
                (Allocation.mk true (some base) request.bytes request.state)
                locations,
              footprint .metadata (Region.mk 0 0 request.bytes.length))
  | .unaddressable =>
      if locations.length != request.bytes.length then none
      else
        some (AllocationMetadata.mk
                (Allocation.mk true none request.bytes request.state)
                locations,
              footprint .metadata (Region.mk 0 0 request.bytes.length))

theorem allocateMetadata_result_contract
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : AllocationMetadata Tag State TypeId × Footprint) :
    allocateMetadata request locations placement = some result ↔
      match placement with
      | .fail => False
      | .address base =>
          locations.length = request.bytes.length ∧
          result =
            (AllocationMetadata.mk
              (Allocation.mk true (some base) request.bytes request.state)
              locations,
             footprint .metadata (Region.mk 0 0 request.bytes.length))
      | .unaddressable =>
          locations.length = request.bytes.length ∧
          result =
            (AllocationMetadata.mk
              (Allocation.mk true none request.bytes request.state)
              locations,
             footprint .metadata (Region.mk 0 0 request.bytes.length)) := by
  cases placement with
  | fail => simp [allocateMetadata]
  | address base =>
      by_cases hlength : locations.length = request.bytes.length
      · simp [allocateMetadata, hlength]
        constructor <;> intro h <;> exact h.symm
      · simp [allocateMetadata, hlength]
  | unaddressable =>
      by_cases hlength : locations.length = request.bytes.length
      · simp [allocateMetadata, hlength]
        constructor <;> intro h <;> exact h.symm
      · simp [allocateMetadata, hlength]

theorem allocateMetadata_failure_contract
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    allocateMetadata request locations placement = none ↔
      match placement with
      | .fail => True
      | .address _ | .unaddressable =>
          locations.length ≠ request.bytes.length := by
  cases placement with
  | fail => simp [allocateMetadata]
  | address base =>
      by_cases hlength : locations.length = request.bytes.length
      · simp [allocateMetadata, hlength]
      · simp [allocateMetadata, hlength]
  | unaddressable =>
      by_cases hlength : locations.length = request.bytes.length
      · simp [allocateMetadata, hlength]
      · simp [allocateMetadata, hlength]

theorem allocateMetadata_preserves_lengths
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : allocateMetadata request locations placement = some result) :
    result.1.locations.length = result.1.allocation.bytes.length := by
  cases placement <;> simp [allocateMetadata] at hresult
  · rcases hresult with ⟨hEq, rfl⟩
    exact hEq
  · rcases hresult with ⟨hEq, rfl⟩
    exact hEq

theorem allocateMetadata_result_footprint
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : allocateMetadata request locations placement = some result) :
    result.2 = footprint .metadata
      (Region.mk 0 0 request.bytes.length) := by
  cases placement <;> simp [allocateMetadata] at hresult
  · rcases hresult with ⟨_, rfl⟩
    rfl
  · rcases hresult with ⟨_, rfl⟩
    rfl

theorem allocateMetadata_result_payload
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : allocateMetadata request locations placement = some result) :
    result.1.allocation.live = true ∧
      result.1.locations = locations ∧
      result.1.allocation.bytes = request.bytes ∧
      result.1.allocation.state = request.state := by
  cases placement <;> simp [allocateMetadata] at hresult
  · rcases hresult with ⟨_, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rcases hresult with ⟨_, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem allocateMetadata_result_wellFormed
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hbytes : bytesWf 0 request.bytes)
    (hresult : allocateMetadata request locations placement = some result) :
    result.1.wellFormed 0 := by
  cases placement <;> simp [allocateMetadata, AllocationMetadata.wellFormed] at hresult
  · rcases hresult with ⟨hEq, rfl⟩
    exact ⟨hbytes, hEq⟩
  · rcases hresult with ⟨hEq, rfl⟩
    exact ⟨hbytes, hEq⟩

theorem allocateMetadata_address_success
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (base : Nat)
    (hsame : locations.length = request.bytes.length) :
    allocateMetadata request locations (.address base) =
      some ({ allocation :=
                { live := true, address := some base,
                  bytes := request.bytes, state := request.state },
              locations },
            footprint .metadata (Region.mk 0 0 request.bytes.length)) := by
  simp [allocateMetadata, hsame]

theorem allocateMetadata_unaddressable_success
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (hsame : locations.length = request.bytes.length) :
    allocateMetadata request locations .unaddressable =
      some ({ allocation :=
                { live := true, address := none,
                  bytes := request.bytes, state := request.state },
              locations },
            footprint .metadata (Region.mk 0 0 request.bytes.length)) := by
  simp [allocateMetadata, hsame]

theorem allocateMetadata_address_rejects_length_mismatch
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (base : Nat)
    (hmismatch : locations.length ≠ request.bytes.length) :
    allocateMetadata request locations (.address base) = none := by
  simp [allocateMetadata, hmismatch]

theorem allocateMetadata_unaddressable_rejects_length_mismatch
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (hmismatch : locations.length ≠ request.bytes.length) :
    allocateMetadata request locations .unaddressable = none := by
  simp [allocateMetadata, hmismatch]

theorem allocateMetadata_rejects_failure
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) :
    allocateMetadata request locations .fail = none := by
  rfl

def pairedAllocateMetadata (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) : Bool :=
  match allocateMetadata request locations placement,
    allocateMetadata (renameAllocationRequest resolve request) locations
      (renamedPlacement resolve id placement) with
  | some _, some _ => true
  | none, none => true
  | _, _ => false

theorem pairedAllocateMetadata_both_success
    (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (hsource : allocateMetadata request locations placement = some source)
    (htarget : allocateMetadata (renameAllocationRequest resolve request) locations
      (renamedPlacement resolve id placement) = some target) :
    pairedAllocateMetadata resolve id request locations placement = true := by
  simp [pairedAllocateMetadata, hsource, htarget]

theorem pairedAllocateMetadata_empty_both_success {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) (placement : Placement)
    (source target : AllocationMetadata Tag State TypeId × Footprint)
    (hsource : allocateMetadata (Tag := Tag) (TypeId := TypeId)
      { bytes := [], state := state } [] placement = some source)
    (htarget : allocateMetadata (Tag := Tag) (TypeId := TypeId)
      (renameAllocationRequest resolve { bytes := [], state := state }) []
      (renamedPlacement resolve id placement) = some target) :
    pairedAllocateMetadata (Tag := Tag) (TypeId := TypeId) resolve id
      { bytes := [], state := state } [] placement = true := by
  exact pairedAllocateMetadata_both_success resolve id
    { bytes := [], state := state } [] placement hsource htarget

theorem pairedAllocateMetadata_both_refused
    (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (hsource : allocateMetadata request locations placement = none)
    (htarget : allocateMetadata (renameAllocationRequest resolve request) locations
      (renamedPlacement resolve id placement) = none) :
    pairedAllocateMetadata resolve id request locations placement = true := by
  simp [pairedAllocateMetadata, hsource, htarget]

theorem pairedAllocateMetadata_empty_both_refused {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) (placement : Placement)
    (hsource : allocateMetadata (Tag := Tag) (TypeId := TypeId)
      { bytes := [], state := state } [] placement = none)
    (htarget : allocateMetadata (Tag := Tag) (TypeId := TypeId)
      (renameAllocationRequest resolve { bytes := [], state := state }) []
      (renamedPlacement resolve id placement) = none) :
    pairedAllocateMetadata (Tag := Tag) (TypeId := TypeId) resolve id
      { bytes := [], state := state } [] placement = true := by
  exact pairedAllocateMetadata_both_refused resolve id
    { bytes := [], state := state } [] placement hsource htarget

theorem pairedAllocateMetadata_empty_true {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) (placement : Placement) :
    pairedAllocateMetadata (Tag := Tag) (TypeId := TypeId) resolve id
      { bytes := [], state := state } [] placement = true := by
  cases placement <;>
    simp [pairedAllocateMetadata, allocateMetadata, renameAllocationRequest,
      renamedPlacement]

theorem pairedAllocateMetadata_empty_address_result_shape {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) (base : Nat) :
    allocateMetadata (Tag := Tag) (TypeId := TypeId)
        { bytes := [], state := state } [] (.address base) =
      some ({ allocation :=
                { live := true, address := some base,
                  bytes := [], state := state },
              locations := [] },
            footprint .metadata (Region.mk 0 0 0)) ∧
    allocateMetadata (Tag := Tag) (TypeId := TypeId)
        (renameAllocationRequest resolve { bytes := [], state := state }) []
        (renamedPlacement resolve id (.address base)) =
      some ({ allocation :=
                { live := true, address := some (resolve id),
                  bytes := [], state := state },
              locations := [] },
            footprint .metadata (Region.mk 0 0 0)) := by
  simp [allocateMetadata, renameAllocationRequest, renamedPlacement]

theorem pairedAllocateMetadata_empty_unaddressable_result_shape {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) :
    allocateMetadata (Tag := Tag) (TypeId := TypeId)
        { bytes := [], state := state } [] .unaddressable =
      some ({ allocation :=
                { live := true, address := none,
                  bytes := [], state := state },
              locations := [] },
            footprint .metadata (Region.mk 0 0 0)) ∧
    allocateMetadata (Tag := Tag) (TypeId := TypeId)
        (renameAllocationRequest resolve { bytes := [], state := state }) []
        (renamedPlacement resolve id .unaddressable) =
      some ({ allocation :=
                { live := true, address := none,
                  bytes := [], state := state },
              locations := [] },
            footprint .metadata (Region.mk 0 0 0)) := by
  simp [allocateMetadata, renameAllocationRequest, renamedPlacement]

theorem pairedAllocateMetadata_empty_result_shape {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) (placement : Placement) :
    match placement with
    | .address base =>
        allocateMetadata (Tag := Tag) (TypeId := TypeId)
            { bytes := [], state := state } [] (.address base) =
          some ({ allocation :=
                    { live := true, address := some base,
                      bytes := [], state := state },
                  locations := [] },
                footprint .metadata (Region.mk 0 0 0)) ∧
        allocateMetadata (Tag := Tag) (TypeId := TypeId)
            (renameAllocationRequest resolve { bytes := [], state := state }) []
            (renamedPlacement resolve id (.address base)) =
          some ({ allocation :=
                    { live := true, address := some (resolve id),
                      bytes := [], state := state },
                  locations := [] },
                footprint .metadata (Region.mk 0 0 0))
    | .unaddressable =>
        allocateMetadata (Tag := Tag) (TypeId := TypeId)
            { bytes := [], state := state } [] .unaddressable =
          some ({ allocation :=
                    { live := true, address := none,
                      bytes := [], state := state },
                  locations := [] },
                footprint .metadata (Region.mk 0 0 0)) ∧
        allocateMetadata (Tag := Tag) (TypeId := TypeId)
            (renameAllocationRequest resolve { bytes := [], state := state }) []
            (renamedPlacement resolve id .unaddressable) =
          some ({ allocation :=
                    { live := true, address := none,
                      bytes := [], state := state },
                  locations := [] },
                footprint .metadata (Region.mk 0 0 0))
    | .fail =>
        allocateMetadata (Tag := Tag) (TypeId := TypeId)
            { bytes := [], state := state } [] .fail = none ∧
        allocateMetadata (Tag := Tag) (TypeId := TypeId)
            (renameAllocationRequest resolve { bytes := [], state := state }) []
            (renamedPlacement resolve id .fail) = none := by
  cases placement <;>
    simp [allocateMetadata, renameAllocationRequest, renamedPlacement]

theorem pairedAllocateMetadata_sound
    (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (h : pairedAllocateMetadata resolve id request locations placement = true) :
    (∃ source target,
      allocateMetadata request locations placement = some source ∧
      allocateMetadata (renameAllocationRequest resolve request) locations
        (renamedPlacement resolve id placement) = some target) ∨
    (allocateMetadata request locations placement = none ∧
      allocateMetadata (renameAllocationRequest resolve request) locations
        (renamedPlacement resolve id placement) = none) := by
  cases hs : allocateMetadata request locations placement with
  | none =>
      cases ht : allocateMetadata (renameAllocationRequest resolve request) locations
          (renamedPlacement resolve id placement) with
      | none => exact Or.inr ⟨rfl, rfl⟩
      | some target => simp [pairedAllocateMetadata, hs, ht] at h
  | some source =>
      cases ht : allocateMetadata (renameAllocationRequest resolve request) locations
          (renamedPlacement resolve id placement) with
      | none => simp [pairedAllocateMetadata, hs, ht] at h
      | some target => exact Or.inl ⟨source, target, rfl, rfl⟩

theorem pairedAllocateMetadata_empty_sound {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) (placement : Placement)
    (h : pairedAllocateMetadata (Tag := Tag) (TypeId := TypeId) resolve id
      { bytes := [], state := state } [] placement = true) :
    (∃ source target,
      allocateMetadata (Tag := Tag) (TypeId := TypeId)
          { bytes := [], state := state } [] placement =
            some (source : AllocationMetadata Tag State TypeId × Footprint) ∧
      allocateMetadata (Tag := Tag) (TypeId := TypeId)
          (renameAllocationRequest resolve { bytes := [], state := state }) []
        (renamedPlacement resolve id placement) = some target) ∨
    (allocateMetadata (Tag := Tag) (TypeId := TypeId)
          { bytes := [], state := state } [] placement = none ∧
      allocateMetadata (Tag := Tag) (TypeId := TypeId)
          (renameAllocationRequest resolve { bytes := [], state := state }) []
        (renamedPlacement resolve id placement) = none) := by
  exact pairedAllocateMetadata_sound resolve id
    { bytes := [], state := state } [] placement h

theorem pairedAllocateMetadata_refusal_source
    (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (hsource : allocateMetadata request locations placement = some source)
    (htarget : allocateMetadata (renameAllocationRequest resolve request) locations
      (renamedPlacement resolve id placement) = none) :
    pairedAllocateMetadata resolve id request locations placement = false := by
  simp [pairedAllocateMetadata, hsource, htarget]

theorem pairedAllocateMetadata_empty_refusal_source {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) (placement : Placement)
    (source : AllocationMetadata Tag State TypeId × Footprint)
    (hsource : allocateMetadata (Tag := Tag) (TypeId := TypeId)
      { bytes := [], state := state } [] placement =
        some (source : AllocationMetadata Tag State TypeId × Footprint))
    (htarget : allocateMetadata (Tag := Tag) (TypeId := TypeId)
      (renameAllocationRequest resolve { bytes := [], state := state }) []
      (renamedPlacement resolve id placement) = none) :
    pairedAllocateMetadata (Tag := Tag) (TypeId := TypeId) resolve id
      { bytes := [], state := state } [] placement = false := by
  exact pairedAllocateMetadata_refusal_source resolve id
    { bytes := [], state := state } [] placement hsource htarget

theorem pairedAllocateMetadata_refusal_target
    (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (hsource : allocateMetadata request locations placement = none)
    (htarget : allocateMetadata (renameAllocationRequest resolve request) locations
      (renamedPlacement resolve id placement) = some target) :
    pairedAllocateMetadata resolve id request locations placement = false := by
  simp [pairedAllocateMetadata, hsource, htarget]

theorem pairedAllocateMetadata_empty_refusal_target {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) (placement : Placement)
    (target : AllocationMetadata Tag State TypeId × Footprint)
    (hsource : allocateMetadata (Tag := Tag) (TypeId := TypeId)
      { bytes := [], state := state } [] placement = none)
    (htarget : allocateMetadata (Tag := Tag) (TypeId := TypeId)
      (renameAllocationRequest resolve { bytes := [], state := state }) []
      (renamedPlacement resolve id placement) = some target) :
    pairedAllocateMetadata (Tag := Tag) (TypeId := TypeId) resolve id
      { bytes := [], state := state } [] placement = false := by
  exact pairedAllocateMetadata_refusal_target resolve id
    { bytes := [], state := state } [] placement hsource htarget

theorem pairedAllocateMetadata_refusal
    (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (hrefusal : allocateMetadata request locations placement = none ∧
      allocateMetadata (renameAllocationRequest resolve request) locations
        (renamedPlacement resolve id placement) = some target ∨
      allocateMetadata request locations placement = some source ∧
      allocateMetadata (renameAllocationRequest resolve request) locations
        (renamedPlacement resolve id placement) = none) :
    pairedAllocateMetadata resolve id request locations placement = false := by
  rcases hrefusal with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · simp [pairedAllocateMetadata, hsource, htarget]
  · simp [pairedAllocateMetadata, hsource, htarget]

theorem pairedAllocateMetadata_failure_contract
    (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    pairedAllocateMetadata resolve id request locations placement = false ↔
      (allocateMetadata request locations placement = none ∧
        allocateMetadata (renameAllocationRequest resolve request) locations
          (renamedPlacement resolve id placement) ≠ none) ∨
      (allocateMetadata request locations placement ≠ none ∧
        allocateMetadata (renameAllocationRequest resolve request) locations
          (renamedPlacement resolve id placement) = none) := by
  cases hs : allocateMetadata request locations placement with
  | none =>
      cases ht : allocateMetadata (renameAllocationRequest resolve request) locations
          (renamedPlacement resolve id placement) with
      | none => simp [pairedAllocateMetadata, hs, ht]
      | some target => simp [pairedAllocateMetadata, hs, ht]
  | some source =>
      cases ht : allocateMetadata (renameAllocationRequest resolve request) locations
          (renamedPlacement resolve id placement) with
      | none => simp [pairedAllocateMetadata, hs, ht]
      | some target => simp [pairedAllocateMetadata, hs, ht]

theorem pairedAllocateMetadata_empty_refusal {Tag TypeId : Type}
    (resolve : AllocId → Nat) (id : AllocId)
    (state : State) (placement : Placement)
    (hrefusal :
      (∃ source target : AllocationMetadata Tag State TypeId × Footprint,
        allocateMetadata (Tag := Tag) (TypeId := TypeId)
            { bytes := [], state := state } [] placement = none ∧
          allocateMetadata (Tag := Tag) (TypeId := TypeId)
            (renameAllocationRequest resolve { bytes := [], state := state }) []
            (renamedPlacement resolve id placement) = some target) ∨
      (∃ source target : AllocationMetadata Tag State TypeId × Footprint,
        allocateMetadata (Tag := Tag) (TypeId := TypeId)
            { bytes := [], state := state } [] placement = some source ∧
          allocateMetadata (Tag := Tag) (TypeId := TypeId)
            (renameAllocationRequest resolve { bytes := [], state := state }) []
            (renamedPlacement resolve id placement) = none)) :
    pairedAllocateMetadata (Tag := Tag) (TypeId := TypeId) resolve id
      { bytes := [], state := state } [] placement = false := by
  rcases hrefusal with ⟨source, target, hsource, htarget⟩ |
    ⟨source, target, hsource, htarget⟩
  · exact pairedAllocateMetadata_refusal_target resolve id
      { bytes := [], state := state } [] placement hsource htarget
  · exact pairedAllocateMetadata_refusal_source resolve id
      { bytes := [], state := state } [] placement hsource htarget

#guard (allocate (Tag := Unit) (State := Unit)
  { allocations := [], nextId := 0 }
  { bytes := [Byte.uninitialized], state := () } (Placement.address 16)).isSome

def storeByte (store : Store Tag State) (id offset : Nat)
    (byte : Byte Tag) : Option (Store Tag State × Footprint) := do
  let allocation ← lookup store id
  if !allocation.live then none
  else if offset ≥ allocation.bytes.length then none
  else
    let bytes := listSet allocation.bytes offset byte
    let updated := { allocation with bytes := bytes }
    let allocations := store.allocations.map (fun entry =>
      if entry.1 == id then (id, updated) else entry)
    some ({ store with allocations := allocations }, footprint .write
      { allocation := id, offset := offset, width := 1 })

theorem storeByte_empty_none
    {Tag State : Type} (id offset : Nat) (byte : Byte Tag) :
    storeByte ({ allocations := [], nextId := 0 } : Store Tag State) id offset byte = none := by
  rfl

theorem storeByte_success_payload
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (result : Store Tag State × Footprint)
    (hresult : storeByte store id offset byte = some result) :
    ∃ allocation,
      lookup store id = some allocation ∧
      result.1 = { store with allocations := store.allocations.map (fun entry =>
        if entry.1 == id then
          (id, { allocation with bytes := listSet allocation.bytes offset byte })
        else entry) } := by
  cases hlookup : lookup store id with
  | none => simp [storeByte, hlookup] at hresult
  | some allocation =>
      cases hlive : allocation.live with
      | false => simp [storeByte, hlookup, hlive] at hresult
      | true =>
          by_cases hoffset : offset ≥ allocation.bytes.length
          · simp [storeByte, hlookup, hlive, hoffset] at hresult
          · simp [storeByte, hlookup, hlive, hoffset] at hresult
            refine ⟨allocation, rfl, ?_⟩
            simpa [hlive] using congrArg (fun pair => pair.1) hresult.symm

theorem storeByte_preserves_wellFormed
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf id (listSet
      ((lookup store id).map (fun allocation => allocation.bytes) |>.getD [])
      offset byte))
    (hresult : storeByte store id offset byte = some result) :
    WellFormed result.1 := by
  cases hlookup : lookup store id with
  | none => simp [storeByte, hlookup] at hresult
  | some allocation =>
      cases hlive : allocation.live with
      | false => simp [storeByte, hlookup, hlive] at hresult
      | true =>
          by_cases hoffset : offset ≥ allocation.bytes.length
          · simp [storeByte, hlookup, hlive, hoffset] at hresult
          · simp [storeByte, hlookup, hlive, hoffset] at hresult
            simp [hlookup] at hbytes
            rcases hresult with ⟨rfl, rfl⟩
            unfold WellFormed at hstore ⊢
            have map_wf : ∀ entries : List (AllocId × Allocation Tag State),
                allocationsWf entries →
                allocationsWf (entries.map (fun entry =>
                  if entry.1 = id then
                    (id, { allocation with bytes := listSet allocation.bytes offset byte })
                  else entry)) := by
              intro entries
              induction entries with
              | nil => intro _; simp [allocationsWf]
              | cons entry rest ih =>
                  cases entry with
                  | mk entryId oldAllocation =>
                      intro hentries
                      by_cases hid : entryId = id
                      · subst entryId
                        simp only [List.map_cons, if_pos, allocationsWf]
                        exact ⟨hbytes, ih hentries.2⟩
                      · simp only [List.map_cons, if_neg hid, allocationsWf] at hentries ⊢
                        exact ⟨hentries.1, ih hentries.2⟩
            simpa [hlive] using map_wf store.allocations hstore

theorem storeByte_result_contract
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (result : Store Tag State × Footprint)
    (hresult : storeByte store id offset byte = some result) :
    (∃ allocation,
      lookup store id = some allocation ∧
      allocation.live = true ∧
      offset < allocation.bytes.length ∧
      result = ({ store with allocations := store.allocations.map (fun entry =>
        if entry.1 == id then
          (id, { allocation with bytes := listSet allocation.bytes offset byte })
        else entry) },
        footprint .write { allocation := id, offset := offset, width := 1 })) := by
  cases hlookup : lookup store id with
  | none => simp [storeByte, hlookup] at hresult
  | some allocation =>
      cases hlive : allocation.live with
      | false => simp [storeByte, hlookup, hlive] at hresult
      | true =>
          by_cases hoffset : offset ≥ allocation.bytes.length
          · simp [storeByte, hlookup, hlive, hoffset] at hresult
          · refine ⟨allocation, rfl, hlive, Nat.lt_of_not_ge hoffset, ?_⟩
            simpa [storeByte, hlookup, hlive, hoffset] using hresult.symm

theorem storeByte_failure_contract
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag) :
    storeByte store id offset byte = none ↔
      lookup store id = none ∨
      (∃ allocation,
        lookup store id = some allocation ∧
        (allocation.live = false ∨ offset ≥ allocation.bytes.length)) := by
  constructor
  · intro hnone
    cases hlookup : lookup store id with
    | none => exact Or.inl rfl
    | some allocation =>
        right
        refine ⟨allocation, rfl, ?_⟩
        cases hlive : allocation.live with
        | false => exact Or.inl rfl
        | true =>
            by_cases hoffset : offset ≥ allocation.bytes.length
            · exact Or.inr hoffset
            · simp [storeByte, hlookup, hlive, hoffset] at hnone
  · intro hfailure
    rcases hfailure with hlookup | ⟨allocation, hlookup, hlive | hoffset⟩
    · simp [storeByte, hlookup]
    · simp [storeByte, hlookup, hlive]
    · simp [storeByte, hlookup, hoffset]

def storeTransitionCorresponds (resolve : AllocId → Nat)
    (source target : Store Tag State)
    (sourceResult targetResult : Store Tag State × Footprint) : Prop :=
  target = renameStore resolve source ∧
    targetResult.1 = renameStore resolve sourceResult.1 ∧
    targetResult.2 = sourceResult.2

def pairedStoreByte (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : AllocId) (byte : Byte Tag) :
    Option ((Store Tag State × Footprint) × (Store Tag State × Footprint)) := do
  let sourceResult ← storeByte store id offset byte
  let targetResult ← storeByte (renameStore resolve store) id offset (renameByte resolve byte)
  some (sourceResult, targetResult)

theorem pairedStoreByte_empty_none
    {Tag State : Type} (resolve : AllocId → Nat)
    (id offset : Nat) (byte : Byte Tag) :
    pairedStoreByte resolve
      ({ allocations := [], nextId := 0 } : Store Tag State)
      id offset byte = none := by
  rfl

theorem pairedStoreByte_decompose
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedStoreByte resolve store id offset byte = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) := by
  cases hs : storeByte store id offset byte with
  | none => simp [pairedStoreByte, hs] at hresult
  | some sourceResult =>
      cases ht : storeByte (renameStore resolve store) id offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreByte, hs, ht] at hresult
      | some targetResult =>
          rw [pairedStoreByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := by
            simpa only [Option.bind_some] using Option.some.inj hresult
          exact ⟨sourceResult, targetResult, hpair.symm⟩

theorem pairedStoreByte_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedStoreByte resolve store id offset byte = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      storeByte store id offset byte = some sourceResult ∧
      storeByte (renameStore resolve store) id offset (renameByte resolve byte) =
        some targetResult := by
  cases hs : storeByte store id offset byte with
  | none => simp [pairedStoreByte, hs] at hresult
  | some sourceResult =>
      cases ht : storeByte (renameStore resolve store) id offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedStoreByte, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨sourceResult, targetResult, rfl, by simpa using hs,
            by simpa using ht⟩

theorem pairedStoreByte_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (hsource : storeByte store id offset byte = none) :
    pairedStoreByte resolve store id offset byte = none := by
  simp [pairedStoreByte, hsource]

theorem pairedStoreByte_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (htarget : storeByte (renameStore resolve store) id offset
      (renameByte resolve byte) = none) :
    pairedStoreByte resolve store id offset byte = none := by
  simp [pairedStoreByte, htarget]

theorem pairedStoreByte_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (hrefusal : storeByte store id offset byte = none ∨
      storeByte (renameStore resolve store) id offset (renameByte resolve byte) = none) :
    pairedStoreByte resolve store id offset byte = none := by
  rcases hrefusal with hsource | htarget
  · simp [pairedStoreByte, hsource]
  · simp [pairedStoreByte, htarget]

theorem pairedStoreByte_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : AllocId) (byte : Byte Tag) :
    pairedStoreByte resolve store id offset byte = none ↔
      storeByte store id offset byte = none ∨
      storeByte (renameStore resolve store) id offset (renameByte resolve byte) = none := by
  cases hs : storeByte store id offset byte with
  | none =>
      simp [pairedStoreByte, hs]
  | some sourceResult =>
      cases ht : storeByte (renameStore resolve store) id offset (renameByte resolve byte) with
      | none => simp [pairedStoreByte, hs, ht]
      | some targetResult => simp [pairedStoreByte, hs, ht]

theorem pairedStoreRepresentationLoadMetadataByte_sound
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (result : (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))))
    (hresult : pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice =
      some result) :
    ∃ sourceStore sourceLoad targetStore targetLoad,
      result = ((sourceStore, sourceLoad), (targetStore, targetLoad)) ∧
      storeMetadataByte metadata offset byte = some sourceStore ∧
      storeMetadataByte (renameMetadata resolve id metadata) offset (renameByte resolve byte) =
        some targetStore ∧
      representationLoadMetadataByte sourceStore.1 offset choice = some sourceLoad ∧
      representationLoadMetadataByte targetStore.1 offset choice = some targetLoad := by
  cases hs : storeMetadataByte metadata offset byte with
  | none => simp [pairedStoreRepresentationLoadMetadataByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeMetadataByte (renameMetadata resolve id metadata) offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht] at hresult
      | some targetStore =>
          cases hsl : representationLoadMetadataByte sourceStore.1 offset choice with
          | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl] at hresult
          | some sourceLoad =>
              cases htl : representationLoadMetadataByte targetStore.1 offset choice with
              | none => simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
              | some targetLoad =>
                  simp [pairedStoreRepresentationLoadMetadataByte, hs, ht, hsl, htl] at hresult
                  exact ⟨sourceStore, sourceLoad, targetStore, targetLoad,
                    hresult.symm, by simpa using hs, by simpa using ht,
                    by simpa using hsl, by simpa using htl⟩

theorem pairedStoreByte_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hsourceStore : WellFormed store)
    (hsourceBytes : bytesWf id (listSet
      ((lookup store id).map (fun allocation => allocation.bytes) |>.getD [])
      offset byte))
    (htargetBytes : bytesWf id (listSet
      ((lookup (renameStore resolve store) id).map
        (fun allocation => allocation.bytes) |>.getD [])
      offset (renameByte resolve byte)))
    (hresult : pairedStoreByte resolve store id offset byte = some result) :
    WellFormed result.1.1 ∧ WellFormed result.2.1 := by
  cases hs : storeByte store id offset byte with
  | none => simp [pairedStoreByte, hs] at hresult
  | some sourceResult =>
      cases ht : storeByte (renameStore resolve store) id offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedStoreByte, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨storeByte_preserves_wellFormed store id offset byte sourceResult
              hsourceStore hsourceBytes hs,
            storeByte_preserves_wellFormed (renameStore resolve store) id offset
              (renameByte resolve byte) targetResult
              (renameStore_preserves_wellFormed resolve store hsourceStore)
              htargetBytes ht⟩

def loadByte (store : Store Tag State) (id offset : Nat) :
    Option (Byte Tag × Footprint) := do
  let allocation ← lookup store id
  if !allocation.live then none
  else
    let byte ← allocation.bytes[offset]?
    some (byte, footprint .read { allocation := id, offset := offset, width := 1 })

theorem loadByte_empty_none
    {Tag State : Type} (id offset : Nat) :
    loadByte ({ allocations := [], nextId := 0 } : Store Tag State) id offset = none := by
  rfl

theorem loadByte_success_value
    (store : Store Tag State) (id offset : Nat)
    (result : Byte Tag × Footprint)
    (hresult : loadByte store id offset = some result) :
    ∃ allocation,
      lookup store id = some allocation ∧
      allocation.live = true ∧
      allocation.bytes[offset]? = some result.1 := by
  cases hlookup : lookup store id with
  | none => simp [loadByte, hlookup] at hresult
  | some allocation =>
      cases hlive : allocation.live with
      | false => simp [loadByte, hlookup, hlive] at hresult
      | true =>
          cases hbyte : allocation.bytes[offset]? with
          | none => simp [loadByte, hlookup, hlive, hbyte] at hresult
          | some stored =>
              simp [loadByte, hlookup, hlive, hbyte] at hresult
              rcases hresult with ⟨rfl, rfl⟩
              exact ⟨allocation, rfl, hlive, hbyte⟩

theorem loadByte_result_contract
    (store : Store Tag State) (id offset : Nat)
    (result : Byte Tag × Footprint)
    (hresult : loadByte store id offset = some result) :
    ∃ allocation byte,
      lookup store id = some allocation ∧
      allocation.live = true ∧
      allocation.bytes[offset]? = some byte ∧
      result = (byte, footprint .read
        { allocation := id, offset := offset, width := 1 }) := by
  cases hlookup : lookup store id with
  | none => simp [loadByte, hlookup] at hresult
  | some allocation =>
      cases hlive : allocation.live with
      | false => simp [loadByte, hlookup, hlive] at hresult
      | true =>
          cases hbyte : allocation.bytes[offset]? with
          | none => simp [loadByte, hlookup, hlive, hbyte] at hresult
          | some byte =>
              refine ⟨allocation, byte, rfl, hlive, hbyte, ?_⟩
              simpa [loadByte, hlookup, hlive, hbyte] using hresult.symm

theorem loadByte_failure_contract
    (store : Store Tag State) (id offset : Nat) :
    loadByte store id offset = none ↔
      lookup store id = none ∨
      (∃ allocation,
        lookup store id = some allocation ∧
        (allocation.live = false ∨ allocation.bytes[offset]? = none)) := by
  constructor
  · intro hnone
    cases hlookup : lookup store id with
    | none => exact Or.inl rfl
    | some allocation =>
        right
        refine ⟨allocation, rfl, ?_⟩
        cases hlive : allocation.live with
        | false => exact Or.inl rfl
        | true =>
            cases hvalue : allocation.bytes[offset]? with
            | none => exact Or.inr rfl
            | some stored => simp [loadByte, hlookup, hlive, hvalue] at hnone
  · intro hfailure
    rcases hfailure with hlookup | ⟨allocation, hlookup, hlive | hbyte⟩
    · simp [loadByte, hlookup]
    · simp [loadByte, hlookup, hlive]
    · simp [loadByte, hlookup, hbyte]

def loadTransitionCorresponds (resolve : AllocId → Nat)
    (source target : Store Tag State)
    (sourceResult targetResult : Byte Tag × Footprint) : Prop :=
  target = renameStore resolve source ∧
    targetResult.1 = renameByte resolve sourceResult.1 ∧
    targetResult.2 = sourceResult.2

def pairedLoadByte (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) :
    Option ((Byte Tag × Footprint) × (Byte Tag × Footprint)) := do
  let sourceResult ← loadByte store id offset
  let targetResult ← loadByte (renameStore resolve store) id offset
  some (sourceResult, targetResult)

theorem pairedLoadByte_empty_none
    {Tag State : Type} (resolve : AllocId → Nat)
    (id offset : Nat) :
    pairedLoadByte resolve
      ({ allocations := [], nextId := 0 } : Store Tag State)
      id offset = none := by
  rfl

theorem pairedLoadByte_decompose
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedLoadByte resolve store id offset = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) := by
  cases hs : loadByte store id offset with
  | none => simp [pairedLoadByte, hs] at hresult
  | some sourceResult =>
      cases ht : loadByte (renameStore resolve store) id offset with
      | none => simp [pairedLoadByte, hs, ht] at hresult
      | some targetResult =>
          rw [pairedLoadByte, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := by
            simpa only [Option.bind_some] using Option.some.inj hresult
          exact ⟨sourceResult, targetResult, hpair.symm⟩

theorem pairedLoadByte_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedLoadByte resolve store id offset = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      loadByte store id offset = some sourceResult ∧
      loadByte (renameStore resolve store) id offset = some targetResult := by
  cases hs : loadByte store id offset with
  | none => simp [pairedLoadByte, hs] at hresult
  | some sourceResult =>
      cases ht : loadByte (renameStore resolve store) id offset with
      | none => simp [pairedLoadByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedLoadByte, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨sourceResult, targetResult, rfl, by simpa using hs,
            by simpa using ht⟩

theorem pairedLoadByte_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (hsource : loadByte store id offset = none) :
    pairedLoadByte resolve store id offset = none := by
  simp [pairedLoadByte, hsource]

theorem pairedLoadByte_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (htarget : loadByte (renameStore resolve store) id offset = none) :
    pairedLoadByte resolve store id offset = none := by
  simp [pairedLoadByte, htarget]

theorem pairedLoadByte_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (hrefusal : loadByte store id offset = none ∨
      loadByte (renameStore resolve store) id offset = none) :
    pairedLoadByte resolve store id offset = none := by
  rcases hrefusal with hsource | htarget
  · simp [pairedLoadByte, hsource]
  · simp [pairedLoadByte, htarget]

theorem pairedLoadByte_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) :
    pairedLoadByte resolve store id offset = none ↔
      loadByte store id offset = none ∨
      loadByte (renameStore resolve store) id offset = none := by
  cases hs : loadByte store id offset with
  | none => simp [pairedLoadByte, hs]
  | some sourceResult =>
      cases ht : loadByte (renameStore resolve store) id offset with
      | none => simp [pairedLoadByte, hs, ht]
      | some targetResult => simp [pairedLoadByte, hs, ht]

theorem pairedLoadByte_value_correspondence
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedLoadByte resolve store id offset = some result) :
    result.2.1 = renameByte resolve result.1.1 := by
  have map_getElem : ∀ (bytes : List (Byte Tag)) (index : Nat) (byte : Byte Tag),
      bytes[index]? = some byte →
      (bytes.map (renameByte resolve))[index]? = some (renameByte resolve byte) := by
    intro bytes
    induction bytes with
    | nil => intro index byte h; simp at h
    | cons head rest ih =>
        intro index byte h
        cases index with
        | zero =>
            have h' : head = byte := by simpa using h
            simpa [h']
        | succ index =>
            apply ih index byte
            simpa using h
  cases hs : loadByte store id offset with
  | none => simp [pairedLoadByte, hs] at hresult
  | some sourceResult =>
      cases ht : loadByte (renameStore resolve store) id offset with
      | none => simp [pairedLoadByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedLoadByte, hs, ht] at hresult
          rcases hresult with rfl
          obtain ⟨sourceAllocation, hsourceLookup, _, hsourceIndex⟩ :=
            loadByte_success_value store id offset sourceResult hs
          obtain ⟨targetAllocation, htargetLookup, _, htargetIndex⟩ :=
            loadByte_success_value (renameStore resolve store) id offset targetResult ht
          have htargetLookup' :
              lookup (renameStore resolve store) id =
                some (renameAllocationValue resolve id sourceAllocation) := by
            rw [lookup_renameStore, hsourceLookup]
            rfl
          have hallocEq : targetAllocation = renameAllocationValue resolve id sourceAllocation := by
            exact (Option.some.inj (htargetLookup'.symm.trans htargetLookup)).symm
          rw [hallocEq, renameAllocationValue] at htargetIndex
          have hmapped := map_getElem sourceAllocation.bytes offset sourceResult.1 hsourceIndex
          change targetResult.1 = renameByte resolve sourceResult.1
          exact Option.some.inj (htargetIndex.symm.trans hmapped)

structure StoreLoadPair (Tag State : Type) where
  sourceStore : Store Tag State × Footprint
  targetStore : Store Tag State × Footprint
  sourceLoad : Byte Tag × Footprint
  targetLoad : Byte Tag × Footprint
deriving Repr

def pairedStoreLoadByte (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag) : Option (StoreLoadPair Tag State) := do
  let stores ← pairedStoreByte resolve store id offset byte
  let sourceLoad ← loadByte stores.1.1 id offset
  let targetLoad ← loadByte stores.2.1 id offset
  some { sourceStore := stores.1, targetStore := stores.2
         sourceLoad := sourceLoad, targetLoad := targetLoad }

theorem pairedStoreLoadByte_empty_none
    {Tag State : Type} (resolve : AllocId → Nat)
    (id offset : Nat) (byte : Byte Tag) :
    pairedStoreLoadByte resolve
      ({ allocations := [], nextId := 0 } : Store Tag State)
      id offset byte = none := by
  rfl

theorem pairedStoreLoadByte_decompose
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : StoreLoadPair Tag State)
    (hresult : pairedStoreLoadByte resolve store id offset byte = some result) :
    ∃ (stores : (Store Tag State × Footprint) ×
        (Store Tag State × Footprint))
      (sourceLoad : Byte Tag × Footprint)
      (targetLoad : Byte Tag × Footprint),
      result.sourceStore = stores.1 ∧
      result.targetStore = stores.2 ∧
      result.sourceLoad = sourceLoad ∧
      result.targetLoad = targetLoad := by
  cases hs : pairedStoreByte resolve store id offset byte with
  | none => simp [pairedStoreLoadByte, hs] at hresult
  | some stores =>
      cases hsource : loadByte stores.1.1 id offset with
      | none => simp [pairedStoreLoadByte, hs, hsource] at hresult
      | some sourceLoad =>
          cases htarget : loadByte stores.2.1 id offset with
          | none => simp [pairedStoreLoadByte, hs, hsource, htarget] at hresult
          | some targetLoad =>
              simp [pairedStoreLoadByte, hs, hsource, htarget] at hresult
              rcases hresult with rfl
              exact ⟨stores, sourceLoad, targetLoad, rfl, rfl, rfl, rfl⟩

theorem pairedStoreLoadByte_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : StoreLoadPair Tag State)
    (hresult : pairedStoreLoadByte resolve store id offset byte = some result) :
    ∃ (stores : (Store Tag State × Footprint) ×
        (Store Tag State × Footprint))
      (sourceLoad : Byte Tag × Footprint)
      (targetLoad : Byte Tag × Footprint),
      result.sourceStore = stores.1 ∧
      result.targetStore = stores.2 ∧
      result.sourceLoad = sourceLoad ∧
      result.targetLoad = targetLoad ∧
      pairedStoreByte resolve store id offset byte = some stores ∧
      loadByte stores.1.1 id offset = some sourceLoad ∧
      loadByte stores.2.1 id offset = some targetLoad := by
  cases hs : pairedStoreByte resolve store id offset byte with
  | none => simp [pairedStoreLoadByte, hs] at hresult
  | some stores =>
      cases hsource : loadByte stores.1.1 id offset with
      | none => simp [pairedStoreLoadByte, hs, hsource] at hresult
      | some sourceLoad =>
          cases htarget : loadByte stores.2.1 id offset with
          | none => simp [pairedStoreLoadByte, hs, hsource, htarget] at hresult
          | some targetLoad =>
              simp [pairedStoreLoadByte, hs, hsource, htarget] at hresult
              rcases hresult with rfl
              exact ⟨stores, sourceLoad, targetLoad, rfl, rfl, rfl, rfl,
                by simpa using hs, by simpa using hsource, by simpa using htarget⟩

theorem pairedStoreLoadByte_refusal_store
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (hstore : pairedStoreByte resolve store id offset byte = none) :
    pairedStoreLoadByte resolve store id offset byte = none := by
  simp [pairedStoreLoadByte, hstore]

theorem pairedStoreLoadByte_refusal_source_load
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (stores : (Store Tag State × Footprint) × (Store Tag State × Footprint))
    (hstore : pairedStoreByte resolve store id offset byte = some stores)
    (hload : loadByte stores.1.1 id offset = none) :
    pairedStoreLoadByte resolve store id offset byte = none := by
  simp [pairedStoreLoadByte, hstore, hload]

theorem pairedStoreLoadByte_refusal_target_load
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (stores : (Store Tag State × Footprint) × (Store Tag State × Footprint))
    (hstore : pairedStoreByte resolve store id offset byte = some stores)
    (hload : loadByte stores.1.1 id offset = some sourceLoad)
    (htarget : loadByte stores.2.1 id offset = none) :
    pairedStoreLoadByte resolve store id offset byte = none := by
  simp [pairedStoreLoadByte, hstore, hload, htarget]

theorem pairedStoreLoadByte_refusal
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (hrefusal :
      pairedStoreByte resolve store id offset byte = none ∨
      (∃ stores,
        pairedStoreByte resolve store id offset byte = some stores ∧
        loadByte stores.1.1 id offset = none) ∨
      (∃ stores sourceLoad,
        pairedStoreByte resolve store id offset byte = some stores ∧
        loadByte stores.1.1 id offset = some sourceLoad ∧
        loadByte stores.2.1 id offset = none)) :
    pairedStoreLoadByte resolve store id offset byte = none := by
  rcases hrefusal with hstore | hsourceLoad | htargetLoad
  · simp [pairedStoreLoadByte, hstore]
  · rcases hsourceLoad with ⟨stores, hstore, hload⟩
    simp [pairedStoreLoadByte, hstore, hload]
  · rcases htargetLoad with ⟨stores, sourceLoad, hstore, hload, htarget⟩
    simp [pairedStoreLoadByte, hstore, hload, htarget]

theorem pairedStoreLoadByte_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag) :
    pairedStoreLoadByte resolve store id offset byte = none ↔
      pairedStoreByte resolve store id offset byte = none ∨
      (∃ stores,
        pairedStoreByte resolve store id offset byte = some stores ∧
        loadByte stores.1.1 id offset = none) ∨
      (∃ stores sourceLoad,
        pairedStoreByte resolve store id offset byte = some stores ∧
        loadByte stores.1.1 id offset = some sourceLoad ∧
        loadByte stores.2.1 id offset = none) := by
  cases hs : pairedStoreByte resolve store id offset byte with
  | none => simp [pairedStoreLoadByte, hs]
  | some stores =>
      cases hsource : loadByte stores.1.1 id offset with
      | none => simp [pairedStoreLoadByte, hs, hsource]
      | some sourceLoad =>
          cases htarget : loadByte stores.2.1 id offset with
          | none =>
              cases sourceLoad with
              | mk sourceByte sourceFootprint =>
                  simp [pairedStoreLoadByte, hs, hsource, htarget]
          | some targetLoad => simp [pairedStoreLoadByte, hs, hsource, htarget]

def endLifetime (store : Store Tag State) (id : AllocId) :
    Option (Store Tag State × Footprint) := do
  let allocation ← lookup store id
  if !allocation.live then none
  else
    let updated := { allocation with live := false }
    let allocations := store.allocations.map (fun entry =>
      if entry.1 == id then (id, updated) else entry)
    some ({ store with allocations := allocations },
      footprint .metadata (Region.mk id 0 allocation.bytes.length))

theorem endLifetime_success_payload
    (store : Store Tag State) (id : AllocId)
    (result : Store Tag State × Footprint)
    (hresult : endLifetime store id = some result) :
    ∃ allocation,
      lookup store id = some allocation ∧
      result.1 = { store with allocations := store.allocations.map (fun entry =>
        if entry.1 == id then
          (id, { allocation with live := false })
        else entry) } := by
  cases hlookup : lookup store id with
  | none => simp [endLifetime, hlookup] at hresult
  | some allocation =>
      cases hlive : allocation.live with
      | false => simp [endLifetime, hlookup, hlive] at hresult
      | true =>
          simp [endLifetime, hlookup, hlive] at hresult
          refine ⟨allocation, rfl, ?_⟩
          simpa [hlive] using congrArg (fun pair => pair.1) hresult.symm

theorem endLifetime_result_contract
    (store : Store Tag State) (id : AllocId)
    (result : Store Tag State × Footprint)
    (hresult : endLifetime store id = some result) :
    ∃ allocation,
      lookup store id = some allocation ∧
      allocation.live = true ∧
      result = ({ store with allocations := store.allocations.map (fun entry =>
        if entry.1 == id then
          (id, { allocation with live := false })
        else entry) },
        footprint .metadata (Region.mk id 0 allocation.bytes.length)) := by
  cases hlookup : lookup store id with
  | none => simp [endLifetime, hlookup] at hresult
  | some allocation =>
      cases hlive : allocation.live with
      | false => simp [endLifetime, hlookup, hlive] at hresult
      | true =>
          refine ⟨allocation, rfl, hlive, ?_⟩
          simpa [endLifetime, hlookup, hlive] using hresult.symm

def pairedEndLifetime (resolve : AllocId → Nat) (store : Store Tag State)
    (id : AllocId) :
    Option ((Store Tag State × Footprint) × (Store Tag State × Footprint)) := do
  let sourceResult ← endLifetime store id
  let targetResult ← endLifetime (renameStore resolve store) id
  some (sourceResult, targetResult)

theorem pairedEndLifetime_empty_none
    {Tag State : Type} (resolve : AllocId → Nat) (id : AllocId) :
    pairedEndLifetime resolve
      ({ allocations := [], nextId := 0 } : Store Tag State) id = none := by
  rfl

theorem pairedEndLifetime_decompose
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedEndLifetime resolve store id = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) := by
  cases hs : endLifetime store id with
  | none => simp [pairedEndLifetime, hs] at hresult
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedEndLifetime, hs, ht] at hresult
      | some targetResult =>
          rw [pairedEndLifetime, hs, ht] at hresult
          have hpair : (sourceResult, targetResult) = result := by
            simpa only [Option.bind_some] using Option.some.inj hresult
          exact ⟨sourceResult, targetResult, hpair.symm⟩

theorem pairedEndLifetime_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId) :
    pairedEndLifetime resolve store id = none ↔
      endLifetime store id = none ∨
      endLifetime (renameStore resolve store) id = none := by
  cases hs : endLifetime store id with
  | none => simp [pairedEndLifetime, hs]
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedEndLifetime, hs, ht]
      | some targetResult => simp [pairedEndLifetime, hs, ht]

theorem pairedEndLifetime_sound
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedEndLifetime resolve store id = some result) :
    ∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      endLifetime store id = some sourceResult ∧
      endLifetime (renameStore resolve store) id = some targetResult := by
  cases hs : endLifetime store id with
  | none => simp [pairedEndLifetime, hs] at hresult
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedEndLifetime, hs, ht] at hresult
      | some targetResult =>
          simp [pairedEndLifetime, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨sourceResult, targetResult, rfl, by simpa using hs,
            by simpa using ht⟩

theorem pairedEndLifetime_refusal
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (hrefusal : endLifetime store id = none ∨
      endLifetime (renameStore resolve store) id = none) :
    pairedEndLifetime resolve store id = none := by
  cases hrefusal with
  | inl hsource => simp [pairedEndLifetime, hsource]
  | inr htarget => simp [pairedEndLifetime, htarget]

theorem pairedEndLifetime_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (hsource : endLifetime store id = none) :
    pairedEndLifetime resolve store id = none := by
  simp [pairedEndLifetime, hsource]

theorem pairedEndLifetime_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (htarget : endLifetime (renameStore resolve store) id = none) :
    pairedEndLifetime resolve store id = none := by
  simp [pairedEndLifetime, htarget]

theorem pairedEndLifetime_both_success
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (source target : Store Tag State × Footprint)
    (hsource : endLifetime store id = some source)
    (htarget : endLifetime (renameStore resolve store) id = some target) :
    pairedEndLifetime resolve store id = some (source, target) := by
  simp [pairedEndLifetime, hsource, htarget]

def pairedLifetimeLookup (resolve : AllocId → Nat)
    (store : Store Tag State) (id : AllocId) : Bool :=
  match endLifetime store id, endLifetime (renameStore resolve store) id with
  | some (source, _), some (target, _) => true
  | _, _ => false

theorem pairedLifetimeLookup_empty_false
    {Tag State : Type} (resolve : AllocId → Nat) (id : AllocId) :
    pairedLifetimeLookup resolve
      ({ allocations := [], nextId := 0 } : Store Tag State) id = false := by
  rfl

theorem pairedLifetimeLookup_sound
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (h : pairedLifetimeLookup resolve store id = true) :
    ∃ source target,
      endLifetime store id = some source ∧
      endLifetime (renameStore resolve store) id = some target := by
  cases hs : endLifetime store id with
  | none => simp [pairedLifetimeLookup, hs] at h
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedLifetimeLookup, hs, ht] at h
      | some targetResult =>
          simp [pairedLifetimeLookup, hs, ht] at h
          exact ⟨sourceResult, targetResult, rfl, rfl⟩

theorem pairedLifetimeLookup_both_success
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (source target : Store Tag State × Footprint)
    (hsource : endLifetime store id = some source)
    (htarget : endLifetime (renameStore resolve store) id = some target) :
    pairedLifetimeLookup resolve store id = true := by
  simp [pairedLifetimeLookup, hsource, htarget]

theorem pairedLifetimeLookup_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (hsource : endLifetime store id = none) :
    pairedLifetimeLookup resolve store id = false := by
  simp [pairedLifetimeLookup, hsource]

theorem pairedLifetimeLookup_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (htarget : endLifetime (renameStore resolve store) id = none) :
    pairedLifetimeLookup resolve store id = false := by
  simp [pairedLifetimeLookup, htarget]

theorem pairedLifetimeLookup_refusal
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (hrefusal : endLifetime store id = none ∨
      endLifetime (renameStore resolve store) id = none) :
    pairedLifetimeLookup resolve store id = false := by
  rcases hrefusal with hsource | htarget
  · simp [pairedLifetimeLookup, hsource]
  · simp [pairedLifetimeLookup, htarget]

theorem pairedLifetimeLookup_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId) :
    pairedLifetimeLookup resolve store id = false ↔
      endLifetime store id = none ∨
      endLifetime (renameStore resolve store) id = none := by
  cases hs : endLifetime store id with
  | none => simp [pairedLifetimeLookup, hs]
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedLifetimeLookup, hs, ht]
      | some targetResult => simp [pairedLifetimeLookup, hs, ht]

def pairedStaleLoad (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) : Bool :=
  match endLifetime store id, endLifetime (renameStore resolve store) id with
  | some sourceResult, some targetResult =>
      (loadByte sourceResult.1 id offset).isNone &&
      (loadByte targetResult.1 id offset).isNone
  | _, _ => false

theorem pairedStaleLoad_empty_false
    {Tag State : Type} (resolve : AllocId → Nat)
    (id offset : Nat) :
    pairedStaleLoad resolve
      ({ allocations := [], nextId := 0 } : Store Tag State) id offset = false := by
  rfl

def pairedStaleStore (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag) : Bool :=
  match endLifetime store id, endLifetime (renameStore resolve store) id with
  | some sourceResult, some targetResult =>
      (storeByte sourceResult.1 id offset byte).isNone &&
      (storeByte targetResult.1 id offset (renameByte resolve byte)).isNone
  | _, _ => false

theorem pairedStaleStore_empty_false
    {Tag State : Type} (resolve : AllocId → Nat)
    (id offset : Nat) (byte : Byte Tag) :
    pairedStaleStore resolve
      ({ allocations := [], nextId := 0 } : Store Tag State) id offset byte = false := by
  rfl

theorem pairedStaleLoad_both_refused
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (hsource : endLifetime store id = some sourceResult)
    (htarget : endLifetime (renameStore resolve store) id = some targetResult)
    (hloadSource : loadByte sourceResult.1 id offset = none)
    (hloadTarget : loadByte targetResult.1 id offset = none) :
    pairedStaleLoad resolve store id offset = true := by
  simp [pairedStaleLoad, hsource, htarget, hloadSource, hloadTarget]

theorem pairedStaleLoad_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (hsource : endLifetime store id = none) :
    pairedStaleLoad resolve store id offset = false := by
  simp [pairedStaleLoad, hsource]

theorem pairedStaleLoad_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (htarget : endLifetime (renameStore resolve store) id = none) :
    pairedStaleLoad resolve store id offset = false := by
  simp [pairedStaleLoad, htarget]

theorem pairedStaleLoad_refusal_source_load
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (sourceResult targetResult : Store Tag State × Footprint)
    (hsource : endLifetime store id = some sourceResult)
    (htarget : endLifetime (renameStore resolve store) id = some targetResult)
    (hloadSource : loadByte sourceResult.1 id offset = some sourceLoad) :
    pairedStaleLoad resolve store id offset = false := by
  simp [pairedStaleLoad, hsource, htarget, hloadSource]

theorem pairedStaleLoad_refusal_target_load
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (sourceResult targetResult : Store Tag State × Footprint)
    (hsource : endLifetime store id = some sourceResult)
    (htarget : endLifetime (renameStore resolve store) id = some targetResult)
    (hloadSource : loadByte sourceResult.1 id offset = none)
    (hloadTarget : loadByte targetResult.1 id offset = some targetLoad) :
    pairedStaleLoad resolve store id offset = false := by
  simp [pairedStaleLoad, hsource, htarget, hloadSource, hloadTarget]

theorem pairedStaleStore_both_refused
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (byte : Byte Tag)
    (hsource : endLifetime store id = some sourceResult)
    (htarget : endLifetime (renameStore resolve store) id = some targetResult)
    (hstoreSource : storeByte sourceResult.1 id offset byte = none)
    (hstoreTarget : storeByte targetResult.1 id offset (renameByte resolve byte) = none) :
    pairedStaleStore resolve store id offset byte = true := by
  simp [pairedStaleStore, hsource, htarget, hstoreSource, hstoreTarget]

theorem pairedStaleStore_refusal_source
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (byte : Byte Tag)
    (hsource : endLifetime store id = none) :
    pairedStaleStore resolve store id offset byte = false := by
  simp [pairedStaleStore, hsource]

theorem pairedStaleStore_refusal_target
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (byte : Byte Tag)
    (htarget : endLifetime (renameStore resolve store) id = none) :
    pairedStaleStore resolve store id offset byte = false := by
  simp [pairedStaleStore, htarget]

theorem pairedStaleStore_refusal_source_store
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (byte : Byte Tag) (sourceResult targetResult : Store Tag State × Footprint)
    (hsource : endLifetime store id = some sourceResult)
    (htarget : endLifetime (renameStore resolve store) id = some targetResult)
    (hstoreSource : storeByte sourceResult.1 id offset byte = some sourceStore) :
    pairedStaleStore resolve store id offset byte = false := by
  simp [pairedStaleStore, hsource, htarget, hstoreSource]

theorem pairedStaleStore_refusal_target_store
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (byte : Byte Tag) (sourceResult targetResult : Store Tag State × Footprint)
    (hsource : endLifetime store id = some sourceResult)
    (htarget : endLifetime (renameStore resolve store) id = some targetResult)
    (hstoreSource : storeByte sourceResult.1 id offset byte = none)
    (hstoreTarget : storeByte targetResult.1 id offset
      (renameByte resolve byte) = some targetStore) :
    pairedStaleStore resolve store id offset byte = false := by
  simp [pairedStaleStore, hsource, htarget, hstoreSource, hstoreTarget]

theorem pairedStaleLoad_refusal
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (hrefusal :
      endLifetime store id = none ∨
      endLifetime (renameStore resolve store) id = none ∨
      (∃ sourceResult targetResult, ∃ (sourceLoad : Byte Tag × Footprint),
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        loadByte sourceResult.1 id offset = some sourceLoad) ∨
      (∃ sourceResult targetResult, ∃ (sourceLoad targetLoad : Byte Tag × Footprint),
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        loadByte sourceResult.1 id offset = none ∧
        loadByte targetResult.1 id offset = some targetLoad)) :
    pairedStaleLoad resolve store id offset = false := by
  rcases hrefusal with hsource | htarget | hsourceLoad | htargetLoad
  · simp [pairedStaleLoad, hsource]
  · simp [pairedStaleLoad, htarget]
  · rcases hsourceLoad with ⟨sourceResult, targetResult, sourceLoad, hsource,
      htarget, hloadSource⟩
    simp [pairedStaleLoad, hsource, htarget, hloadSource]
  · rcases htargetLoad with ⟨sourceResult, targetResult, sourceLoad, targetLoad,
      hsource, htarget, hloadSource, hloadTarget⟩
    simp [pairedStaleLoad, hsource, htarget, hloadSource, hloadTarget]

theorem pairedStaleStore_refusal
    (resolve : AllocId → Nat) (store : Store Tag State) (id offset : Nat)
    (byte : Byte Tag)
    (hrefusal :
      endLifetime store id = none ∨
      endLifetime (renameStore resolve store) id = none ∨
      (∃ sourceResult targetResult, ∃ (sourceStore : Store Tag State × Footprint),
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        storeByte sourceResult.1 id offset byte = some sourceStore) ∨
      (∃ sourceResult targetResult, ∃ (sourceStore targetStore : Store Tag State × Footprint),
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        storeByte sourceResult.1 id offset byte = none ∧
        storeByte targetResult.1 id offset (renameByte resolve byte) = some targetStore)) :
    pairedStaleStore resolve store id offset byte = false := by
  rcases hrefusal with hsource | htarget | hsourceStore | htargetStore
  · simp [pairedStaleStore, hsource]
  · simp [pairedStaleStore, htarget]
  · rcases hsourceStore with ⟨sourceResult, targetResult, sourceStore, hsource,
      htarget, hstoreSource⟩
    simp [pairedStaleStore, hsource, htarget, hstoreSource]
  · rcases htargetStore with ⟨sourceResult, targetResult, sourceStore, targetStore,
      hsource, htarget, hstoreSource, hstoreTarget⟩
    simp [pairedStaleStore, hsource, htarget, hstoreSource, hstoreTarget]

theorem pairedStaleLoad_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (h : pairedStaleLoad resolve store id offset = true) :
    ∃ sourceResult targetResult,
      endLifetime store id = some sourceResult ∧
      endLifetime (renameStore resolve store) id = some targetResult ∧
      loadByte sourceResult.1 id offset = none ∧
      loadByte targetResult.1 id offset = none := by
  cases hs : endLifetime store id with
  | none => simp [pairedStaleLoad, hs] at h
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedStaleLoad, hs, ht] at h
      | some targetResult =>
          simp [pairedStaleLoad, hs, ht] at h
          exact ⟨sourceResult, targetResult, rfl, rfl, h.1, h.2⟩

theorem pairedStaleStore_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (h : pairedStaleStore resolve store id offset byte = true) :
    ∃ sourceResult targetResult,
      endLifetime store id = some sourceResult ∧
      endLifetime (renameStore resolve store) id = some targetResult ∧
      storeByte sourceResult.1 id offset byte = none ∧
      storeByte targetResult.1 id offset (renameByte resolve byte) = none := by
  cases hs : endLifetime store id with
  | none => simp [pairedStaleStore, hs] at h
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedStaleStore, hs, ht] at h
      | some targetResult =>
          simp [pairedStaleStore, hs, ht] at h
          exact ⟨sourceResult, targetResult, rfl, rfl, h.1, h.2⟩

theorem pairedStaleLoad_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) :
    pairedStaleLoad resolve store id offset = false ↔
      endLifetime store id = none ∨
      endLifetime (renameStore resolve store) id = none ∨
      (∃ (sourceResult targetResult : Store Tag State × Footprint)
          (sourceLoad : Byte Tag × Footprint),
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        loadByte sourceResult.1 id offset = some sourceLoad) ∨
      (∃ (sourceResult targetResult : Store Tag State × Footprint)
          (targetLoad : Byte Tag × Footprint),
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        loadByte sourceResult.1 id offset = none ∧
        loadByte targetResult.1 id offset = some targetLoad) := by
  cases hs : endLifetime store id with
  | none => simp [pairedStaleLoad, hs]
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedStaleLoad, hs, ht]
      | some targetResult =>
          cases hsource : loadByte sourceResult.1 id offset with
          | some sourceLoad =>
              simp [pairedStaleLoad, hs, ht, hsource]
              exact ⟨sourceLoad.1, sourceLoad.2, rfl⟩
          | none =>
              cases htarget : loadByte targetResult.1 id offset with
              | some targetLoad =>
                  simp [pairedStaleLoad, hs, ht, hsource, htarget]
                  exact ⟨targetLoad.1, targetLoad.2, rfl⟩
              | none =>
                  simp [pairedStaleLoad, hs, ht, hsource, htarget]

theorem pairedStaleStore_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag) :
    pairedStaleStore resolve store id offset byte = false ↔
      endLifetime store id = none ∨
      endLifetime (renameStore resolve store) id = none ∨
      (∃ (sourceResult targetResult : Store Tag State × Footprint)
          (sourceStore : Store Tag State × Footprint),
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        storeByte sourceResult.1 id offset byte = some sourceStore) ∨
      (∃ (sourceResult targetResult : Store Tag State × Footprint)
          (targetStore : Store Tag State × Footprint),
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        storeByte sourceResult.1 id offset byte = none ∧
        storeByte targetResult.1 id offset (renameByte resolve byte) =
          some targetStore) := by
  cases hs : endLifetime store id with
  | none => simp [pairedStaleStore, hs]
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedStaleStore, hs, ht]
      | some targetResult =>
          cases hsource : storeByte sourceResult.1 id offset byte with
          | some sourceStore =>
              simp [pairedStaleStore, hs, ht, hsource]
              exact ⟨sourceStore.1, sourceStore.2, rfl⟩
          | none =>
              cases htarget : storeByte targetResult.1 id offset
                  (renameByte resolve byte) with
              | some targetStore =>
                  simp [pairedStaleStore, hs, ht, hsource, htarget]
                  exact ⟨targetStore.1, targetStore.2, rfl⟩
              | none =>
                  simp [pairedStaleStore, hs, ht, hsource, htarget]

theorem storeByte_preserves_nextId
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (result : Store Tag State × Footprint)
    (hresult : storeByte store id offset byte = some result) :
    result.1.nextId = store.nextId := by
  cases hlookup : lookup store id with
  | none => simp [storeByte, hlookup] at hresult
  | some allocation =>
      simp [storeByte, hlookup] at hresult
      rcases hresult with ⟨_, _, hEq⟩
      exact congrArg (fun pair => pair.1.nextId) hEq.symm

theorem storeByte_preserves_allocation_count
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (result : Store Tag State × Footprint)
    (hresult : storeByte store id offset byte = some result) :
    result.1.allocations.length = store.allocations.length := by
  cases hlookup : lookup store id with
  | none => simp [storeByte, hlookup] at hresult
  | some allocation =>
      simp [storeByte, hlookup] at hresult
      rcases hresult with ⟨_, _, hEq⟩
      simpa using congrArg (fun pair => pair.1.allocations.length) hEq.symm


theorem storeByte_footprint
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (result : Store Tag State × Footprint)
    (hresult : storeByte store id offset byte = some result) :
    result.2 = footprint .write { allocation := id, offset := offset, width := 1 } := by
  cases hlookup : lookup store id with
  | none => simp [storeByte, hlookup] at hresult
  | some allocation =>
      simp [storeByte, hlookup] at hresult
      rcases hresult with ⟨_, _, hEq⟩
      exact congrArg (fun pair => pair.2) hEq.symm

theorem pairedStoreByte_preserves_store_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedStoreByte resolve store id offset byte = some result) :
    result.1.1.nextId = store.nextId ∧
      result.2.1.nextId = (renameStore resolve store).nextId ∧
      result.1.1.allocations.length = store.allocations.length ∧
      result.2.1.allocations.length = (renameStore resolve store).allocations.length := by
  cases hs : storeByte store id offset byte with
  | none => simp [pairedStoreByte, hs] at hresult
  | some sourceResult =>
      cases ht : storeByte (renameStore resolve store) id offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedStoreByte, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨storeByte_preserves_nextId store id offset byte sourceResult hs,
            storeByte_preserves_nextId (renameStore resolve store) id offset
              (renameByte resolve byte) targetResult ht,
            storeByte_preserves_allocation_count store id offset byte sourceResult hs,
            storeByte_preserves_allocation_count (renameStore resolve store) id offset
              (renameByte resolve byte) targetResult ht⟩

theorem loadByte_footprint
    (store : Store Tag State) (id offset : Nat)
    (result : Byte Tag × Footprint)
    (hresult : loadByte store id offset = some result) :
    result.2 = footprint .read { allocation := id, offset := offset, width := 1 } := by
  cases hlookup : lookup store id with
  | none => simp [loadByte, hlookup] at hresult
  | some allocation =>
      simp [loadByte, hlookup] at hresult
      rcases hindex : allocation.bytes[offset]? with value | none
      · simp [hindex] at hresult
      · simp [hindex] at hresult
        rcases hresult with ⟨hlive, hpair⟩
        rcases hpair with rfl
        rfl

theorem loadByte_success
    (store : Store Tag State) (id offset : Nat)
    (allocation : Allocation Tag State) (byte : Byte Tag)
    (hlive : allocation.live = true)
    (hlookup : lookup store id = some allocation)
    (hindex : allocation.bytes[offset]? = some byte) :
    loadByte store id offset =
      some (byte, footprint .read { allocation := id, offset := offset, width := 1 }) := by
  simp [loadByte, hlookup, hindex, hlive]

theorem storeByte_success
    (store : Store Tag State) (id offset : Nat)
    (allocation : Allocation Tag State) (oldByte newByte : Byte Tag)
    (hlive : allocation.live = true)
    (hlookup : lookup store id = some allocation)
    (hindex : allocation.bytes[offset]? = some oldByte) :
    ∃ newStore, storeByte store id offset newByte = some
      (newStore, footprint .write { allocation := id, offset := offset, width := 1 }) := by
  have hoffset : offset < allocation.bytes.length := by
    apply Nat.lt_of_not_ge
    intro h
    simp [List.getElem?_eq_none h] at hindex
  have hnot : ¬ allocation.bytes.length ≤ offset := by omega
  simp [storeByte, hlookup, hlive, hnot]

theorem storeByte_missing
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (hlookup : lookup store id = none) :
    storeByte store id offset byte = none := by
  simp [storeByte, hlookup]

theorem storeByte_dead
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (allocation : Allocation Tag State)
    (hlookup : lookup store id = some allocation)
    (hdead : allocation.live = false) :
    storeByte store id offset byte = none := by
  simp [storeByte, hlookup, hdead]

theorem storeByte_outOfBounds
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (allocation : Allocation Tag State)
    (hlookup : lookup store id = some allocation)
    (hlive : allocation.live = true)
    (hindex : allocation.bytes[offset]? = none) :
    storeByte store id offset byte = none := by
  have hoffset : allocation.bytes.length ≤ offset :=
    (List.getElem?_eq_none_iff).mp hindex
  simp [storeByte, hlookup, hlive, hoffset]

theorem loadByte_missing
    (store : Store Tag State) (id offset : Nat)
    (hlookup : lookup store id = none) :
    loadByte store id offset = none := by
  simp [loadByte, hlookup]

theorem loadByte_dead
    (store : Store Tag State) (id offset : Nat)
    (allocation : Allocation Tag State)
    (hlookup : lookup store id = some allocation)
    (hdead : allocation.live = false) :
    loadByte store id offset = none := by
  simp [loadByte, hlookup, hdead]

theorem loadByte_outOfBounds
    (store : Store Tag State) (id offset : Nat)
    (allocation : Allocation Tag State)
    (hlookup : lookup store id = some allocation)
    (hlive : allocation.live = true)
    (hindex : allocation.bytes[offset]? = none) :
    loadByte store id offset = none := by
  simp [loadByte, hlookup, hlive, hindex]

theorem endLifetime_success
    (store : Store Tag State) (id : AllocId)
    (allocation : Allocation Tag State)
    (hlive : allocation.live = true)
    (hlookup : lookup store id = some allocation) :
    ∃ newStore, endLifetime store id = some
      (newStore, footprint .metadata (Region.mk id 0 allocation.bytes.length)) := by
  simp [endLifetime, hlookup, hlive]

theorem endLifetime_missing
    (store : Store Tag State) (id : AllocId)
    (hlookup : lookup store id = none) :
    endLifetime store id = none := by
  simp [endLifetime, hlookup]

theorem endLifetime_dead
    (store : Store Tag State) (id : AllocId)
    (allocation : Allocation Tag State)
    (hlookup : lookup store id = some allocation)
    (hdead : allocation.live = false) :
    endLifetime store id = none := by
  simp [endLifetime, hlookup, hdead]

theorem endLifetime_preserves_nextId
    (store : Store Tag State) (id : AllocId)
    (result : Store Tag State × Footprint)
    (hresult : endLifetime store id = some result) :
    result.1.nextId = store.nextId := by
  cases hlookup : lookup store id with
  | none => simp [endLifetime, hlookup] at hresult
  | some allocation =>
      simp [endLifetime, hlookup] at hresult
      rcases hresult with ⟨_, hEq⟩
      exact congrArg (fun pair => pair.1.nextId) hEq.symm

theorem endLifetime_preserves_allocation_count
    (store : Store Tag State) (id : AllocId)
    (result : Store Tag State × Footprint)
    (hresult : endLifetime store id = some result) :
    result.1.allocations.length = store.allocations.length := by
  cases hlookup : lookup store id with
  | none => simp [endLifetime, hlookup] at hresult
  | some allocation =>
      simp [endLifetime, hlookup] at hresult
      rcases hresult with ⟨_, hEq⟩
      simpa using congrArg (fun pair => pair.1.allocations.length) hEq.symm

theorem endLifetime_preserves_wellFormed
    (store : Store Tag State) (id : AllocId)
    (result : Store Tag State × Footprint)
    (hstore : WellFormed store)
    (hbytes : bytesWf id ((lookup store id).map
      (fun allocation => allocation.bytes) |>.getD []))
    (hresult : endLifetime store id = some result) :
    WellFormed result.1 := by
  obtain ⟨allocation, hlookup, hpayload⟩ :=
    endLifetime_success_payload store id result hresult
  rw [hpayload]
  unfold WellFormed at hstore ⊢
  simp [hlookup] at hbytes
  have map_wf : ∀ entries : List (AllocId × Allocation Tag State),
      allocationsWf entries →
      allocationsWf (entries.map (fun entry =>
        if entry.1 == id then
          (id, { allocation with live := false })
        else entry)) := by
    intro entries
    induction entries with
    | nil => intro _; simp [allocationsWf]
    | cons entry rest ih =>
        intro hentries
        rcases entry with ⟨entryId, entryAllocation⟩
        simp only [List.map_cons, allocationsWf] at hentries ⊢
        by_cases heq : entryId == id
        · simp only [heq, ite_true]
          exact ⟨hbytes, ih hentries.2⟩
        · simp only [heq, ite_false]
          exact ⟨hentries.1, ih hentries.2⟩
  exact map_wf store.allocations hstore


theorem endLifetime_footprint
    (store : Store Tag State) (id : AllocId)
    (result : Store Tag State × Footprint)
    (hresult : endLifetime store id = some result) :
    result.2 = footprint .metadata (Region.mk id 0
      ((lookup store id).map (fun allocation => allocation.bytes.length) |>.getD 0)) := by
  cases hlookup : lookup store id with
  | none => simp [endLifetime, hlookup] at hresult
  | some allocation =>
      simp [endLifetime, hlookup] at hresult
      rcases hresult with ⟨_, hEq⟩
      exact congrArg (fun pair => pair.2) hEq.symm

theorem pairedStoreByte_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedStoreByte resolve store id offset byte = some result) :
    result.1.2 = footprint .write { allocation := id, offset := offset, width := 1 } ∧
      result.2.2 = footprint .write { allocation := id, offset := offset, width := 1 } := by
  cases hs : storeByte store id offset byte with
  | none => simp [pairedStoreByte, hs] at hresult
  | some sourceResult =>
      cases ht : storeByte (renameStore resolve store) id offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedStoreByte, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨storeByte_footprint _ _ _ _ _ hs,
            storeByte_footprint _ _ _ _ _ ht⟩

theorem pairedLoadByte_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedLoadByte resolve store id offset = some result) :
    result.1.2 = footprint .read { allocation := id, offset := offset, width := 1 } ∧
      result.2.2 = footprint .read { allocation := id, offset := offset, width := 1 } := by
  cases hs : loadByte store id offset with
  | none => simp [pairedLoadByte, hs] at hresult
  | some sourceResult =>
      cases ht : loadByte (renameStore resolve store) id offset with
      | none => simp [pairedLoadByte, hs, ht] at hresult
      | some targetResult =>
          simp [pairedLoadByte, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨loadByte_footprint _ _ _ _ hs,
            loadByte_footprint _ _ _ _ ht⟩

theorem pairedStoreLoadByte_footprints
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : StoreLoadPair Tag State)
    (hresult : pairedStoreLoadByte resolve store id offset byte = some result) :
    result.sourceStore.2 = footprint .write
        { allocation := id, offset := offset, width := 1 } ∧
      result.targetStore.2 = footprint .write
        { allocation := id, offset := offset, width := 1 } ∧
      result.sourceLoad.2 = footprint .read
        { allocation := id, offset := offset, width := 1 } ∧
      result.targetLoad.2 = footprint .read
        { allocation := id, offset := offset, width := 1 } := by
  cases hs : pairedStoreByte resolve store id offset byte with
  | none => simp [pairedStoreLoadByte, hs] at hresult
  | some stores =>
      cases hsource : loadByte stores.1.1 id offset with
      | none => simp [pairedStoreLoadByte, hs, hsource] at hresult
      | some sourceLoad =>
          cases htarget : loadByte stores.2.1 id offset with
          | none => simp [pairedStoreLoadByte, hs, hsource, htarget] at hresult
          | some targetLoad =>
              simp [pairedStoreLoadByte, hs, hsource, htarget] at hresult
              rcases hresult with rfl
              have hsourceStore : stores.1.2 = footprint .write
                  { allocation := id, offset := offset, width := 1 } :=
                pairedStoreByte_footprints resolve store id offset byte stores hs |>.1
              have htargetStore : stores.2.2 = footprint .write
                  { allocation := id, offset := offset, width := 1 } :=
                pairedStoreByte_footprints resolve store id offset byte stores hs |>.2
              exact ⟨hsourceStore, htargetStore,
                loadByte_footprint _ _ _ _ hsource,
                loadByte_footprint _ _ _ _ htarget⟩

theorem pairedStoreLoadByte_preserves_store_counts
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : StoreLoadPair Tag State)
    (hresult : pairedStoreLoadByte resolve store id offset byte = some result) :
    result.sourceStore.1.nextId = store.nextId ∧
      result.targetStore.1.nextId = (renameStore resolve store).nextId ∧
      result.sourceStore.1.allocations.length = store.allocations.length ∧
      result.targetStore.1.allocations.length =
        (renameStore resolve store).allocations.length := by
  cases hs : storeByte store id offset byte with
  | none => simp [pairedStoreLoadByte, pairedStoreByte, hs] at hresult
  | some sourceStore =>
      cases ht : storeByte (renameStore resolve store) id offset
          (renameByte resolve byte) with
      | none => simp [pairedStoreLoadByte, pairedStoreByte, hs, ht] at hresult
      | some targetStore =>
          cases hsource : loadByte sourceStore.1 id offset with
          | none => simp [pairedStoreLoadByte, pairedStoreByte, hs, ht, hsource] at hresult
          | some sourceLoad =>
              cases htarget : loadByte targetStore.1 id offset with
              | none => simp [pairedStoreLoadByte, pairedStoreByte, hs, ht, hsource, htarget] at hresult
              | some targetLoad =>
                  simp [pairedStoreLoadByte, pairedStoreByte, hs, ht, hsource, htarget] at hresult
                  rcases hresult with rfl
                  exact ⟨storeByte_preserves_nextId store id offset byte sourceStore hs,
                    storeByte_preserves_nextId (renameStore resolve store) id offset
                      (renameByte resolve byte) targetStore ht,
                    storeByte_preserves_allocation_count store id offset byte sourceStore hs,
                    storeByte_preserves_allocation_count (renameStore resolve store) id offset
                      (renameByte resolve byte) targetStore ht⟩

theorem pairedStoreLoadByte_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : StoreLoadPair Tag State)
    (hsourceStore : WellFormed store)
    (hsourceBytes : bytesWf id (listSet
      ((lookup store id).map (fun allocation => allocation.bytes) |>.getD [])
      offset byte))
    (htargetBytes : bytesWf id (listSet
      ((lookup (renameStore resolve store) id).map
        (fun allocation => allocation.bytes) |>.getD [])
      offset (renameByte resolve byte)))
    (hresult : pairedStoreLoadByte resolve store id offset byte = some result) :
    WellFormed result.sourceStore.1 ∧ WellFormed result.targetStore.1 := by
  cases hs : pairedStoreByte resolve store id offset byte with
  | none => simp [pairedStoreLoadByte, hs] at hresult
  | some stores =>
      cases hsource : loadByte stores.1.1 id offset with
      | none => simp [pairedStoreLoadByte, hs, hsource] at hresult
      | some sourceLoad =>
          cases htarget : loadByte stores.2.1 id offset with
          | none => simp [pairedStoreLoadByte, hs, hsource, htarget] at hresult
          | some targetLoad =>
              simp [pairedStoreLoadByte, hs, hsource, htarget] at hresult
              rcases hresult with rfl
              exact pairedStoreByte_preserves_wellFormed resolve store id offset byte
                stores hsourceStore hsourceBytes htargetBytes hs

theorem pairedEndLifetime_footprints
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedEndLifetime resolve store id = some result) :
    result.1.2 = footprint .metadata
      (Region.mk id 0 ((lookup store id).map
        (fun allocation => allocation.bytes.length) |>.getD 0)) ∧
      result.2.2 = footprint .metadata
        (Region.mk id 0 ((lookup (renameStore resolve store) id).map
          (fun allocation => allocation.bytes.length) |>.getD 0)) := by
  cases hs : endLifetime store id with
  | none => simp [pairedEndLifetime, hs] at hresult
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedEndLifetime, hs, ht] at hresult
      | some targetResult =>
          simp [pairedEndLifetime, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨endLifetime_footprint _ _ _ hs,
            endLifetime_footprint _ _ _ ht⟩

theorem pairedEndLifetime_preserves_store_counts
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hresult : pairedEndLifetime resolve store id = some result) :
    result.1.1.nextId = store.nextId ∧
      result.2.1.nextId = (renameStore resolve store).nextId ∧
      result.1.1.allocations.length = store.allocations.length ∧
      result.2.1.allocations.length = (renameStore resolve store).allocations.length := by
  cases hs : endLifetime store id with
  | none => simp [pairedEndLifetime, hs] at hresult
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedEndLifetime, hs, ht] at hresult
      | some targetResult =>
          simp [pairedEndLifetime, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨endLifetime_preserves_nextId _ _ _ hs,
            endLifetime_preserves_nextId _ _ _ ht,
            endLifetime_preserves_allocation_count _ _ _ hs,
            endLifetime_preserves_allocation_count _ _ _ ht⟩

theorem pairedEndLifetime_preserves_wellFormed
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hstore : WellFormed store)
    (hsourceBytes : bytesWf id ((lookup store id).map
      (fun allocation => allocation.bytes) |>.getD []))
    (htargetBytes : bytesWf id ((lookup (renameStore resolve store) id).map
      (fun allocation => allocation.bytes) |>.getD []))
    (hresult : pairedEndLifetime resolve store id = some result) :
    WellFormed result.1.1 ∧ WellFormed result.2.1 := by
  cases hs : endLifetime store id with
  | none => simp [pairedEndLifetime, hs] at hresult
  | some sourceResult =>
      cases ht : endLifetime (renameStore resolve store) id with
      | none => simp [pairedEndLifetime, hs, ht] at hresult
      | some targetResult =>
          simp [pairedEndLifetime, hs, ht] at hresult
          rcases hresult with rfl
          exact ⟨endLifetime_preserves_wellFormed store id sourceResult
              hstore hsourceBytes hs,
            endLifetime_preserves_wellFormed (renameStore resolve store) id
              targetResult (renameStore_preserves_wellFormed resolve store hstore)
              htargetBytes ht⟩

theorem pairedUnaddressableAllocation_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State)
    (hstore : WellFormed store)
    (hsourceBytes : bytesWf store.nextId request.bytes)
    (htargetBytes : bytesWf (renameStore resolve store).nextId
      (renameAllocationRequest resolve request).bytes)
    (h : pairedUnaddressableAllocation resolve store request = true) :
    (∃ source target,
      allocate store request .unaddressable = some source ∧
      allocate (renameStore resolve store)
        (renameAllocationRequest resolve request) .unaddressable = some target ∧
      WellFormed source.1 ∧ WellFormed target.1) ∨
    (allocate store request .unaddressable = none ∧
      allocate (renameStore resolve store)
        (renameAllocationRequest resolve request) .unaddressable = none) := by
  rcases pairedUnaddressableAllocation_sound resolve store request h with
    hsuccess | hfailure
  · rcases hsuccess with ⟨source, target, hsource, htarget⟩
    have hwfSource := allocate_preserves_wellFormed store request .unaddressable source
      hstore hsourceBytes hsource
    have hwfTarget := allocate_preserves_wellFormed (renameStore resolve store)
      (renameAllocationRequest resolve request) .unaddressable target
      (renameStore_preserves_wellFormed resolve store hstore) htargetBytes htarget
    exact Or.inl ⟨source, target, hsource, htarget, hwfSource, hwfTarget⟩
  · exact Or.inr hfailure

theorem pairedCopySnapshot_contract [BEq Tag]
    (resolve : AllocId → Nat)
    (source destination : List (Byte Tag))
    (result : List (Byte Tag) × List (Byte Tag))
    (hresult : pairedCopySnapshot resolve source destination = some result) :
    (∃ sourceResult targetResult, result = (sourceResult, targetResult)) ∧
      result.2 = result.1.map (renameByte resolve) := by
  constructor
  · exact pairedCopySnapshot_decompose resolve source destination result hresult
  · exact pairedCopySnapshot_byte_correspondence resolve source destination result hresult

theorem pairedCopySnapshot_failure_contract [BEq Tag]
    (resolve : AllocId → Nat)
    (source destination : List (Byte Tag)) :
    pairedCopySnapshot resolve source destination = none ↔
      source.length ≠ destination.length := by
  by_cases hsame : source.length = destination.length
  · simp [pairedCopySnapshot, copySnapshot, hsame, List.length_map]
  · simp [pairedCopySnapshot, copySnapshot, hsame, List.length_map]

theorem pairedMergeByte_contract [BEq Tag]
    (resolve : AllocId → Nat) (old : Byte Tag)
    (mask value choice : UInt8) :
    ((mergeByte (renameByte resolve old) mask value choice ==
        renameByte resolve (mergeByte old mask value choice)) = true ∧
      pairedMergeByte resolve old mask value choice =
        some (mergeByte old mask value choice,
          mergeByte (renameByte resolve old) mask value choice)) ∨
    ((mergeByte (renameByte resolve old) mask value choice ==
        renameByte resolve (mergeByte old mask value choice)) = false ∧
      pairedMergeByte resolve old mask value choice = none) := by
  by_cases hguard : (mergeByte (renameByte resolve old) mask value choice ==
      renameByte resolve (mergeByte old mask value choice)) = true
  · exact Or.inl ⟨hguard,
      pairedMergeByte_success resolve old mask value choice hguard⟩
  · have hguard' : (mergeByte (renameByte resolve old) mask value choice ==
      renameByte resolve (mergeByte old mask value choice)) = false := by
      apply Bool.eq_false_iff.mpr
      exact hguard
    exact Or.inr ⟨hguard',
      pairedMergeByte_refusal resolve old mask value choice hguard'⟩

theorem pairedMemmoveSnapshot_contract [BEq Tag]
    (resolve : AllocId → Nat) (source destination : Region)
    (bytes : List (Byte Tag))
    (result : List (Byte Tag) × List (Byte Tag))
    (hresult : pairedMemmoveSnapshot resolve source destination bytes = some result) :
    (∃ sourceResult targetResult, result = (sourceResult, targetResult)) ∧
      result.2 = result.1.map (renameByte resolve) ∧
      (result.1.length = bytes.length ∧ result.2.length = bytes.length) := by
  constructor
  · exact pairedMemmoveSnapshot_decompose resolve source destination bytes result hresult
  constructor
  · exact pairedMemmoveSnapshot_byte_correspondence resolve source destination bytes result
      hresult
  · exact pairedMemmoveSnapshot_preserves_lengths resolve source destination bytes result hresult

theorem pairedFreePointer_contract
    (resolve : AllocId → Nat)
    (metadata : Option (AllocationMetadata Tag State TypeId)) :
    pairedFreePointer resolve metadata = true ∧
      freePointer metadata =
        freePointer (metadata.map (renameZeroTokenMetadata resolve)) := by
  exact ⟨pairedFreePointer_true resolve metadata,
    pairedFreePointer_agrees resolve metadata⟩

theorem pairedAllocateFailure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (h : pairedAllocateFailure resolve store request placement = true) :
    allocate store request placement = none ∧
      allocate (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) = none := by
  exact pairedAllocateFailure_sound resolve store request placement h

theorem pairedAllocateFailure_failure_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement) :
    pairedAllocateFailure resolve store request placement = true ↔
      allocate store request placement = none ∧
        allocate (renameStore resolve store) (renameAllocationRequest resolve request)
          (renamedPlacement resolve store.nextId placement) = none := by
  simp [pairedAllocateFailure, Bool.and_eq_true]

theorem pairedAllocateZeroSize_contract
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) :
    pairedAllocateZeroSize (Tag := Tag) (State := State) (TypeId := TypeId)
        resolve state placement = true ∧
      (((allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 = .null ∧
        (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
          (match placement with
          | .address _ => .address (resolve 0)
          | .unaddressable => .unaddressable
          | .fail => .fail)).1 = .null) ∨
       (∃ source target,
        (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state placement).1 = .token source ∧
        (allocateZeroSize (Tag := Tag) (TypeId := TypeId) state
          (match placement with
          | .address _ => .address (resolve 0)
          | .unaddressable => .unaddressable
          | .fail => .fail)).1 = .token target ∧
        source.wellFormed 0 ∧ target.wellFormed 0)) := by
  constructor
  · exact pairedAllocateZeroSize_true resolve state placement
  · exact pairedAllocateZeroSize_sound_wellFormed resolve state placement

theorem pairedAllocateZeroSize_failure_contract
    {Tag State TypeId : Type} (resolve : AllocId → Nat) (state : State)
    (placement : Placement) :
    pairedAllocateZeroSize (Tag := Tag) (State := State) (TypeId := TypeId)
      resolve state placement = false ↔ False := by
  cases placement <;> simp [pairedAllocateZeroSize, allocateZeroSize]

theorem pairedAllocateAligned_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat) (hstore : WellFormed store)
    (hsourceBytes : bytesWf store.nextId request.bytes)
    (htargetBytes : bytesWf (renameStore resolve store).nextId
      (renameAllocationRequest resolve request).bytes)
    (h : pairedAllocateAligned resolve store request placement alignment = true) :
    (∃ source target,
      allocateAligned store request placement alignment = some source ∧
      allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment = some target ∧
      WellFormed source.1 ∧ WellFormed target.1) ∨
    (allocateAligned store request placement alignment = none ∧
      allocateAligned (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment = none) := by
  rcases pairedAllocateAligned_sound resolve store request placement alignment h with
    hsuccess | hfailure
  · rcases hsuccess with ⟨source, target, hsource, htarget⟩
    have hwf := pairedAllocateAligned_preserves_wellFormed resolve store request placement
      alignment source target hstore hsourceBytes htargetBytes hsource htarget
    exact Or.inl ⟨source, target, hsource, htarget, hwf.1, hwf.2⟩
  · exact Or.inr hfailure

theorem pairedAllocate_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hstore : WellFormed store)
    (hsourceBytes : bytesWf store.nextId request.bytes)
    (htargetBytes : bytesWf (renameStore resolve store).nextId
      (renameAllocationRequest resolve request).bytes)
    (hresult : pairedAllocate resolve store request placement = some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      allocate store request placement = some sourceResult ∧
      allocate (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) = some targetResult) ∧
      (WellFormed result.1.1 ∧ WellFormed result.2.1) ∧
      (result.1.1.nextId = store.nextId + 1 ∧
        result.2.1.nextId = (renameStore resolve store).nextId + 1 ∧
        result.1.1.allocations.length = store.allocations.length + 1 ∧
        result.2.1.allocations.length =
          (renameStore resolve store).allocations.length + 1) ∧
      (result.1.2 = footprint .metadata
          (Region.mk store.nextId 0 request.bytes.length) ∧
        result.2.2 = footprint .metadata
          (Region.mk (renameStore resolve store).nextId 0 request.bytes.length)) := by
  constructor
  · exact pairedAllocate_sound resolve store request placement result hresult
  constructor
  · exact pairedAllocate_preserves_wellFormed resolve store request placement result
      hstore hsourceBytes htargetBytes hresult
  constructor
  · exact pairedAllocate_preserves_counts resolve store request placement result hresult
  · exact pairedAllocate_preserves_footprints resolve store request placement result hresult

theorem pairedAllocateBounded_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat)
    (hstore : WellFormed store)
    (hsourceBytes : bytesWf store.nextId request.bytes)
    (htargetBytes : bytesWf (renameStore resolve store).nextId
      (renameAllocationRequest resolve request).bytes)
    (h : pairedAllocateBounded resolve store request placement alignment limit = true) :
    (∃ source target,
      allocateBounded store request placement alignment limit = .ok source ∧
      allocateBounded (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment limit = .ok target ∧
      (WellFormed source.1 ∧ WellFormed target.1) ∧
      (source.1.nextId = store.nextId + 1 ∧
        source.1.allocations.length = store.allocations.length + 1 ∧
        target.1.nextId = (renameStore resolve store).nextId + 1 ∧
        target.1.allocations.length =
          (renameStore resolve store).allocations.length + 1) ∧
      (source.2 = footprint .metadata
          (Region.mk store.nextId 0 request.bytes.length) ∧
        target.2 = footprint .metadata
          (Region.mk (renameStore resolve store).nextId 0
            (renameAllocationRequest resolve request).bytes.length))) ∨
    (∃ fault,
      allocateBounded store request placement alignment limit = .error fault ∧
      allocateBounded (renameStore resolve store) (renameAllocationRequest resolve request)
        (renamedPlacement resolve store.nextId placement) alignment limit = .error fault) := by
  rcases pairedAllocateBounded_sound resolve store request placement alignment limit h with
    hsuccess | hfailure
  · rcases hsuccess with ⟨source, target, hsource, htarget⟩
    left
    refine ⟨source, target, hsource, htarget, ?_, ?_, ?_⟩
    · exact pairedAllocateBounded_preserves_wellFormed resolve store request placement
        alignment limit source target hstore hsourceBytes htargetBytes hsource htarget
    · exact pairedAllocateBounded_preserves_counts resolve store request placement
        alignment limit source target hsource htarget
    · exact pairedAllocateBounded_preserves_footprints resolve store request placement
        alignment limit source target hsource htarget
  · exact Or.inr hfailure

theorem pairedFreeMetadata_contract
    (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hmetadata : metadata.wellFormed 0)
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      freeMetadata metadata = some sourceResult ∧
      freeMetadata (renameZeroTokenMetadata resolve metadata) = some targetResult) ∧
      (result.1.2 = footprint .metadata
          (Region.mk 0 0 metadata.allocation.bytes.length) ∧
        result.2.2 = footprint .metadata
          (Region.mk 0 0 metadata.allocation.bytes.length)) ∧
      (result.1.1.allocation.live = false ∧ result.2.1.allocation.live = false) ∧
      (result.1.1.locations = metadata.locations ∧
        result.2.1.locations = (renameZeroTokenMetadata resolve metadata).locations) ∧
      (result.1.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
        result.1.1.locations.length = metadata.locations.length ∧
        result.2.1.allocation.bytes.length =
          (renameZeroTokenMetadata resolve metadata).allocation.bytes.length ∧
        result.2.1.locations.length =
          (renameZeroTokenMetadata resolve metadata).locations.length) ∧
      (result.1.1.allocation.address = metadata.allocation.address ∧
        result.1.1.allocation.bytes = metadata.allocation.bytes ∧
        result.1.1.allocation.state = metadata.allocation.state ∧
        result.2.1.allocation.address =
          (renameZeroTokenMetadata resolve metadata).allocation.address ∧
        result.2.1.allocation.bytes =
          (renameZeroTokenMetadata resolve metadata).allocation.bytes ∧
        result.2.1.allocation.state =
          (renameZeroTokenMetadata resolve metadata).allocation.state) ∧
      (result.1.1.wellFormed 0 ∧ result.2.1.wellFormed 0) := by
  constructor
  · exact pairedFreeMetadata_sound resolve metadata result hresult
  constructor
  · simpa only using pairedFreeMetadata_footprints resolve metadata result hresult
  constructor
  · exact pairedFreeMetadata_marks_dead resolve metadata result hresult
  constructor
  · exact pairedFreeMetadata_preserves_locations resolve metadata result hresult
  constructor
  · exact pairedFreeMetadata_preserves_lengths resolve metadata result hresult
  constructor
  · exact pairedFreeMetadata_preserves_payload resolve metadata result hresult
  · exact pairedFreeMetadata_preserves_wellFormed_from_source resolve metadata result
      hmetadata hresult

theorem pairedReallocMetadata_contract
    (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hold : old.wellFormed 0)
    (hbytes : bytesWf 0 request.bytes)
    (hlocations : locations.length = request.bytes.length)
    (hresult : pairedReallocMetadata resolve old request locations placement = some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult)) ∧
      ((match result.1.1 with
        | .failed previous => previous.allocation.bytes.length = old.allocation.bytes.length
        | .replaced fresh =>
            fresh.allocation.bytes.length = request.bytes.length ∧
              fresh.locations.length = locations.length) ∧
       (match result.2.1 with
        | .failed previous => previous.allocation.bytes.length =
            (renameMetadata resolve 0 old).allocation.bytes.length
        | .replaced fresh =>
            fresh.allocation.bytes.length =
                (renameAllocationRequest resolve request).bytes.length ∧
              fresh.locations.length = locations.length)) ∧
      ((match result.1.1 with
        | .failed previous => previous = old
        | .replaced fresh =>
            fresh.allocation.bytes = request.bytes ∧
              fresh.allocation.state = request.state ∧ fresh.locations = locations) ∧
       (match result.2.1 with
        | .failed previous => previous = renameMetadata resolve 0 old
        | .replaced fresh =>
            fresh.allocation.bytes = (renameAllocationRequest resolve request).bytes ∧
              fresh.allocation.state = request.state ∧ fresh.locations = locations)) ∧
      ((match result.1.1 with
        | .failed previous => previous.allocation.live = old.allocation.live
        | .replaced fresh => fresh.allocation.live = true) ∧
       (match result.2.1 with
        | .failed previous => previous.allocation.live =
            (renameMetadata resolve 0 old).allocation.live
        | .replaced fresh => fresh.allocation.live = true)) ∧
      ((match result.1.1 with
        | .failed previous => previous.locations = old.locations
        | .replaced fresh => fresh.locations = locations) ∧
       (match result.2.1 with
        | .failed previous => previous.locations = (renameMetadata resolve 0 old).locations
        | .replaced fresh => fresh.locations = locations)) ∧
      (result.1.2 = footprint .metadata
          (Region.mk 0 0 (match result.1.1 with
            | .failed previous => previous.allocation.bytes.length
            | .replaced fresh => fresh.allocation.bytes.length)) ∧
        result.2.2 = footprint .metadata
          (Region.mk 0 0 (match result.2.1 with
            | .failed previous => previous.allocation.bytes.length
            | .replaced fresh => fresh.allocation.bytes.length))) ∧
      ((match result.1.1 with
        | .failed previous => previous.wellFormed 0
        | .replaced fresh => fresh.wellFormed 0) ∧
       (match result.2.1 with
        | .failed previous => previous.wellFormed 0
        | .replaced fresh => fresh.wellFormed 0)) := by
  constructor
  · exact pairedReallocMetadata_decompose resolve old request locations placement result hresult
  constructor
  · simpa only using
      (pairedReallocMetadata_preserves_lengths resolve old request locations placement
        result hresult)
  constructor
  · simpa only using
      (pairedReallocMetadata_preserves_payload resolve old request locations placement
        result hresult)
  constructor
  · simpa only using
      (pairedReallocMetadata_preserves_liveness resolve old request locations placement
        result hresult)
  constructor
  · simpa only using
      (pairedReallocMetadata_preserves_locations resolve old request locations placement
        result hresult)
  constructor
  · simpa only using
      (pairedReallocMetadata_footprints resolve old request locations placement result hresult)
  · simpa only using
      (pairedReallocMetadata_preserves_wellFormed resolve old request locations placement
        result hold hbytes hlocations hresult)

theorem pairedUnionLoadMetadataByte_contract
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedUnionLoadMetadataByte resolve id metadata offset = some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      unionLoadMetadataByte metadata offset = some sourceResult ∧
      unionLoadMetadataByte (renameMetadata resolve id metadata) offset =
        some targetResult ∧
      (targetResult.1 == renameByte resolve sourceResult.1) = true ∧
      (targetResult.2 == sourceResult.2) = true) ∧
      ((result.2.1 == renameByte resolve result.1.1) = true ∧
        (result.2.2 == result.1.2) = true) ∧
      (result.1.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 }) := by
  constructor
  · exact pairedUnionLoadMetadataByte_sound resolve id metadata offset result hresult
  constructor
  · obtain ⟨sourceResult, targetResult, hpair, hsource, htarget, hbyte, hfootprint⟩ :=
      pairedUnionLoadMetadataByte_sound resolve id metadata offset result hresult
    rcases hpair with rfl
    exact ⟨hbyte, hfootprint⟩
  · exact pairedUnionLoadMetadataByte_footprints resolve id metadata offset result hresult

theorem pairedStoreUnionLoadMetadataByte_contract
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)))
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hbytesTarget : bytesWf 0 (listSet
      (renameMetadata resolve id metadata).allocation.bytes offset
      (renameByte resolve byte)))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length)
    (hlocationsTarget :
      (renameMetadata resolve id metadata).locations.length =
        (renameMetadata resolve id metadata).allocation.bytes.length)
    (hresult : pairedStoreUnionLoadMetadataByte resolve id metadata offset byte =
      some result) :
    (∃ sourceStore sourceLoad targetStore targetLoad,
      result = ((sourceStore, sourceLoad), (targetStore, targetLoad)) ∧
      storeMetadataByte metadata offset byte = some sourceStore ∧
      storeMetadataByte (renameMetadata resolve id metadata) offset
        (renameByte resolve byte) = some targetStore ∧
      unionLoadMetadataByte sourceStore.1 offset = some sourceLoad ∧
      unionLoadMetadataByte targetStore.1 offset = some targetLoad ∧
      (targetStore.1 == renameMetadata resolve id sourceStore.1) = true ∧
      (targetStore.2 == sourceStore.2) = true ∧
      (targetLoad.1 == renameByte resolve sourceLoad.1) = true ∧
      (targetLoad.2 == sourceLoad.2) = true) ∧
      (result.1.1.2 = footprint .write
          { allocation := 0, offset := offset, width := 1 } ∧
        result.1.2.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.1.2 = footprint .write
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.2.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 }) ∧
      (result.1.1.1.allocation.live = metadata.allocation.live ∧
        result.1.1.1.allocation.address = metadata.allocation.address ∧
        result.1.1.1.allocation.state = metadata.allocation.state ∧
        result.2.1.1.allocation.live =
          (renameMetadata resolve id metadata).allocation.live ∧
        result.2.1.1.allocation.address =
          (renameMetadata resolve id metadata).allocation.address ∧
        result.2.1.1.allocation.state =
          (renameMetadata resolve id metadata).allocation.state) ∧
      (result.1.1.1.locations = metadata.locations ∧
        result.2.1.1.locations = (renameMetadata resolve id metadata).locations) ∧
      (result.1.1.1.wellFormed 0 ∧ result.2.1.1.wellFormed 0) := by
  constructor
  · exact pairedStoreUnionLoadMetadataByte_sound resolve id metadata offset byte result hresult
  constructor
  · exact pairedStoreUnionLoadMetadataByte_footprints resolve id metadata offset byte result
      hresult
  constructor
  · exact pairedStoreUnionLoadMetadataByte_preserves_payload resolve id metadata offset byte
      result hresult
  constructor
  · exact pairedStoreUnionLoadMetadataByte_preserves_locations resolve id metadata offset byte
      result hresult
  · exact pairedStoreUnionLoadMetadataByte_preserves_wellFormed resolve id metadata offset byte
      result hresult hbytes hbytesTarget hlocations hlocationsTarget

theorem pairedRepresentationLoadMetadataByte_contract
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedRepresentationLoadMetadataByte resolve id metadata offset choice =
      some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      representationLoadMetadataByte metadata offset choice = some sourceResult ∧
      representationLoadMetadataByte (renameMetadata resolve id metadata) offset choice =
        some targetResult) ∧
      (result.1.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 }) := by
  constructor
  · exact pairedRepresentationLoadMetadataByte_sound resolve id metadata offset choice result
      hresult
  · exact pairedRepresentationLoadMetadataByte_footprints resolve id metadata offset choice result
      hresult

theorem pairedTypedLoadMetadataByte_contract
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedTypedLoadMetadataByte resolve id metadata offset typeId =
      some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      typedLoadMetadataByte metadata offset typeId = some sourceResult ∧
      typedLoadMetadataByte (renameMetadata resolve id metadata) offset typeId =
        some targetResult ∧
      (targetResult.1 == renameByte resolve sourceResult.1) = true ∧
      (targetResult.2 == sourceResult.2) = true) ∧
      ((result.2.1 == renameByte resolve result.1.1) = true ∧
        (result.2.2 == result.1.2) = true) ∧
      (result.1.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 }) := by
  constructor
  · exact pairedTypedLoadMetadataByte_sound resolve id metadata offset typeId result hresult
  constructor
  · exact pairedTypedLoadMetadataByte_correspondence resolve id metadata offset typeId result
      hresult
  · exact pairedTypedLoadMetadataByte_footprints resolve id metadata offset typeId result hresult

theorem pairedTypedStoreLoadMetadataByte_contract
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)))
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hbytesTarget : bytesWf 0 (listSet
      (renameMetadata resolve id metadata).allocation.bytes offset
      (renameByte resolve byte)))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length)
    (hlocationsTarget :
      (renameMetadata resolve id metadata).locations.length =
        (renameMetadata resolve id metadata).allocation.bytes.length)
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result) :
    (∃ sourceStore sourceLoad targetStore targetLoad,
      result = ((sourceStore, sourceLoad), (targetStore, targetLoad)) ∧
      typedStoreMetadataByte metadata offset typeId byte = some sourceStore ∧
      typedStoreMetadataByte (renameMetadata resolve id metadata) offset typeId
        (renameByte resolve byte) = some targetStore ∧
      typedLoadMetadataByte sourceStore.1 offset typeId = some sourceLoad ∧
      typedLoadMetadataByte targetStore.1 offset typeId = some targetLoad ∧
      (targetStore.1 == renameMetadata resolve id sourceStore.1) = true ∧
      (targetStore.2 == sourceStore.2) = true ∧
      (targetLoad.1 == renameByte resolve sourceLoad.1) = true ∧
      (targetLoad.2 == sourceLoad.2) = true) ∧
      (result.1.1.2 = footprint .write
          { allocation := 0, offset := offset, width := 1 } ∧
        result.1.2.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.1.2 = footprint .write
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.2.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 }) ∧
      ((result.2.1.1 == renameMetadata resolve id result.1.1.1) = true ∧
        (result.2.1.2 == result.1.1.2) = true ∧
        (result.2.2.1 == renameByte resolve result.1.2.1) = true ∧
        (result.2.2.2 == result.1.2.2) = true) ∧
      (result.1.1.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
        result.1.1.1.locations.length = metadata.locations.length ∧
        result.2.1.1.allocation.bytes.length =
          (renameMetadata resolve id metadata).allocation.bytes.length ∧
        result.2.1.1.locations.length =
          (renameMetadata resolve id metadata).locations.length) ∧
      (result.1.1.1.allocation.live = metadata.allocation.live ∧
        result.1.1.1.allocation.address = metadata.allocation.address ∧
        result.1.1.1.allocation.state = metadata.allocation.state ∧
        result.2.1.1.allocation.live =
          (renameMetadata resolve id metadata).allocation.live ∧
        result.2.1.1.allocation.address =
          (renameMetadata resolve id metadata).allocation.address ∧
        result.2.1.1.allocation.state =
          (renameMetadata resolve id metadata).allocation.state) ∧
      (result.1.1.1.locations = listSet metadata.locations offset
          { effectiveType := .typed typeId, initialized := true } ∧
        result.2.1.1.locations = listSet
          (renameMetadata resolve id metadata).locations offset
          { effectiveType := .typed typeId, initialized := true }) ∧
      (result.1.1.1.wellFormed 0 ∧ result.2.1.1.wellFormed 0) := by
  constructor
  · exact pairedTypedStoreLoadMetadataByte_sound resolve id metadata offset typeId byte
      result hresult
  constructor
  · exact pairedTypedStoreLoadMetadataByte_footprints resolve id metadata offset typeId byte
      result hresult
  constructor
  · exact pairedTypedStoreLoadMetadataByte_correspondence resolve id metadata offset typeId byte
      result hresult
  constructor
  · exact pairedTypedStoreLoadMetadataByte_preserves_lengths resolve id metadata offset typeId byte
      result hresult
  constructor
  · exact pairedTypedStoreLoadMetadataByte_preserves_payload resolve id metadata offset typeId byte
      result hresult
  constructor
  · exact pairedTypedStoreLoadMetadataByte_preserves_locations resolve id metadata offset typeId byte
      result hresult
  · exact pairedTypedStoreLoadMetadataByte_preserves_wellFormed resolve id metadata offset typeId
      byte result hresult hbytes hbytesTarget hlocations hlocationsTarget

theorem pairedTypedStoreMetadataByte_contract
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hbytesTarget : bytesWf 0 (listSet
      (renameMetadata resolve id metadata).allocation.bytes offset
      (renameByte resolve byte)))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length)
    (hlocationsTarget :
      (renameMetadata resolve id metadata).locations.length =
        (renameMetadata resolve id metadata).allocation.bytes.length)
    (hresult : pairedTypedStoreMetadataByte resolve id metadata offset typeId byte =
      some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      typedStoreMetadataByte metadata offset typeId byte = some sourceResult ∧
      typedStoreMetadataByte (renameMetadata resolve id metadata) offset typeId
        (renameByte resolve byte) = some targetResult ∧
      (targetResult.1 == renameMetadata resolve id sourceResult.1) = true ∧
      (targetResult.2 == sourceResult.2) = true) ∧
      (result.1.2 = footprint .write
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.2 = footprint .write
          { allocation := 0, offset := offset, width := 1 }) ∧
      ((result.2.1 == renameMetadata resolve id result.1.1) = true ∧
        (result.2.2 == result.1.2) = true) ∧
      (result.1.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
        result.1.1.locations.length = metadata.locations.length ∧
        result.2.1.allocation.bytes.length =
          (renameMetadata resolve id metadata).allocation.bytes.length ∧
        result.2.1.locations.length =
          (renameMetadata resolve id metadata).locations.length) ∧
      (result.1.1.allocation.live = metadata.allocation.live ∧
        result.1.1.allocation.address = metadata.allocation.address ∧
        result.1.1.allocation.state = metadata.allocation.state ∧
        result.2.1.allocation.live =
          (renameMetadata resolve id metadata).allocation.live ∧
        result.2.1.allocation.address =
          (renameMetadata resolve id metadata).allocation.address ∧
        result.2.1.allocation.state =
          (renameMetadata resolve id metadata).allocation.state) ∧
      (result.1.1.wellFormed 0 ∧ result.2.1.wellFormed 0) := by
  constructor
  · exact pairedTypedStoreMetadataByte_sound resolve id metadata offset typeId byte
      result hresult
  constructor
  · exact pairedTypedStoreMetadataByte_footprints resolve id metadata offset typeId byte
      result hresult
  constructor
  · exact pairedTypedStoreMetadataByte_correspondence resolve id metadata offset typeId byte
      result hresult
  constructor
  · exact pairedTypedStoreMetadataByte_preserves_lengths resolve id metadata offset typeId byte
      result hresult
  constructor
  · exact pairedTypedStoreMetadataByte_preserves_payload resolve id metadata offset typeId byte
      result hresult
  · exact pairedTypedStoreMetadataByte_preserves_wellFormed resolve id metadata offset typeId
      byte result hresult hbytes hbytesTarget hlocations hlocationsTarget

theorem pairedStoreRepresentationLoadMetadataByte_contract
    [BEq Tag] [BEq State] [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (result : (((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))))
    (hbytes : bytesWf 0 (listSet metadata.allocation.bytes offset byte))
    (hbytesTarget : bytesWf 0 (listSet
      (renameMetadata resolve id metadata).allocation.bytes offset
      (renameByte resolve byte)))
    (hlocations : metadata.locations.length = metadata.allocation.bytes.length)
    (hlocationsTarget :
      (renameMetadata resolve id metadata).locations.length =
        (renameMetadata resolve id metadata).allocation.bytes.length)
    (hresult : pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte choice =
      some result) :
    (∃ sourceStore sourceLoad targetStore targetLoad,
      result = ((sourceStore, sourceLoad), (targetStore, targetLoad)) ∧
      storeMetadataByte metadata offset byte = some sourceStore ∧
      storeMetadataByte (renameMetadata resolve id metadata) offset
        (renameByte resolve byte) = some targetStore ∧
      representationLoadMetadataByte sourceStore.1 offset choice = some sourceLoad ∧
      representationLoadMetadataByte targetStore.1 offset choice = some targetLoad) ∧
      (result.1.1.2 = footprint .write
          { allocation := 0, offset := offset, width := 1 } ∧
        result.1.2.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.1.2 = footprint .write
          { allocation := 0, offset := offset, width := 1 } ∧
        result.2.2.2 = footprint .read
          { allocation := 0, offset := offset, width := 1 }) ∧
      (result.1.1.1.locations = metadata.locations ∧
        result.2.1.1.locations = (renameMetadata resolve id metadata).locations) ∧
      (result.1.1.1.allocation.bytes.length = metadata.allocation.bytes.length ∧
        result.1.1.1.locations.length = metadata.locations.length ∧
        result.2.1.1.allocation.bytes.length =
          (renameMetadata resolve id metadata).allocation.bytes.length ∧
        result.2.1.1.locations.length =
          (renameMetadata resolve id metadata).locations.length) ∧
      (result.1.1.1.allocation.live = metadata.allocation.live ∧
        result.1.1.1.allocation.address = metadata.allocation.address ∧
        result.1.1.1.allocation.state = metadata.allocation.state ∧
        result.2.1.1.allocation.live =
          (renameMetadata resolve id metadata).allocation.live ∧
        result.2.1.1.allocation.address =
          (renameMetadata resolve id metadata).allocation.address ∧
        result.2.1.1.allocation.state =
          (renameMetadata resolve id metadata).allocation.state) ∧
      (result.1.1.1.wellFormed 0 ∧ result.2.1.1.wellFormed 0) := by
  constructor
  · exact pairedStoreRepresentationLoadMetadataByte_sound resolve id metadata
      offset byte choice result hresult
  constructor
  · exact pairedStoreRepresentationLoadMetadataByte_footprints resolve id metadata
      offset byte choice result hresult
  constructor
  · exact pairedStoreRepresentationLoadMetadataByte_preserves_locations resolve id metadata
      offset byte choice result hresult
  constructor
  · exact pairedStoreRepresentationLoadMetadataByte_preserves_lengths resolve id metadata
      offset byte choice result hresult
  constructor
  · exact pairedStoreRepresentationLoadMetadataByte_preserves_payload resolve id metadata
      offset byte choice result hresult
  · exact pairedStoreRepresentationLoadMetadataByte_preserves_wellFormed resolve id metadata
      offset byte choice result hresult hbytes hbytesTarget hlocations hlocationsTarget

theorem pairedStoreLoadByte_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : StoreLoadPair Tag State)
    (hsourceStore : WellFormed store)
    (hsourceBytes : bytesWf id (listSet
      ((lookup store id).map (fun allocation => allocation.bytes) |>.getD [])
      offset byte))
    (htargetBytes : bytesWf id (listSet
      ((lookup (renameStore resolve store) id).map
        (fun allocation => allocation.bytes) |>.getD [])
      offset (renameByte resolve byte)))
    (hresult : pairedStoreLoadByte resolve store id offset byte = some result) :
    (∃ stores sourceLoad targetLoad,
      result.sourceStore = stores.1 ∧
      result.targetStore = stores.2 ∧
      result.sourceLoad = sourceLoad ∧
      result.targetLoad = targetLoad ∧
      pairedStoreByte resolve store id offset byte = some stores ∧
      loadByte stores.1.1 id offset = some sourceLoad ∧
      loadByte stores.2.1 id offset = some targetLoad) ∧
      (result.sourceStore.2 = footprint .write
          { allocation := id, offset := offset, width := 1 } ∧
        result.targetStore.2 = footprint .write
          { allocation := id, offset := offset, width := 1 } ∧
        result.sourceLoad.2 = footprint .read
          { allocation := id, offset := offset, width := 1 } ∧
        result.targetLoad.2 = footprint .read
          { allocation := id, offset := offset, width := 1 }) ∧
      (result.sourceStore.1.nextId = store.nextId ∧
        result.targetStore.1.nextId = (renameStore resolve store).nextId ∧
        result.sourceStore.1.allocations.length = store.allocations.length ∧
        result.targetStore.1.allocations.length =
          (renameStore resolve store).allocations.length) ∧
      (WellFormed result.sourceStore.1 ∧ WellFormed result.targetStore.1) := by
  constructor
  · exact pairedStoreLoadByte_sound resolve store id offset byte result hresult
  constructor
  · exact pairedStoreLoadByte_footprints resolve store id offset byte result hresult
  constructor
  · exact pairedStoreLoadByte_preserves_store_counts resolve store id offset byte result hresult
  · exact pairedStoreLoadByte_preserves_wellFormed resolve store id offset byte result
      hsourceStore hsourceBytes htargetBytes hresult

theorem pairedLoadByte_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedLoadByte resolve store id offset = some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      loadByte store id offset = some sourceResult ∧
      loadByte (renameStore resolve store) id offset = some targetResult) ∧
      result.2.1 = renameByte resolve result.1.1 ∧
      (result.1.2 = footprint .read
          { allocation := id, offset := offset, width := 1 } ∧
        result.2.2 = footprint .read
          { allocation := id, offset := offset, width := 1 }) := by
  constructor
  · exact pairedLoadByte_sound resolve store id offset result hresult
  constructor
  · exact pairedLoadByte_value_correspondence resolve store id offset result hresult
  · exact pairedLoadByte_footprints resolve store id offset result hresult

theorem pairedStoreByte_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hsourceStore : WellFormed store)
    (hsourceBytes : bytesWf id (listSet
      ((lookup store id).map (fun allocation => allocation.bytes) |>.getD [])
      offset byte))
    (htargetBytes : bytesWf id (listSet
      ((lookup (renameStore resolve store) id).map
        (fun allocation => allocation.bytes) |>.getD [])
      offset (renameByte resolve byte)))
    (hresult : pairedStoreByte resolve store id offset byte = some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      storeByte store id offset byte = some sourceResult ∧
      storeByte (renameStore resolve store) id offset (renameByte resolve byte) =
        some targetResult) ∧
      (result.1.2 = footprint .write
          { allocation := id, offset := offset, width := 1 } ∧
        result.2.2 = footprint .write
          { allocation := id, offset := offset, width := 1 }) ∧
      (result.1.1.nextId = store.nextId ∧
        result.2.1.nextId = (renameStore resolve store).nextId ∧
        result.1.1.allocations.length = store.allocations.length ∧
        result.2.1.allocations.length =
          (renameStore resolve store).allocations.length) ∧
      (WellFormed result.1.1 ∧ WellFormed result.2.1) := by
  constructor
  · exact pairedStoreByte_sound resolve store id offset byte result hresult
  constructor
  · exact pairedStoreByte_footprints resolve store id offset byte result hresult
  constructor
  · exact pairedStoreByte_preserves_store_counts resolve store id offset byte result hresult
  · exact pairedStoreByte_preserves_wellFormed resolve store id offset byte result
      hsourceStore hsourceBytes htargetBytes hresult

theorem pairedEndLifetime_contract
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (result : (Store Tag State × Footprint) ×
      (Store Tag State × Footprint))
    (hstore : WellFormed store)
    (hsourceBytes : bytesWf id ((lookup store id).map
      (fun allocation => allocation.bytes) |>.getD []))
    (htargetBytes : bytesWf id ((lookup (renameStore resolve store) id).map
      (fun allocation => allocation.bytes) |>.getD []))
    (hresult : pairedEndLifetime resolve store id = some result) :
    (∃ sourceResult targetResult,
      result = (sourceResult, targetResult) ∧
      endLifetime store id = some sourceResult ∧
      endLifetime (renameStore resolve store) id = some targetResult) ∧
      (result.1.2 = footprint .metadata (Region.mk id 0
        ((lookup store id).map
          (fun allocation => allocation.bytes.length) |>.getD 0)) ∧
        result.2.2 = footprint .metadata (Region.mk id 0
          ((lookup (renameStore resolve store) id).map
            (fun allocation => allocation.bytes.length) |>.getD 0))) ∧
      (result.1.1.nextId = store.nextId ∧
        result.2.1.nextId = (renameStore resolve store).nextId ∧
        result.1.1.allocations.length = store.allocations.length ∧
        result.2.1.allocations.length =
          (renameStore resolve store).allocations.length) ∧
      (WellFormed result.1.1 ∧ WellFormed result.2.1) := by
  constructor
  · exact pairedEndLifetime_sound resolve store id result hresult
  constructor
  · exact pairedEndLifetime_footprints resolve store id result hresult
  constructor
  · exact pairedEndLifetime_preserves_store_counts resolve store id result hresult
  · exact pairedEndLifetime_preserves_wellFormed resolve store id result
      hstore hsourceBytes htargetBytes hresult

theorem pairedAllocateMetadata_contract
    (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    (pairedAllocateMetadata resolve id request locations placement = true ∧
      ((∃ source target,
          allocateMetadata request locations placement = some source ∧
          allocateMetadata (renameAllocationRequest resolve request) locations
            (renamedPlacement resolve id placement) = some target) ∨
        (allocateMetadata request locations placement = none ∧
          allocateMetadata (renameAllocationRequest resolve request) locations
            (renamedPlacement resolve id placement) = none))) ∨
    (pairedAllocateMetadata resolve id request locations placement = false ∧
      ((∃ target,
          allocateMetadata request locations placement = none ∧
          allocateMetadata (renameAllocationRequest resolve request) locations
            (renamedPlacement resolve id placement) = some target) ∨
        (∃ source,
          allocateMetadata request locations placement = some source ∧
          allocateMetadata (renameAllocationRequest resolve request) locations
            (renamedPlacement resolve id placement) = none))) := by
  by_cases h : pairedAllocateMetadata resolve id request locations placement = true
  · exact Or.inl ⟨h, pairedAllocateMetadata_sound resolve id request locations
      placement h⟩
  · have hfalse : pairedAllocateMetadata resolve id request locations placement = false := by
      apply Bool.eq_false_iff.mpr
      exact h
    refine Or.inr ⟨hfalse, ?_⟩
    cases hs : allocateMetadata request locations placement with
    | none =>
        cases ht : allocateMetadata (renameAllocationRequest resolve request)
            locations (renamedPlacement resolve id placement) with
        | none => simp [pairedAllocateMetadata, hs, ht] at h
        | some target => exact Or.inl ⟨target, rfl, rfl⟩
    | some source =>
        cases ht : allocateMetadata (renameAllocationRequest resolve request)
            locations (renamedPlacement resolve id placement) with
        | none => exact Or.inr ⟨source, rfl, rfl⟩
        | some target => simp [pairedAllocateMetadata, hs, ht] at h

theorem pairedPointerEqual_contract
    (resolve : AllocId → Nat) (left right : Pointer Tag)
    (choice : EqualityChoice) :
    pairedPointerEqual resolve left right choice = true ↔
      choice = .unequal ∨
        (choice = .equal ∧
          decide (((renamePointer resolve left).address ==
            (renamePointer resolve right).address) =
            (left.address == right.address)) = true) := by
  cases choice with
  | unequal => simp [pairedPointerEqual, pointerEqual]
  | equal =>
      simp [pairedPointerEqual, pointerEqual]
      exact decide_eq_true_iff

theorem pairedOffsetPointer_contract [BEq Tag]
    (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat) :
    (pairedOffsetPointer resolve pointer elementSize delta bound = true ∧
      ((∃ source target,
          offsetPointer pointer elementSize delta bound = .ok source ∧
          offsetPointer (renamePointer resolve pointer) elementSize delta bound =
            .ok target ∧
          target.address = (renamePointer resolve source).address) ∨
        (∃ fault,
          offsetPointer pointer elementSize delta bound = .error fault ∧
          offsetPointer (renamePointer resolve pointer) elementSize delta bound =
            .error fault))) ∨
    (pairedOffsetPointer resolve pointer elementSize delta bound = false ∧
      ((∃ fault target,
          offsetPointer pointer elementSize delta bound = .error fault ∧
          offsetPointer (renamePointer resolve pointer) elementSize delta bound =
            .ok target) ∨
        (∃ source fault,
          offsetPointer pointer elementSize delta bound = .ok source ∧
          offsetPointer (renamePointer resolve pointer) elementSize delta bound =
            .error fault) ∨
        (∃ sourceFault targetFault,
          offsetPointer pointer elementSize delta bound = .error sourceFault ∧
          offsetPointer (renamePointer resolve pointer) elementSize delta bound =
            .error targetFault ∧ sourceFault ≠ targetFault) ∨
        (∃ source target,
          offsetPointer pointer elementSize delta bound = .ok source ∧
          offsetPointer (renamePointer resolve pointer) elementSize delta bound =
            .ok target ∧
          (renamePointer resolve source).address ≠ target.address))) := by
  by_cases h : pairedOffsetPointer resolve pointer elementSize delta bound = true
  · exact Or.inl ⟨h, pairedOffsetPointer_sound resolve pointer elementSize delta bound h⟩
  · have hfalse : pairedOffsetPointer resolve pointer elementSize delta bound = false := by
      apply Bool.eq_false_iff.mpr
      exact h
    refine Or.inr ⟨hfalse, ?_⟩
    cases hs : offsetPointer pointer elementSize delta bound with
    | ok source =>
        cases ht : offsetPointer (renamePointer resolve pointer) elementSize delta bound with
        | ok target =>
            have haddr : ((renamePointer resolve source).address == target.address) = false := by
              simpa [pairedOffsetPointer, hs, ht] using h
            exact Or.inr (Or.inr (Or.inr ⟨source, target, rfl, rfl,
              beq_eq_false_iff_ne.mp haddr⟩))
        | error fault =>
            exact Or.inr (Or.inl ⟨source, fault, rfl, rfl⟩)
    | error sourceFault =>
        cases ht : offsetPointer (renamePointer resolve pointer) elementSize delta bound with
        | ok target =>
            exact Or.inl ⟨sourceFault, target, rfl, rfl⟩
        | error targetFault =>
            cases sourceFault <;> cases targetFault <;>
              simp [pairedOffsetPointer, hs, ht] at h ⊢

theorem pairedRecoverAddress_contract
    (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag)) :
    pairedRecoverAddress resolve address live = true ↔
      ((∃ source target,
          recoverAddress address live = .recovered source ∧
          recoverAddress address (live.map (renameLiveRegion resolve)) =
            .recovered target) ∨
        (∃ source target,
          recoverAddress address live = .empty source ∧
          recoverAddress address (live.map (renameLiveRegion resolve)) =
            .empty target)) := by
  cases hs : recoverAddress address live <;>
    cases ht : recoverAddress address (live.map (renameLiveRegion resolve)) <;>
      simp [pairedRecoverAddress, hs, ht]

theorem pairedPlacementAllowed_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (base size : Nat) :
    pairedPlacementAllowed resolve store base size = true ↔
      placementAllowed store base size =
        placementAllowed (renameStore resolve store) (resolve store.nextId) size := by
  simp [pairedPlacementAllowed, beq_iff_eq]

theorem pairedAlignmentAllowed_contract
    (resolve : AllocId → Nat) (id alignment : Nat) :
    pairedAlignmentAllowed resolve id alignment = true ↔
      alignmentAllowed id alignment = alignmentAllowed (resolve id) alignment := by
  simp [pairedAlignmentAllowed, beq_iff_eq]

theorem pairedLifetimeLookup_contract
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId) :
    (pairedLifetimeLookup resolve store id = true ∧
      ∃ source target,
        endLifetime store id = some source ∧
        endLifetime (renameStore resolve store) id = some target) ∨
    (pairedLifetimeLookup resolve store id = false ∧
      (endLifetime store id = none ∨
        endLifetime (renameStore resolve store) id = none)) := by
  by_cases h : pairedLifetimeLookup resolve store id = true
  · exact Or.inl ⟨h, pairedLifetimeLookup_sound resolve store id h⟩
  · have hfalse : pairedLifetimeLookup resolve store id = false := by
      apply Bool.eq_false_iff.mpr
      exact h
    refine Or.inr ⟨hfalse, ?_⟩
    cases hs : endLifetime store id with
    | none => simp
    | some sourceResult =>
        cases ht : endLifetime (renameStore resolve store) id with
        | none => simp
        | some targetResult =>
            simp [pairedLifetimeLookup, hs, ht] at h

theorem pairedStaleLoad_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) :
    (pairedStaleLoad resolve store id offset = true ∧
      ∃ sourceResult targetResult,
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        loadByte sourceResult.1 id offset = none ∧
        loadByte targetResult.1 id offset = none) ∨
    (pairedStaleLoad resolve store id offset = false ∧
      (endLifetime store id = none ∨
        endLifetime (renameStore resolve store) id = none ∨
        (∃ (sourceResult targetResult : Store Tag State × Footprint)
            (sourceLoad : Byte Tag × Footprint),
          endLifetime store id = some sourceResult ∧
          endLifetime (renameStore resolve store) id = some targetResult ∧
          loadByte sourceResult.1 id offset = some sourceLoad) ∨
        (∃ (sourceResult targetResult : Store Tag State × Footprint)
            (targetLoad : Byte Tag × Footprint),
          endLifetime store id = some sourceResult ∧
          endLifetime (renameStore resolve store) id = some targetResult ∧
          loadByte sourceResult.1 id offset = none ∧
          loadByte targetResult.1 id offset = some targetLoad))) := by
  by_cases h : pairedStaleLoad resolve store id offset = true
  · exact Or.inl ⟨h, pairedStaleLoad_sound resolve store id offset h⟩
  · have hfalse : pairedStaleLoad resolve store id offset = false := by
      apply Bool.eq_false_iff.mpr
      exact h
    refine Or.inr ⟨hfalse, ?_⟩
    cases hs : endLifetime store id with
    | none => simp
    | some sourceResult =>
        cases ht : endLifetime (renameStore resolve store) id with
        | none => simp
        | some targetResult =>
            cases hloadSource : loadByte sourceResult.1 id offset with
            | some sourceLoad =>
                exact Or.inr (Or.inr (Or.inl ⟨sourceResult, targetResult,
                  sourceLoad, rfl, rfl, hloadSource⟩))
            | none =>
                cases hloadTarget : loadByte targetResult.1 id offset with
                | some targetLoad =>
                    exact Or.inr (Or.inr (Or.inr ⟨sourceResult, targetResult,
                      targetLoad, rfl, rfl, hloadSource, hloadTarget⟩))
                | none =>
                    simp [pairedStaleLoad, hs, ht, hloadSource, hloadTarget] at h

theorem pairedStaleStore_contract
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag) :
    (pairedStaleStore resolve store id offset byte = true ∧
      ∃ sourceResult targetResult,
        endLifetime store id = some sourceResult ∧
        endLifetime (renameStore resolve store) id = some targetResult ∧
        storeByte sourceResult.1 id offset byte = none ∧
        storeByte targetResult.1 id offset (renameByte resolve byte) = none) ∨
    (pairedStaleStore resolve store id offset byte = false ∧
      (endLifetime store id = none ∨
        endLifetime (renameStore resolve store) id = none ∨
        (∃ (sourceResult targetResult : Store Tag State × Footprint)
            (sourceStore : Store Tag State × Footprint),
          endLifetime store id = some sourceResult ∧
          endLifetime (renameStore resolve store) id = some targetResult ∧
          storeByte sourceResult.1 id offset byte = some sourceStore) ∨
        (∃ (sourceResult targetResult : Store Tag State × Footprint)
            (targetStore : Store Tag State × Footprint),
          endLifetime store id = some sourceResult ∧
          endLifetime (renameStore resolve store) id = some targetResult ∧
          storeByte sourceResult.1 id offset byte = none ∧
          storeByte targetResult.1 id offset (renameByte resolve byte) =
            some targetStore))) := by
  by_cases h : pairedStaleStore resolve store id offset byte = true
  · exact Or.inl ⟨h, pairedStaleStore_sound resolve store id offset byte h⟩
  · have hfalse : pairedStaleStore resolve store id offset byte = false := by
      apply Bool.eq_false_iff.mpr
      exact h
    refine Or.inr ⟨hfalse, ?_⟩
    cases hs : endLifetime store id with
    | none => simp
    | some sourceResult =>
        cases ht : endLifetime (renameStore resolve store) id with
        | none => simp
        | some targetResult =>
            cases hstoreSource : storeByte sourceResult.1 id offset byte with
            | some sourceStore =>
                exact Or.inr (Or.inr (Or.inl ⟨sourceResult, targetResult,
                  sourceStore, rfl, rfl, hstoreSource⟩))
            | none =>
                cases hstoreTarget : storeByte targetResult.1 id offset
                    (renameByte resolve byte) with
                | some targetStore =>
                    exact Or.inr (Or.inr (Or.inr ⟨sourceResult, targetResult,
                      targetStore, rfl, rfl, hstoreSource, hstoreTarget⟩))
                | none =>
                    simp [pairedStaleStore, hs, ht, hstoreSource,
                      hstoreTarget] at h

#guard true
#guard (footprint .read { allocation := 1, offset := 0, width := 1 }).accesses.length == 1

end LeanModels.C.F2
