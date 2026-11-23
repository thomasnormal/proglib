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
deriving Repr, BEq

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

theorem renamePointer_idempotent (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    renamePointer resolve (renamePointer resolve pointer) = renamePointer resolve pointer := by
  cases pointer.provenance <;> simp [renamePointer]

theorem renameByte_preserves_fragment (resolve : AllocId → Nat) (byte : Byte Tag) :
    byteFragment (renameByte resolve byte) = byteFragment byte := by
  cases byte <;> simp [renameByte, byteFragment]

theorem renameByte_preserves_provenance (resolve : AllocId → Nat) (byte : Byte Tag) :
    byteProvenance (renameByte resolve byte) = byteProvenance byte := by
  cases byte <;> simp [renameByte, byteProvenance]

inductive Value (Tag : Type) where
  | scalar (bytes : List UInt8)
  | pointer (pointer : Pointer Tag)
  | aggregate (members : List (Value Tag))
deriving Repr

def encodePointer (pointer : Pointer Tag) : List (Byte Tag) :=
  (List.range 8).map (fun fragment =>
    .value (pointerByte pointer.address fragment)
      pointer.provenance (some fragment))

def encodeValue : Value Tag → List (Byte Tag)
  | .scalar bytes => bytes.map (fun byte => .value byte none none)
  | .pointer pointer => encodePointer pointer
  | .aggregate members => members.flatMap encodeValue

def copyEncoded (bytes : List (Byte Tag)) : List (Byte Tag) := bytes.map id

def decodePointer (bytes : List (Byte Tag)) : Option (Pointer Tag) := do
  if bytes.length != 8 then none
  let first ← bytes.head?
  let provenance ← match first with
    | .value _ provenance (some 0) => some provenance
    | _ => none
  let fragments := bytes.zipIdx.all fun entry =>
    match entry.1, entry.2 with
    | .value _ p (some fragment), index => p == provenance && fragment == index
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

theorem decodePointer_encodePointer (pointer : Pointer Tag) :
    decodePointer (encodePointer pointer) = some pointer := by
  simp [decodePointer, encodePointer]

structure Allocation (Tag State : Type) where
  live : Bool
  address : Option Nat
  bytes : List (Byte Tag)
  state : State
deriving Repr

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
deriving Repr

structure LocationState (TypeId : Type) where
  effectiveType : EffectiveTypeState TypeId
  initialized : Bool
deriving Repr

abbrev LocationStore (TypeId : Type) :=
  List (AllocId × Nat × LocationState TypeId)

structure AllocationMetadata (Tag State TypeId : Type) where
  allocation : Allocation Tag State
  locations : List (LocationState TypeId)
deriving Repr

def setLocation (locations : LocationStore TypeId) (allocation offset : Nat)
    (state : LocationState TypeId) : Option (LocationStore TypeId) :=
  if locations.any (fun entry => entry.1 == allocation && entry.2 == offset) then
    some (locations.map (fun entry =>
      if entry.1 == allocation && entry.2 == offset then
        (allocation, offset, state)
      else entry))
  else none

theorem setLocation_length (locations : LocationStore TypeId)
    (allocation offset : Nat) (state : LocationState TypeId)
    (result : LocationStore TypeId)
    (hresult : setLocation locations allocation offset state = some result) :
    result.length = locations.length := by
  simp [setLocation] at hresult
  split at hresult <;> simp_all

structure Store (Tag State : Type) where
  allocations : List (AllocId × Allocation Tag State)
  nextId : AllocId
deriving Repr

def renameAllocation (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) : AllocId × Allocation Tag State :=
  let allocation := entry.2
  (entry.1,
    { allocation with
      address := allocation.address.map (fun _ => resolve entry.1)
      bytes := allocation.bytes.map (renameByte resolve) })

def renameStore (resolve : AllocId → Nat) (store : Store Tag State) : Store Tag State :=
  { store with allocations := store.allocations.map (renameAllocation resolve) }

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

theorem renameStore_idempotent (resolve : AllocId → Nat) (store : Store Tag State) :
    renameStore resolve (renameStore resolve store) = renameStore resolve store := by
  simp [renameStore, renameAllocation, renameByte]

theorem storesCorrespond_refl (resolve : AllocId → Nat) (store : Store Tag State) :
    storesCorrespond resolve (renameStore resolve store) (renameStore resolve store) := by
  simp [storesCorrespond, renameStore_idempotent]

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
deriving Repr

structure HookRequest where
  choice : HookChoice
  footprint : Footprint
deriving Repr

structure Fault (F : Type) where
  value : F
deriving Repr

inductive Result (Tag State F A : Type) where
  | ok (value : A) (store : Store Tag State) (footprint : Footprint)
  | fault (error : Fault F) (store : Store Tag State) (footprint : Footprint)
  | refused (reason : String) (store : Store Tag State) (footprint : Footprint)
deriving Repr

def lookup (store : Store Tag State) (id : AllocId) : Option (Allocation Tag State) :=
  store.allocations.find? (fun entry => entry.1 == id) |>.map (·.2)

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
      bytes := metadata.allocation.bytes.set! offset byte }
    some ({ metadata with allocation := allocation },
      footprint .write { allocation := 0, offset := offset, width := 1 })

theorem storeMetadataByte_preserves_locations
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : storeMetadataByte metadata offset byte = some result) :
    result.1.locations = metadata.locations := by
  simp [storeMetadataByte] at hresult
  split at hresult <;> simp_all

def typedStoreMetadataByte (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag) :
    Option (AllocationMetadata Tag State TypeId × Footprint) :=
  if offset ≥ metadata.allocation.bytes.length then none
  else
    let allocation := { metadata.allocation with
      bytes := metadata.allocation.bytes.set! offset byte }
    let locations := metadata.locations.set! offset
      { effectiveType := .typed typeId, initialized := true }
    some ({ allocation := allocation, locations := locations },
      footprint .write { allocation := 0, offset := offset, width := 1 })

theorem typedStoreMetadataByte_preserves_length
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (typeId : TypeId) (byte : Byte Tag)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : typedStoreMetadataByte metadata offset typeId byte = some result) :
    result.1.locations.length = metadata.locations.length := by
  simp [typedStoreMetadataByte] at hresult
  split at hresult <;> simp_all

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

def pairedTypedStoreMetadataByte (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag) :
    Option ((AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint)) := do
  let sourceResult ← typedStoreMetadataByte metadata offset typeId byte
  let targetResult ← typedStoreMetadataByte (renameMetadata resolve id metadata)
    offset typeId (renameByte resolve byte)
  if targetResult.1 = renameMetadata resolve id sourceResult.1 &&
      targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedTypedStoreMetadataByte_corresponds
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedTypedStoreMetadataByte resolve id metadata offset typeId byte =
      some result) :
    result.2.1 = renameMetadata resolve id result.1.1 ∧
      result.2.2 = result.1.2 := by
  simp [pairedTypedStoreMetadataByte] at hresult
  split at hresult <;> simp_all

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

def pairedTypedLoadMetadataByte [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) :
    Option ((Byte Tag × Footprint) × (Byte Tag × Footprint)) := do
  let sourceResult ← typedLoadMetadataByte metadata offset typeId
  let targetResult ← typedLoadMetadataByte (renameMetadata resolve id metadata)
    offset typeId
  if targetResult.1 = renameByte resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedTypedLoadMetadataByte_corresponds [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedTypedLoadMetadataByte resolve id metadata offset typeId =
      some result) :
    result.2.1 = renameByte resolve result.1.1 ∧
      result.2.2 = result.1.2 := by
  simp [pairedTypedLoadMetadataByte] at hresult
  split at hresult <;> simp_all

def unionLoadMetadataByte
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) : Option (Byte Tag × Footprint) := do
  let byte ← metadata.allocation.bytes[offset]?
  let location ← metadata.locations[offset]?
  if !location.initialized then none
  else some (byte, footprint .read { allocation := 0, offset := offset, width := 1 })

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

def mergeBytes (old values masks choices : List UInt8) : Option (List (Byte Tag)) :=
  if old.length != values.length || values.length != masks.length ||
      masks.length != choices.length then none
  else some (List.zipWith (fun oldByte entry =>
    mergeByte oldByte entry.1.1 entry.1.2.1 entry.1.2.2)
    old (List.zipWith (fun value mask => (value, mask)) values masks
      |>.zip choices))

def mergeFootprint (allocation offset width : Nat) : Footprint :=
  footprint .write { allocation := allocation, offset := offset, width := width }

theorem mergeByte_preserves_pointer_fragment
    (pointer : Provenance Tag) (fragment : Nat)
    (bits mask value choice : UInt8) :
    (mergeByte (.value bits (some pointer) (some fragment)) mask value choice).provenance =
      some pointer ∧
    (mergeByte (.value bits (some pointer) (some fragment)) mask value choice).fragment =
      some fragment := by
  simp [mergeByte]

def copySnapshot (source destination : List (Byte Tag)) : Option (List (Byte Tag)) :=
  if source.length == destination.length then some source else none

def copyFootprint (source destination : Region) (width : Nat) : Footprint :=
  { accesses := [(.read { source with width := width }),
                 (.write { destination with width := width })] }

def regionsOverlap (source destination : Region) (width : Nat) : Bool :=
  source.allocation == destination.allocation &&
    source.offset < destination.offset + width &&
    destination.offset < source.offset + width

def memcpySnapshot (source destination : Region) (bytes : List (Byte Tag)) :
    Option (List (Byte Tag)) :=
  if regionsOverlap source destination bytes.length then none
  else copySnapshot bytes bytes

def memmoveSnapshot (_source _destination : Region) (bytes : List (Byte Tag)) :
    Option (List (Byte Tag)) := some bytes

inductive ReallocOutcome (Tag State TypeId : Type) where
  | failed (old : AllocationMetadata Tag State TypeId)
  | replaced (fresh : AllocationMetadata Tag State TypeId)
deriving Repr

def reallocMetadata (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    Option (ReallocOutcome Tag State TypeId × Footprint) :=
  match placement with
  | .fail => some (.failed old, footprint .metadata
      { allocation := 0, offset := 0, width := old.allocation.bytes.length })
  | .address base | .unaddressable =>
      if locations.length != request.bytes.length then none
      else some (.replaced
        { allocation :=
            { live := true
              address := match placement with | .address _ => some base | .unaddressable => none
              bytes := request.bytes
              state := request.state }
          locations := locations },
        footprint .metadata { allocation := 0, offset := 0,
          width := request.bytes.length })

inductive ZeroSizeOutcome (Tag State TypeId : Type) where
  | null
  | token (metadata : AllocationMetadata Tag State TypeId)
deriving Repr

def allocateZeroSize (state : State) (placement : Placement) :
    ZeroSizeOutcome Tag State TypeId × Footprint :=
  match placement with
  | .fail => (.null, footprint .metadata { allocation := 0, offset := 0, width := 0 })
  | .address base =>
      (.token { allocation :=
          { live := true, address := some base, bytes := [], state := state }
          locations := [] },
       footprint .metadata { allocation := 0, offset := 0, width := 0 })
  | .unaddressable =>
      (.token { allocation :=
          { live := true, address := none, bytes := [], state := state }
          locations := [] },
       footprint .metadata { allocation := 0, offset := 0, width := 0 })

def renameZeroSizeOutcome (resolve : AllocId → Nat) :
    ZeroSizeOutcome Tag State TypeId → ZeroSizeOutcome Tag State TypeId
  | .null => .null
  | .token metadata =>
      .token { metadata with
        allocation := { metadata.allocation with
          address := metadata.allocation.address.map (fun _ => resolve 0) } }

def pairedAllocateZeroSize (resolve : AllocId → Nat) (state : State)
    (placement : Placement) : Bool :=
  let source := allocateZeroSize state placement
  let target := allocateZeroSize state (match placement with
    | .address _ => .address (resolve 0)
    | .unaddressable => .unaddressable
    | .fail => .fail)
  target.1 = renameZeroSizeOutcome resolve source.1 && target.2 = source.2

theorem pairedAllocateZeroSize_sound (resolve : AllocId → Nat) (state : State)
    (placement : Placement)
    (h : pairedAllocateZeroSize resolve state placement = true) :
    (allocateZeroSize state (match placement with
      | .address _ => .address (resolve 0)
      | .unaddressable => .unaddressable
      | .fail => .fail)).1 =
      renameZeroSizeOutcome resolve (allocateZeroSize state placement).1 := by
  simpa [pairedAllocateZeroSize] using congrArg And.left h

inductive ReallocZeroOutcome where
  | freedNull
  | refusedUndefined
deriving Repr, BEq

def reallocZeroGNU17 : ReallocZeroOutcome := .freedNull

def isZeroToken (metadata : AllocationMetadata Tag State TypeId) : Bool :=
  metadata.allocation.live && metadata.allocation.bytes.isEmpty

def zeroTokenEqual (left right : AllocationMetadata Tag State TypeId) : Bool :=
  isZeroToken left && isZeroToken right && left.allocation.address == right.allocation.address

def zeroTokenFreeable (metadata : AllocationMetadata Tag State TypeId) : Bool :=
  isZeroToken metadata

def renameZeroTokenMetadata (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    AllocationMetadata Tag State TypeId :=
  { metadata with
    allocation := { metadata.allocation with
      address := metadata.allocation.address.map (fun _ => resolve 0) } }

theorem renameZeroTokenMetadata_selfEqual (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId)
    (h : isZeroToken metadata) :
    zeroTokenEqual (renameZeroTokenMetadata resolve metadata)
      (renameZeroTokenMetadata resolve metadata) = true := by
  simp [zeroTokenEqual, renameZeroTokenMetadata, isZeroToken, h]

theorem renameZeroTokenMetadata_freeable (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    zeroTokenFreeable (renameZeroTokenMetadata resolve metadata) =
      zeroTokenFreeable metadata := by
  simp [zeroTokenFreeable, isZeroToken, renameZeroTokenMetadata]

def freeMetadata (metadata : AllocationMetadata Tag State TypeId) :
    Option (AllocationMetadata Tag State TypeId × Footprint) :=
  if metadata.allocation.live then
    some ({ metadata with allocation := { metadata.allocation with live := false } },
      footprint .metadata { allocation := 0, offset := 0,
        width := metadata.allocation.bytes.length })
  else none

def pairedFreeMetadata (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    Option ((AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint)) := do
  let sourceResult ← freeMetadata metadata
  let targetResult ← freeMetadata (renameZeroTokenMetadata resolve metadata)
  if targetResult.1 = renameZeroTokenMetadata resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedFreeMetadata_corresponds
    (resolve : AllocId → Nat) (metadata : AllocationMetadata Tag State TypeId)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint))
    (hresult : pairedFreeMetadata resolve metadata = some result) :
    result.2.1 = renameZeroTokenMetadata resolve result.1.1 ∧
      result.2.2 = result.1.2 := by
  simp [pairedFreeMetadata] at hresult
  split at hresult <;> simp_all

inductive FreeOutcome where
  | nullSuccess
  | freed
  | stalePointer
  | unmatchedPointer
deriving Repr, BEq

def freePointer (metadata : Option (AllocationMetadata Tag State TypeId)) : FreeOutcome :=
  match metadata with
  | none => .nullSuccess
  | some metadata => if metadata.allocation.live then .freed else .stalePointer

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

def allocationsWf : List (AllocId × Allocation Tag State) → Prop
  | [] => True
  | (id, allocation) :: rest =>
      bytesWf id allocation.bytes ∧
      allocationsWf rest ∧
      ∀ other, (other, _) ∈ rest → id ≠ other

def WellFormed (store : Store Tag State) : Prop :=
  allocationsWf store.allocations

theorem bytesWf_renameByte (resolve : AllocId → Nat) (id : AllocId)
    (bytes : List (Byte Tag)) :
    bytesWf id (bytes.map (renameByte resolve)) ↔ bytesWf id bytes := by
  induction bytes with
  | nil => simp [bytesWf]
  | cons byte rest ih =>
      cases byte <;> simp [bytesWf, renameByte, ih]

theorem allocationsWf_rename (resolve : AllocId → Nat)
    (allocations : List (AllocId × Allocation Tag State)) :
    allocationsWf (allocations.map (renameAllocation resolve)) ↔
      allocationsWf allocations := by
  induction allocations with
  | nil => simp [allocationsWf]
  | cons entry rest ih =>
      rcases entry with ⟨id, allocation⟩
      simp only [List.map_cons, allocationsWf, renameAllocation]
      constructor
      · intro h
        refine ⟨?_, ?_, ?_⟩
        · exact (bytesWf_renameByte resolve id allocation.bytes).mp h.1
        · exact ih.mp h.2.1
        · intro other hmem
          apply h.2.2 other
          obtain ⟨entry, hentry, rfl⟩ := List.mem_map.1 hmem
          exact ⟨entry, hentry, by rfl⟩
      · intro h
        refine ⟨?_, ?_, ?_⟩
        · exact (bytesWf_renameByte resolve id allocation.bytes).mpr h.1
        · exact ih.mpr h.2.1
        · intro other hmem
          apply h.2.2 other
          obtain ⟨entry, hentry, rfl⟩ := List.mem_map.1 hmem
          exact ⟨entry, hentry, by rfl⟩

theorem renameStore_wf (resolve : AllocId → Nat) (store : Store Tag State)
    (hstore : WellFormed store) : WellFormed (renameStore resolve store) := by
  exact (allocationsWf_rename resolve store.allocations).mpr hstore

def footprint (kind : AccessKind) (region : Region) : Footprint :=
  { accesses := [(kind, region)] }

structure AllocationRequest (Tag State : Type) where
  bytes : List (Byte Tag)
  state : State
deriving Repr

inductive Placement where
  | address (base : Nat)
  | unaddressable
  | fail
deriving Repr, BEq

def intervalOverlap (leftBase leftSize rightBase rightSize : Nat) : Bool :=
  leftBase < rightBase + rightSize && rightBase < leftBase + leftSize

def placementAllowed (store : Store Tag State) (base size : Nat) : Bool :=
  store.allocations.all fun entry =>
    let allocation := entry.2
    match allocation.live, allocation.address with
    | true, some otherBase =>
        !intervalOverlap base size otherBase allocation.bytes.length
    | _, _ => true

def alignmentAllowed (base alignment : Nat) : Bool :=
  alignment > 0 && base % alignment == 0


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

inductive OffsetFault where
  | outOfBounds
  | alignment
deriving Repr, BEq

structure Exposure where
  exposed : Bool
deriving Repr, BEq

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

inductive ReplayEnding where
  | exit (status : Int)
  | signal (number : Nat)
  | exhausted
  | diverges
  | ub (clause operand : String)
  | refused (name : String)
deriving Repr, BEq

structure ReplayFixture where
  sourceHash : String
  compilerVersion : String
  targetTriple : String
  placements : List ReplayPlacement
  events : List ReplayEvent
  ending : ReplayEnding
deriving Repr

def ReplayFixture.wellFormed (fixture : ReplayFixture) : Prop :=
  fixture.sourceHash ≠ "" ∧ fixture.compilerVersion ≠ "" ∧
    fixture.targetTriple ≠ "" ∧
    fixture.placements.Pairwise (fun left right =>
      left.base + left.size ≤ right.base ∨ right.base + right.size ≤ left.base)

def expose (state : Exposure) : Exposure := { exposed := true }

inductive Recovery where
  | recovered (pointer : Pointer Tag)
  | empty (address : Nat)
  | ambiguousOnePastAdjacent
  | noLiveAllocation
deriving Repr, BEq

def recoverAddress (address : Nat) (live : List (AllocId × Nat × Nat × Tag)) : Recovery :=
  match live.find? (fun entry => entry.2.1 ≤ address && address < entry.2.2) with
  | some entry => .recovered { provenance := some { allocation := entry.1, tag := entry.2.3 }, address := address }
  | none => .empty address

def offsetPointer (pointer : Pointer Tag) (elementSize : Nat) (delta : Int)
    (bound : Nat) : Except OffsetFault (Pointer Tag) :=
  if elementSize == 0 then .error .alignment
  else
    let magnitude := Int.natAbs delta * elementSize
    let address := if delta < 0 then pointer.address - magnitude else pointer.address + magnitude
    if address > bound then .error .outOfBounds else .ok { pointer with address := address }

theorem offsetPointer_zero (pointer : Pointer Tag) (elementSize bound : Nat)
    (hsize : elementSize > 0) (hbound : pointer.address ≤ bound) :
    offsetPointer pointer elementSize 0 bound = .ok pointer := by
  simp [offsetPointer, Nat.not_eq_zero_of_lt hsize, hbound]

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
              footprint .metadata { allocation := id, offset := 0,
                width := request.bytes.length })
  | .unaddressable =>
      let id := store.nextId
      let allocation : Allocation Tag State :=
        { live := true, address := none, bytes := request.bytes, state := request.state }
      some ({ allocations := store.allocations ++ [(id, allocation)],
              nextId := id + 1 },
            footprint .metadata { allocation := id, offset := 0,
              width := request.bytes.length })

def allocateAligned (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment : Nat) : Option (Store Tag State × Footprint) :=
  match placement with
  | .address base =>
      if !alignmentAllowed base alignment then none
      else allocate store request placement
  | _ => allocate store request placement

inductive PlacementFault where
  | exhausted
  | overlap
  | misaligned
deriving Repr, BEq

def placementWithin (base size limit : Nat) : Bool :=
  base ≤ limit && size ≤ limit - base

structure PlacementAgreement where
  left right : AllocId → Option Nat
  exposed : AllocId → Bool

def PlacementAgreement.agrees (agreement : PlacementAgreement) : Prop :=
  ∀ allocation, agreement.exposed allocation →
    agreement.left allocation = agreement.right allocation

theorem PlacementAgreement.refl (left : AllocId → Option Nat)
    (exposed : AllocId → Bool) :
    (PlacementAgreement.mk left left exposed).agrees := by
  intro allocation _
  rfl

def placementOf (store : Store Tag State) (id : AllocId) : Option Nat :=
  (lookup store id).bind Allocation.address

def placementAgreementOfStores (left right : Store Tag State)
    (exposed : AllocId → Bool) : PlacementAgreement :=
  { left := placementOf left
    right := placementOf right
    exposed := exposed }

theorem placementAgreementOfStores_refl (store : Store Tag State)
    (exposed : AllocId → Bool) :
    (placementAgreementOfStores store store exposed).agrees := by
  apply PlacementAgreement.refl

theorem allocate_fresh_id {Tag State : Type} (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (result : Store Tag State × Footprint)
    (hresult : allocate store request placement = some result) :
    result.1.nextId = store.nextId + 1 := by
  cases placement <;> simp [allocate] at hresult
  · omega
  · omega

def renamedPlacement (resolve : AllocId → Nat) (id : AllocId) :
    Placement → Placement
  | .address _ => .address (resolve id)
  | .unaddressable => .unaddressable
  | .fail => .fail

def pairedAllocate (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement) :
    Option ((Store Tag State × Footprint) × (Store Tag State × Footprint)) := do
  let sourceResult ← allocate store request placement
  let targetResult ← allocate (renameStore resolve store) request
    (renamedPlacement resolve store.nextId placement)
  if targetResult.1 = renameStore resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedAllocate_corresponds
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (result : (Store Tag State × Footprint) × (Store Tag State × Footprint))
    (hresult : pairedAllocate resolve store request placement = some result) :
    result.2.1 = renameStore resolve result.1.1 ∧
      result.2.2 = result.1.2 := by
  simp [pairedAllocate] at hresult
  split at hresult <;> simp_all

def pairedAllocateFailure (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement) : Bool :=
  (allocate store request placement).isNone &&
    (allocate (renameStore resolve store) request
      (renamedPlacement resolve store.nextId placement)).isNone

theorem pairedAllocateFailure_preserves
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (hfailure : pairedAllocateFailure resolve store request placement = true) :
    (allocate store request placement).isNone ∧
      (allocate (renameStore resolve store) request
        (renamedPlacement resolve store.nextId placement)).isNone := by
  simpa [pairedAllocateFailure] using hfailure

def unaddressableToken (store : Store Tag State) (id : AllocId) : Bool :=
  match lookup store id with
  | some allocation => allocation.live && allocation.address.isNone
  | none => false

def pairedUnaddressableAllocation (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State) :
    Bool :=
  match allocate store request .unaddressable,
    allocate (renameStore resolve store) request .unaddressable with
  | some (source, _), some (target, _) =>
      target = renameStore resolve source &&
      unaddressableToken source (store.nextId) &&
      unaddressableToken target (store.nextId)
  | _, _ => false

theorem pairedUnaddressableAllocation_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State)
    (h : pairedUnaddressableAllocation resolve store request = true) :
    ∃ source target sourceFootprint targetFootprint,
      allocate store request .unaddressable = some (source, sourceFootprint) ∧
      allocate (renameStore resolve store) request .unaddressable =
        some (target, targetFootprint) ∧
      target = renameStore resolve source := by
  simp [pairedUnaddressableAllocation] at h
  split at h <;> simp_all

def footprintAgrees (left right : Footprint) : Prop :=
  left.accesses.length = right.accesses.length ∧
    List.zipWith (fun l r => l.1 == r.1 && l.2.width == r.2.width)
      left.accesses right.accesses |>.all id

theorem footprintAgrees_refl (footprint : Footprint) :
    footprintAgrees footprint footprint := by
  simp [footprintAgrees]

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

def allocateMetadata (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    Option (AllocationMetadata Tag State TypeId × Footprint) :=
  match placement with
  | .fail => none
  | .address base | .unaddressable =>
      if locations.length != request.bytes.length then none
      else
        some ({ allocation :=
                 { live := true
                   address := match placement with | .address _ => some base | .unaddressable => none
                   bytes := request.bytes
                   state := request.state }
               locations := locations },
              footprint .metadata { allocation := 0, offset := 0,
                width := request.bytes.length })

theorem allocateMetadata_wf {Tag State TypeId : Type}
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : allocateMetadata request locations placement = some result)
    (hbytes : ∀ id, bytesWf id request.bytes) :
    result.1.wellFormed 0 := by
  cases placement <;> simp [allocateMetadata] at hresult
  · simp_all [AllocationMetadata.wellFormed]
  · simp_all [AllocationMetadata.wellFormed]

theorem allocate_wf {Tag State : Type} (store : Store Tag State)
    (hstore : WellFormed store) (request : AllocationRequest Tag State)
    (placement : Placement) (result : Store Tag State × Footprint)
    (hresult : allocate store request placement = some result) :
    WellFormed result.1 := by
  cases placement <;> simp [allocate] at hresult
  · omega
  · simp_all [WellFormed, allocationsWf, bytesWf]

#guard (allocate (Tag := Unit) (State := Unit)
  { allocations := [], nextId := 0 }
  { bytes := [Byte.uninitialized], state := () } (Placement.address 16)).isSome

def storeByte (store : Store Tag State) (id offset : Nat)
    (byte : Byte Tag) : Option (Store Tag State × Footprint) := do
  let allocation ← lookup store id
  if !allocation.live then none
  else if offset ≥ allocation.bytes.length then none
  else
    let bytes := allocation.bytes.set! offset byte
    let updated := { allocation with bytes := bytes }
    let allocations := store.allocations.map (fun entry =>
      if entry.1 == id then (id, updated) else entry)
    some ({ store with allocations := allocations }, footprint .write
      { allocation := id, offset := offset, width := 1 })

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
  if targetResult.1 = renameStore resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedStoreByte_corresponds
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : AllocId) (byte : Byte Tag)
    (result : (Store Tag State × Footprint) × (Store Tag State × Footprint))
    (hresult : pairedStoreByte resolve store id offset byte = some result) :
    storeTransitionCorresponds resolve store (renameStore resolve store)
      result.1 result.2 := by
  simp [pairedStoreByte, storeTransitionCorresponds] at hresult
  obtain ⟨sourceResult, targetResult, hpair⟩ := hresult
  simp_all

def loadByte (store : Store Tag State) (id offset : Nat) :
    Option (Byte Tag × Footprint) := do
  let allocation ← lookup store id
  if !allocation.live then none
  else
    let byte ← allocation.bytes[offset]?
    some (byte, footprint .read { allocation := id, offset := offset, width := 1 })

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
  if targetResult.1 = renameByte resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedLoadByte_corresponds
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedLoadByte resolve store id offset = some result) :
    loadTransitionCorresponds resolve store (renameStore resolve store)
      result.1 result.2 := by
  simp [pairedLoadByte, loadTransitionCorresponds] at hresult
  obtain ⟨sourceResult, targetResult, hpair⟩ := hresult
  simp_all

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
  if targetLoad.1 = renameByte resolve sourceLoad.1 &&
      targetLoad.2 = sourceLoad.2 then
    some { sourceStore := stores.1, targetStore := stores.2
           sourceLoad := sourceLoad, targetLoad := targetLoad }
  else none

theorem pairedStoreLoadByte_sound (resolve : AllocId → Nat)
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (pair : StoreLoadPair Tag State)
    (hpair : pairedStoreLoadByte resolve store id offset byte = some pair) :
    pair.targetStore.1 = renameStore resolve pair.sourceStore.1 ∧
      pair.targetLoad.1 = renameByte resolve pair.sourceLoad.1 ∧
      pair.targetStore.2 = pair.sourceStore.2 ∧
      pair.targetLoad.2 = pair.sourceLoad.2 := by
  simp [pairedStoreLoadByte, pairedStoreByte] at hpair
  split at hpair <;> simp_all

def endLifetime (store : Store Tag State) (id : AllocId) :
    Option (Store Tag State × Footprint) := do
  let allocation ← lookup store id
  if !allocation.live then none
  else
    let updated := { allocation with live := false }
    let allocations := store.allocations.map (fun entry =>
      if entry.1 == id then (id, updated) else entry)
    some ({ store with allocations := allocations },
      footprint .metadata { allocation := id, offset := 0,
        width := allocation.bytes.length })

def pairedEndLifetime (resolve : AllocId → Nat) (store : Store Tag State)
    (id : AllocId) :
    Option ((Store Tag State × Footprint) × (Store Tag State × Footprint)) := do
  let sourceResult ← endLifetime store id
  let targetResult ← endLifetime (renameStore resolve store) id
  if targetResult.1 = renameStore resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedEndLifetime_corresponds
    (resolve : AllocId → Nat) (store : Store Tag State) (id : AllocId)
    (result : (Store Tag State × Footprint) × (Store Tag State × Footprint))
    (hresult : pairedEndLifetime resolve store id = some result) :
    result.2.1 = renameStore resolve result.1.1 ∧
      result.2.2 = result.1.2 := by
  simp [pairedEndLifetime] at hresult
  split at hresult <;> simp_all

def pairedStaleLoad (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) : Bool :=
  match endLifetime store id, endLifetime (renameStore resolve store) id with
  | some sourceResult, some targetResult =>
      (loadByte sourceResult.1 id offset).isNone &&
      (loadByte targetResult.1 id offset).isNone
  | _, _ => false

theorem pairedStaleLoad_sound (resolve : AllocId → Nat)
    (store : Store Tag State) (id offset : Nat)
    (h stale : pairedStaleLoad resolve store id offset = true) :
    (loadByte (endLifetime store id).getD (store, {}).1 id offset).isNone := by
  simp [pairedStaleLoad] at stale
  split at stale <;> simp_all

def pairedStaleStore (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag) : Bool :=
  match endLifetime store id, endLifetime (renameStore resolve store) id with
  | some sourceResult, some targetResult =>
      (storeByte sourceResult.1 id offset byte).isNone &&
      (storeByte targetResult.1 id offset (renameByte resolve byte)).isNone
  | _, _ => false

theorem pairedStaleStore_sound (resolve : AllocId → Nat)
    (store : Store Tag State) (id offset : Nat) (byte : Byte Tag)
    (h : pairedStaleStore resolve store id offset byte = true) :
    (storeByte (endLifetime store id).getD (store, {}).1 id offset byte).isNone := by
  simp [pairedStaleStore] at h
  split at h <;> simp_all

theorem endLifetime_wf {Tag State : Type} (store : Store Tag State)
    (hstore : WellFormed store) (id : AllocId)
    (result : Store Tag State × Footprint)
    (hresult : endLifetime store id = some result) :
    WellFormed result.1 := by
  simp [endLifetime] at hresult
  split at hresult <;> simp_all [WellFormed, allocationsWf, bytesWf]

theorem storeByte_wf {Tag State : Type} (store : Store Tag State)
    (hstore : WellFormed store) (id offset : Nat) (byte : Byte Tag)
    (result : Store Tag State × Footprint)
    (hresult : storeByte store id offset byte = some result) :
    WellFormed result.1 := by
  simp [storeByte] at hresult
  split at hresult <;> simp_all [WellFormed, allocationsWf, bytesWf]

theorem loadByte_wf {Tag State : Type} (store : Store Tag State)
    (hstore : WellFormed store) (id offset : Nat)
    (result : Byte Tag × Footprint)
    (hresult : loadByte store id offset = some result) :
    WellFormed store := hstore

#guard (bytesWf 3 [Byte.uninitialized] : Prop) = True
#guard (footprint .read { allocation := 1, offset := 0, width := 1 }).accesses.length == 1

end LeanModels.C.F2
