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

theorem renamePointer_comp (first second : AllocId → Nat) (pointer : Pointer Tag) :
    renamePointer second (renamePointer first pointer) = renamePointer second pointer := by
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

def renameValue (resolve : AllocId → Nat) : Value Tag → Value Tag
  | .scalar bytes => .scalar bytes
  | .pointer pointer => .pointer (renamePointer resolve pointer)
  | .aggregate members => .aggregate (members.map (renameValue resolve))

theorem encodeValue_rename (resolve : AllocId → Nat) (value : Value Tag) :
    encodeValue (renameValue resolve value) =
      (encodeValue value).map (renameByte resolve) := by
  induction value with
  | scalar bytes => simp [encodeValue, renameValue, renameByte]
  | pointer pointer =>
      cases pointer.provenance <;>
        simp [encodeValue, renameValue, encodePointer, renamePointer, renameByte,
          pointerByte]
  | aggregate members ih =>
      simp [encodeValue, renameValue, List.flatMap_map, ih]

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

theorem encodePointer_rename (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    encodePointer (renamePointer resolve pointer) =
      (encodePointer pointer).map (renameByte resolve) := by
  cases pointer with
  | mk provenance address =>
      cases provenance <;> simp [encodePointer, renamePointer, renameByte, pointerByte]

theorem decodePointer_rename_encode (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    decodePointer ((encodePointer pointer).map (renameByte resolve)) =
      some (renamePointer resolve pointer) := by
  rw [← encodePointer_rename]
  exact decodePointer_encodePointer _

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

def renameAllocationValue (resolve : AllocId → Nat) (id : AllocId)
    (allocation : Allocation Tag State) : Allocation Tag State :=
  { allocation with
    address := allocation.address.map (fun _ => resolve id)
    bytes := allocation.bytes.map (renameByte resolve) }

theorem renameAllocation_value (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).2 =
      renameAllocationValue resolve entry.1 entry.2 := by
  rfl

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

theorem renameStore_comp (first second : AllocId → Nat) (store : Store Tag State) :
    renameStore second (renameStore first store) = renameStore second store := by
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

def renameRegion (_resolve : AllocId → Nat) (region : Region) : Region := region

def renameFootprint (resolve : AllocId → Nat) (footprint : Footprint) : Footprint :=
  { accesses := footprint.accesses.map (fun access =>
      (access.1, renameRegion resolve access.2)) }

theorem renameRegion_identity (resolve : AllocId → Nat) (region : Region) :
    renameRegion resolve region = region := by
  rfl

theorem renameFootprint_identity (resolve : AllocId → Nat) (footprint : Footprint) :
    renameFootprint resolve footprint = footprint := by
  simp [renameFootprint, renameRegion]

structure HookRequest where
  choice : HookChoice
  footprint : Footprint
deriving Repr

def renameHookRequest (resolve : AllocId → Nat) (request : HookRequest) : HookRequest :=
  { request with footprint := renameFootprint resolve request.footprint }

theorem renameHookRequest_identity (resolve : AllocId → Nat) (request : HookRequest) :
    renameHookRequest resolve request = request := by
  simp [renameHookRequest, renameFootprint_identity]

structure Fault (F : Type) where
  value : F
deriving Repr

inductive Result (Tag State F A : Type) where
  | ok (value : A) (store : Store Tag State) (footprint : Footprint)
  | fault (error : Fault F) (store : Store Tag State) (footprint : Footprint)
  | refused (reason : String) (store : Store Tag State) (footprint : Footprint)
deriving Repr

def renameResult (resolve : AllocId → Nat) :
    Result Tag State F (Byte Tag) → Result Tag State F (Byte Tag)
  | .ok value store footprint =>
      .ok (renameByte resolve value) (renameStore resolve store)
        (renameFootprint resolve footprint)
  | .fault error store footprint =>
      .fault error (renameStore resolve store) (renameFootprint resolve footprint)
  | .refused reason store footprint =>
      .refused reason (renameStore resolve store) (renameFootprint resolve footprint)

theorem renameResult_kind_preserved (resolve : AllocId → Nat)
    (result : Result Tag State F (Byte Tag)) :
    match result, renameResult resolve result with
    | .ok .., .ok .. => True
    | .fault .., .fault .. => True
    | .refused .., .refused .. => True
    | _, _ => False := by
  cases result <;> simp [renameResult]

theorem renameResult_refusal_reason (resolve : AllocId → Nat)
    (reason : String) (store : Store Tag State) (footprint : Footprint) :
    renameResult resolve (.refused reason store footprint) =
      .refused reason (renameStore resolve store) (renameFootprint resolve footprint) := by
  rfl

def lookup (store : Store Tag State) (id : AllocId) : Option (Allocation Tag State) :=
  store.allocations.find? (fun entry => entry.1 == id) |>.map (·.2)

theorem lookup_renameStore (resolve : AllocId → Nat) (store : Store Tag State)
    (id : AllocId) :
    lookup (renameStore resolve store) id =
      (lookup store id).map (renameAllocationValue resolve id) := by
  cases store with
  | mk allocations nextId =>
      induction allocations with
      | nil => simp [lookup, renameStore]
      | cons entry rest ih =>
          rcases entry with ⟨entryId, allocation⟩
          by_cases h : entryId == id <;>
            simp [lookup, renameStore, renameAllocation, renameAllocationValue, h, ih]

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

theorem renameMetadata_preserves_byte_length (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).allocation.bytes.length =
      metadata.allocation.bytes.length := by
  simp [renameMetadata]

theorem renameMetadata_preserves_location_length (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).locations.length = metadata.locations.length := by
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

def pairedTypedStoreLoadMetadataByte [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag) :
    Option ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))) := do
  let sourceStore ← typedStoreMetadataByte metadata offset typeId byte
  let targetStore ← typedStoreMetadataByte (renameMetadata resolve id metadata)
    offset typeId (renameByte resolve byte)
  let sourceLoad ← typedLoadMetadataByte sourceStore.1 offset typeId
  let targetLoad ← typedLoadMetadataByte targetStore.1 offset typeId
  if targetStore.1 = renameMetadata resolve id sourceStore.1 &&
      targetStore.2 = sourceStore.2 &&
      targetLoad.1 = renameByte resolve sourceLoad.1 &&
      targetLoad.2 = sourceLoad.2 then
    some ((sourceStore, sourceLoad), (targetStore, targetLoad))
  else none

theorem pairedTypedStoreLoadMetadataByte_sound [BEq TypeId]
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (typeId : TypeId) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)))
    (hresult : pairedTypedStoreLoadMetadataByte resolve id metadata offset typeId byte =
      some result) :
    result.2.1.1 = renameMetadata resolve id result.1.1.1 ∧
      result.2.1.2 = result.1.1.2 ∧
      result.2.2.1 = renameByte resolve result.1.2.1 ∧
      result.2.2.2 = result.1.2.2 := by
  simp [pairedTypedStoreLoadMetadataByte] at hresult
  split at hresult <;> simp_all

def unionLoadMetadataByte
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) : Option (Byte Tag × Footprint) := do
  let byte ← metadata.allocation.bytes[offset]?
  let location ← metadata.locations[offset]?
  if !location.initialized then none
  else some (byte, footprint .read { allocation := 0, offset := offset, width := 1 })

def pairedUnionLoadMetadataByte (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat) :
    Option ((Byte Tag × Footprint) × (Byte Tag × Footprint)) := do
  let sourceResult ← unionLoadMetadataByte metadata offset
  let targetResult ← unionLoadMetadataByte (renameMetadata resolve id metadata) offset
  if targetResult.1 = renameByte resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedUnionLoadMetadataByte_corresponds
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedUnionLoadMetadataByte resolve id metadata offset =
      some result) :
    result.2.1 = renameByte resolve result.1.1 ∧
      result.2.2 = result.1.2 := by
  simp [pairedUnionLoadMetadataByte] at hresult
  split at hresult <;> simp_all

def pairedStoreUnionLoadMetadataByte
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) :
    Option ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))) := do
  let sourceStore ← storeMetadataByte metadata offset byte
  let targetStore ← storeMetadataByte (renameMetadata resolve id metadata)
    offset (renameByte resolve byte)
  let sourceLoad ← unionLoadMetadataByte sourceStore.1 offset
  let targetLoad ← unionLoadMetadataByte targetStore.1 offset
  if targetStore.1 = renameMetadata resolve id sourceStore.1 &&
      targetStore.2 = sourceStore.2 &&
      targetLoad.1 = renameByte resolve sourceLoad.1 &&
      targetLoad.2 = sourceLoad.2 then
    some ((sourceStore, sourceLoad), (targetStore, targetLoad))
  else none

theorem pairedStoreUnionLoadMetadataByte_sound
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)))
    (hresult : pairedStoreUnionLoadMetadataByte resolve id metadata offset byte =
      some result) :
    result.2.1.1 = renameMetadata resolve id result.1.1.1 ∧
      result.2.1.2 = result.1.1.2 ∧
      result.2.2.1 = renameByte resolve result.1.2.1 ∧
      result.2.2.2 = result.1.2.2 := by
  simp [pairedStoreUnionLoadMetadataByte] at hresult
  split at hresult <;> simp_all

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

def pairedMergeByte (resolve : AllocId → Nat) (old : Byte Tag)
    (mask value choice : UInt8) : Option (Byte Tag × Byte Tag) :=
  let source := mergeByte old mask value choice
  let target := mergeByte (renameByte resolve old) mask value choice
  if target = renameByte resolve source then some (source, target) else none

theorem pairedMergeByte_sound (resolve : AllocId → Nat) (old : Byte Tag)
    (mask value choice : UInt8) (result : Byte Tag × Byte Tag)
    (hresult : pairedMergeByte resolve old mask value choice = some result) :
    result.2 = renameByte resolve result.1 := by
  simp [pairedMergeByte] at hresult
  split at hresult <;> simp_all

def copySnapshot (source destination : List (Byte Tag)) : Option (List (Byte Tag)) :=
  if source.length == destination.length then some source else none

def pairedCopySnapshot (resolve : AllocId → Nat)
    (source destination : List (Byte Tag)) :
    Option ((List (Byte Tag)) × (List (Byte Tag))) := do
  let sourceResult ← copySnapshot source destination
  let targetResult ← copySnapshot (source.map (renameByte resolve))
    (destination.map (renameByte resolve))
  if targetResult = sourceResult.map (List.map (renameByte resolve)) then
    some (sourceResult, targetResult)
  else none

theorem pairedCopySnapshot_sound (resolve : AllocId → Nat)
    (source destination : List (Byte Tag))
    (result : List (Byte Tag) × List (Byte Tag))
    (hresult : pairedCopySnapshot resolve source destination = some result) :
    result.2 = result.1.map (renameByte resolve) := by
  simp [pairedCopySnapshot] at hresult
  split at hresult <;> simp_all

def copyFootprint (source destination : Region) (width : Nat) : Footprint :=
  { accesses := [(.read { source with width := width }),
                 (.write { destination with width := width })] }

def pairedCopyFootprint (source destination : Region) (width : Nat) : Bool :=
  footprintAgrees (copyFootprint source destination width)
    (copyFootprint source destination width)

theorem pairedCopyFootprint_sound (source destination : Region) (width : Nat) :
    pairedCopyFootprint source destination width := by
  simp [pairedCopyFootprint, copyFootprint, footprintAgrees]

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

def pairedMemmoveSnapshot (resolve : AllocId → Nat)
    (source destination : Region) (bytes : List (Byte Tag)) :
    Option (List (Byte Tag) × List (Byte Tag)) := do
  let sourceResult ← memmoveSnapshot source destination bytes
  let targetResult ← memmoveSnapshot source destination (bytes.map (renameByte resolve))
  if targetResult = sourceResult.map (List.map (renameByte resolve)) then
    some (sourceResult, targetResult)
  else none

theorem pairedMemmoveSnapshot_sound (resolve : AllocId → Nat)
    (source destination : Region) (bytes : List (Byte Tag))
    (result : List (Byte Tag) × List (Byte Tag))
    (hresult : pairedMemmoveSnapshot resolve source destination bytes = some result) :
    result.2 = result.1.map (renameByte resolve) := by
  simp [pairedMemmoveSnapshot] at hresult
  split at hresult <;> simp_all

def pairedMemmoveFootprint (source destination : Region) (width : Nat) : Bool :=
  footprintAgrees (copyFootprint source destination width)
    (copyFootprint source destination width)

theorem pairedMemmoveFootprint_sound (source destination : Region) (width : Nat) :
    pairedMemmoveFootprint source destination width := by
  simp [pairedMemmoveFootprint, copyFootprint, footprintAgrees]

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

def pairedReallocMetadata (resolve : AllocId → Nat)
    (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) :
    Option ((ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint)) := do
  let sourceResult ← reallocMetadata old request locations placement
  let targetResult ← reallocMetadata (renameMetadata resolve 0 old) request locations
    (match placement with
    | .address _ => .address (resolve 0)
    | .unaddressable => .unaddressable
    | .fail => .fail)
  if targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedReallocMetadata_footprint
    (resolve : AllocId → Nat) (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations placement =
      some result) :
    result.2.2 = result.1.2 := by
  simp [pairedReallocMetadata] at hresult
  split at hresult <;> simp_all

theorem pairedReallocMetadata_footprint_agrees
    (resolve : AllocId → Nat) (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations placement =
      some result) :
    footprintAgrees result.1.2 result.2.2 := by
  have h := pairedReallocMetadata_footprint resolve old request locations placement result hresult
  rw [h]
  exact footprintAgrees_refl _

theorem pairedReallocMetadata_failure
    (resolve : AllocId → Nat) (old : AllocationMetadata Tag State TypeId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId))
    (result : (ReallocOutcome Tag State TypeId × Footprint) ×
      (ReallocOutcome Tag State TypeId × Footprint))
    (hresult : pairedReallocMetadata resolve old request locations .fail =
      some result) :
    result.1.1 = .failed old ∧
      result.2.1 = .failed (renameMetadata resolve 0 old) ∧
      result.2.2 = result.1.2 := by
  simp [pairedReallocMetadata, reallocMetadata] at hresult
  split at hresult <;> simp_all

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

def pairedReallocZero (resolve : AllocId → Nat) : Bool :=
  reallocZeroGNU17 = reallocZeroGNU17

theorem pairedReallocZero_sound (resolve : AllocId → Nat) :
    pairedReallocZero resolve := by
  simp [pairedReallocZero]

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

theorem zeroTokenEqual_distinct_address
    (left right : AllocationMetadata Tag State TypeId)
    (hleft : isZeroToken left) (hright : isZeroToken right)
    (haddr : left.allocation.address ≠ right.allocation.address) :
    zeroTokenEqual left right = false := by
  simp [zeroTokenEqual, hleft, hright, haddr]

def pairedZeroTokenEqual (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId) : Bool :=
  zeroTokenEqual (renameZeroTokenMetadata resolve left)
    (renameZeroTokenMetadata resolve right) =
    zeroTokenEqual left right

theorem pairedZeroTokenEqual_sound (resolve : AllocId → Nat)
    (left right : AllocationMetadata Tag State TypeId)
    (h : pairedZeroTokenEqual resolve left right) :
    zeroTokenEqual (renameZeroTokenMetadata resolve left)
      (renameZeroTokenMetadata resolve right) = zeroTokenEqual left right := by
  simpa [pairedZeroTokenEqual] using h

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

def pairedFreePointer (resolve : AllocId → Nat)
    (metadata : Option (AllocationMetadata Tag State TypeId)) : Bool :=
  freePointer metadata = freePointer metadata

theorem pairedFreePointer_sound (resolve : AllocId → Nat)
    (metadata : Option (AllocationMetadata Tag State TypeId)) :
    pairedFreePointer resolve metadata := by
  simp [pairedFreePointer]

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

def pairedRepresentationLoadMetadataByte (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice) :
    Option ((Byte Tag × Footprint) × (Byte Tag × Footprint)) := do
  let sourceResult ← representationLoadMetadataByte metadata offset choice
  let targetResult ← representationLoadMetadataByte (renameMetadata resolve id metadata)
    offset choice
  if targetResult.1 = renameByte resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2 then
    some (sourceResult, targetResult)
  else none

theorem pairedRepresentationLoadMetadataByte_corresponds
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedRepresentationLoadMetadataByte resolve id metadata offset choice =
      some result) :
    result.2.1 = renameByte resolve result.1.1 ∧
      result.2.2 = result.1.2 := by
  simp [pairedRepresentationLoadMetadataByte] at hresult
  split at hresult <;> simp_all

def pairedStoreRepresentationLoadMetadataByte
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice) :
    Option ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint))) := do
  let sourceStore ← storeMetadataByte metadata offset byte
  let targetStore ← storeMetadataByte (renameMetadata resolve id metadata)
    offset (renameByte resolve byte)
  let sourceLoad ← representationLoadMetadataByte sourceStore.1 offset choice
  let targetLoad ← representationLoadMetadataByte targetStore.1 offset choice
  if targetStore.1 = renameMetadata resolve id sourceStore.1 &&
      targetStore.2 = sourceStore.2 &&
      targetLoad.1 = renameByte resolve sourceLoad.1 &&
      targetLoad.2 = sourceLoad.2 then
    some ((sourceStore, sourceLoad), (targetStore, targetLoad))
  else none

theorem pairedStoreRepresentationLoadMetadataByte_sound
    (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (byte : Byte Tag) (choice : RepresentationChoice)
    (result : (AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint) ×
      ((AllocationMetadata Tag State TypeId × Footprint) ×
      (Byte Tag × Footprint)))
    (hresult : pairedStoreRepresentationLoadMetadataByte resolve id metadata offset byte
      choice = some result) :
    result.2.1.1 = renameMetadata resolve id result.1.1.1 ∧
      result.2.1.2 = result.1.1.2 ∧
      result.2.2.1 = renameByte resolve result.1.2.1 ∧
      result.2.2.2 = result.1.2.2 := by
  simp [pairedStoreRepresentationLoadMetadataByte] at hresult
  split at hresult <;> simp_all

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

theorem renameMetadata_wellFormed (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId) :
    (renameMetadata resolve id metadata).wellFormed id ↔
      metadata.wellFormed id := by
  simp [AllocationMetadata.wellFormed, renameMetadata,
    bytesWf_renameByte]

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

theorem renameStore_wf_iff (resolve : AllocId → Nat) (store : Store Tag State) :
    WellFormed (renameStore resolve store) ↔ WellFormed store := by
  exact allocationsWf_rename resolve store.allocations

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

def pairedPlacementAllowed (resolve : AllocId → Nat)
    (store : Store Tag State) (base size : Nat) : Bool :=
  placementAllowed store base size =
    placementAllowed (renameStore resolve store) (resolve store.nextId) size

theorem pairedPlacementAllowed_sound (resolve : AllocId → Nat)
    (store : Store Tag State) (base size : Nat)
    (h : pairedPlacementAllowed resolve store base size) :
    placementAllowed store base size =
      placementAllowed (renameStore resolve store) (resolve store.nextId) size := by
  simpa [pairedPlacementAllowed] using h

theorem zeroSizePlacementAllowed (store : Store Tag State) (base : Nat) :
    placementAllowed store base 0 = true := by
  simp [placementAllowed, intervalOverlap]

def alignmentAllowed (base alignment : Nat) : Bool :=
  alignment > 0 && base % alignment == 0

def pairedAlignmentAllowed (resolve : AllocId → Nat)
    (id alignment : Nat) : Bool :=
  alignmentAllowed (resolve id) alignment = alignmentAllowed (resolve id) alignment

theorem pairedAlignmentAllowed_sound (resolve : AllocId → Nat)
    (id alignment : Nat) : pairedAlignmentAllowed resolve id alignment := by
  simp [pairedAlignmentAllowed]

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

def pairedPointerEqual (resolve : AllocId → Nat)
    (left right : Pointer Tag) (choice : EqualityChoice) : Bool :=
  pointerEqual (renamePointer resolve left) (renamePointer resolve right) choice =
    pointerEqual left right choice

theorem pairedPointerEqual_self (resolve : AllocId → Nat)
    (pointer : Pointer Tag) (choice : EqualityChoice) :
    pairedPointerEqual resolve pointer pointer choice := by
  simp [pairedPointerEqual, pointerEqual]

theorem pairedPointerEqual_sound (resolve : AllocId → Nat)
    (left right : Pointer Tag) (choice : EqualityChoice)
    (h : pairedPointerEqual resolve left right choice) :
    pointerEqual (renamePointer resolve left) (renamePointer resolve right) choice =
      pointerEqual left right choice := by
  simpa [pairedPointerEqual] using h

theorem renamePointer_empty_provenance (resolve : AllocId → Nat)
    (address : Nat) :
    renamePointer resolve { provenance := none, address := address } =
      { provenance := none, address := address } := by
  rfl

theorem pointerEqual_empty_provenance_rename (resolve : AllocId → Nat)
    (left right : Pointer Tag) (hleft : left.provenance = none)
    (hright : right.provenance = none) (choice : EqualityChoice) :
    pointerEqual (renamePointer resolve left) (renamePointer resolve right) choice =
      pointerEqual left right choice := by
  cases left
  cases right
  simp_all [renamePointer, pointerEqual]

inductive OffsetFault where
  | outOfBounds
  | alignment
deriving Repr, BEq

structure Exposure where
  exposed : Bool
deriving Repr, BEq

def renameExposure (resolve : AllocId → Nat) (state : Exposure) : Exposure := state

theorem renameExposure_identity (resolve : AllocId → Nat) (state : Exposure) :
    renameExposure resolve state = state := by
  rfl

theorem expose_renameExposure (resolve : AllocId → Nat) (state : Exposure) :
    renameExposure resolve (expose state) = expose (renameExposure resolve state) := by
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
  simp [renameReplayEvents, renameReplayEvent_identity]

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

def renameReplayPlacement (resolve : AllocId → Nat)
    (placement : ReplayPlacement) : ReplayPlacement :=
  { placement with base := resolve placement.allocation }

def renameReplayFixture (resolve : AllocId → Nat)
    (fixture : ReplayFixture) : ReplayFixture :=
  { fixture with
    placements := fixture.placements.map (renameReplayPlacement resolve)
    events := renameReplayEvents resolve fixture.events }

theorem renameReplayFixture_events (resolve : AllocId → Nat)
    (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).events = fixture.events := by
  simp [renameReplayFixture, renameReplayEvents, renameReplayEvent]

theorem renameReplayFixture_ending (resolve : AllocId → Nat)
    (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).ending = fixture.ending := by
  rfl

theorem renameReplayFixture_comp (first second : AllocId → Nat)
    (fixture : ReplayFixture) :
    renameReplayFixture second (renameReplayFixture first fixture) =
      renameReplayFixture second fixture := by
  cases fixture
  simp [renameReplayFixture, renameReplayPlacement, renameReplayEvents,
    renameReplayEvent]

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

def renameLiveRegion (resolve : AllocId → Nat)
    (entry : AllocId × Nat × Nat × Tag) : AllocId × Nat × Nat × Tag :=
  (entry.1, resolve entry.1, resolve entry.1 + (entry.2.2 - entry.2.1), entry.2.3)

def renameRecovery (resolve : AllocId → Nat) : Recovery → Recovery
  | .recovered pointer => .recovered (renamePointer resolve pointer)
  | .empty address => .empty address
  | .ambiguousOnePastAdjacent => .ambiguousOnePastAdjacent
  | .noLiveAllocation => .noLiveAllocation

def pairedRecoverAddress (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag)) : Bool :=
  recoverAddress address live =
    recoverAddress address (live.map (renameLiveRegion resolve))

theorem pairedRecoverAddress_sound (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag))
    (h : pairedRecoverAddress resolve address live) :
    recoverAddress address live =
      recoverAddress address (live.map (renameLiveRegion resolve)) := by
  simpa [pairedRecoverAddress] using h

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

def renameOffsetResult (resolve : AllocId → Nat) :
    Except OffsetFault (Pointer Tag) → Except OffsetFault (Pointer Tag)
  | .error fault => .error fault
  | .ok pointer => .ok (renamePointer resolve pointer)

def pairedOffsetPointer (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat) :
    Bool :=
  let source := offsetPointer pointer elementSize delta bound
  let target := offsetPointer (renamePointer resolve pointer) elementSize delta bound
  target = renameOffsetResult resolve source

theorem pairedOffsetPointer_sound (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat)
    (h : pairedOffsetPointer resolve pointer elementSize delta bound) :
    offsetPointer (renamePointer resolve pointer) elementSize delta bound =
      renameOffsetResult resolve (offsetPointer pointer elementSize delta bound) := by
  simpa [pairedOffsetPointer] using h

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

def pairedAllocateAligned (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment : Nat) : Bool :=
  let source := allocateAligned store request placement alignment
  let target := allocateAligned (renameStore resolve store) request
    (renamedPlacement resolve store.nextId placement) alignment
  target = source.map (fun result => (renameStore resolve result.1, result.2))

theorem pairedAllocateAligned_sound (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment : Nat)
    (h : pairedAllocateAligned resolve store request placement alignment) :
    allocateAligned (renameStore resolve store) request
      (renamedPlacement resolve store.nextId placement) alignment =
      (allocateAligned store request placement alignment).map
        (fun result => (renameStore resolve result.1, result.2)) := by
  simpa [pairedAllocateAligned] using h

inductive PlacementFault where
  | exhausted
  | overlap
  | misaligned
deriving Repr, BEq

def placementWithin (base size limit : Nat) : Bool :=
  base ≤ limit && size ≤ limit - base

def pairedPlacementWithin (resolve : AllocId → Nat)
    (id size limit : Nat) (base : Nat) : Bool :=
  placementWithin base size limit = placementWithin (resolve id) size limit

theorem pairedPlacementWithin_sound (resolve : AllocId → Nat)
    (id size limit base : Nat)
    (h : pairedPlacementWithin resolve id size limit base) :
    placementWithin base size limit = placementWithin (resolve id) size limit := by
  simpa [pairedPlacementWithin] using h

theorem placementWithin_zero (base limit : Nat) :
    placementWithin base 0 limit = (base ≤ limit) := by
  simp [placementWithin]

structure PlacementAgreement where
  left right : AllocId → Option Nat
  exposed : AllocId → Bool

def PlacementAgreement.agrees (agreement : PlacementAgreement) : Prop :=
  ∀ allocation, agreement.exposed allocation →
    agreement.left allocation = agreement.right allocation

theorem PlacementAgreement.agrees_iff (agreement : PlacementAgreement) :
    agreement.agrees ↔
      ∀ allocation, agreement.exposed allocation = false ∨
        agreement.left allocation = agreement.right allocation := by
  constructor
  · intro h allocation
    by_cases hexposed : agreement.exposed allocation
    · right
      exact h allocation hexposed
    · left
      exact Bool.eq_false_of_not_eq_true hexposed
  · intro h allocation hexposed
    exact (h allocation).resolve_left (Bool.eq_true_of_decide hexposed)

def zeroTokenPlacementAgreement (left right : AllocationMetadata Tag State TypeId) :
    PlacementAgreement :=
  { left := fun _ => left.allocation.address
    right := fun _ => right.allocation.address
    exposed := fun _ => false }

theorem zeroTokenPlacementAgreement_agrees
    (left right : AllocationMetadata Tag State TypeId) :
    (zeroTokenPlacementAgreement left right).agrees := by
  intro allocation hexposed
  simp [zeroTokenPlacementAgreement] at hexposed

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

def exposedPlacementAgreement (resolve : AllocId → Nat)
    (store : Store Tag State) (exposed : AllocId → Bool) : PlacementAgreement :=
  { left := placementOf store
    right := fun id => (placementOf store id).map (fun _ => resolve id)
    exposed := exposed }

theorem exposedPlacementAgreement_agrees
    (resolve : AllocId → Nat) (store : Store Tag State)
    (exposed : AllocId → Bool)
    (hresolve : ∀ id, exposed id = true →
      (placementOf store id).map (fun _ => resolve id) = placementOf store id) :
    (exposedPlacementAgreement resolve store exposed).agrees := by
  intro allocation hexposed
  exact hresolve allocation hexposed

theorem exposedPlacementAgreement_zeroToken
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id : AllocId) (hexposed : (fun _ => false) id = true) :
    (placementOf store id).map (fun _ => resolve id) = placementOf store id := by
  simp at hexposed

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

theorem footprintAgrees_rename (resolve : AllocId → Nat) (footprint : Footprint) :
    footprintAgrees (renameFootprint resolve footprint) footprint := by
  simp [renameFootprint, renameRegion, footprintAgrees]

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

def renameBoundedResult (resolve : AllocId → Nat) :
    Except PlacementFault (Store Tag State × Footprint) →
      Except PlacementFault (Store Tag State × Footprint)
  | .error fault => .error fault
  | .ok (store, footprint) =>
      .ok (renameStore resolve store, footprint)

def pairedAllocateBounded (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment limit : Nat) : Bool :=
  let source := allocateBounded store request placement alignment limit
  let target := allocateBounded (renameStore resolve store) request
    (renamedPlacement resolve store.nextId placement) alignment limit
  target = renameBoundedResult resolve source

theorem pairedAllocateBounded_sound (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment limit : Nat)
    (h : pairedAllocateBounded resolve store request placement alignment limit) :
    allocateBounded (renameStore resolve store) request
      (renamedPlacement resolve store.nextId placement) alignment limit =
      renameBoundedResult resolve
        (allocateBounded store request placement alignment limit) := by
  simpa [pairedAllocateBounded] using h

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

def pairedAllocateMetadata (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement) : Bool :=
  let source := allocateMetadata request locations placement
  let target := allocateMetadata request locations
    (renamedPlacement resolve id placement)
  target = source.map (fun result =>
    (renameMetadata resolve id result.1, result.2))

theorem pairedAllocateMetadata_sound (resolve : AllocId → Nat) (id : AllocId)
    (request : AllocationRequest Tag State)
    (locations : List (LocationState TypeId)) (placement : Placement)
    (h : pairedAllocateMetadata resolve id request locations placement) :
    allocateMetadata request locations (renamedPlacement resolve id placement) =
      (allocateMetadata request locations placement).map (fun result =>
        (renameMetadata resolve id result.1, result.2)) := by
  simpa [pairedAllocateMetadata] using h

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

theorem storeByte_lookup_correspondence
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag)
    (result : (Store Tag State × Footprint) × (Store Tag State × Footprint))
    (hresult : pairedStoreByte resolve store id offset byte = some result) :
    result.2.1 = renameStore resolve result.1.1 := by
  exact (pairedStoreByte_corresponds resolve store id offset byte result hresult).2.1

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

theorem loadByte_lookup_correspondence
    (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat)
    (result : (Byte Tag × Footprint) × (Byte Tag × Footprint))
    (hresult : pairedLoadByte resolve store id offset = some result) :
    result.2.1 = renameByte resolve result.1.1 := by
  exact (pairedLoadByte_corresponds resolve store id offset result hresult).2.2.1

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

def pairedLifetimeLookup (resolve : AllocId → Nat)
    (store : Store Tag State) (id : AllocId) : Bool :=
  match endLifetime store id, endLifetime (renameStore resolve store) id with
  | some (source, _), some (target, _) =>
      target = renameStore resolve source &&
      (lookup target id).map (renameAllocationValue resolve id) = lookup source id
  | _, _ => false

theorem pairedLifetimeLookup_sound (resolve : AllocId → Nat)
    (store : Store Tag State) (id : AllocId)
    (h : pairedLifetimeLookup resolve store id = true) :
    ∃ source target sourceFootprint targetFootprint,
      endLifetime store id = some (source, sourceFootprint) ∧
      endLifetime (renameStore resolve store) id = some (target, targetFootprint) ∧
      target = renameStore resolve source := by
  simp [pairedLifetimeLookup] at h
  split at h <;> simp_all

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
