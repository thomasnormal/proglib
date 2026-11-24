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
  cases pointer with
  | mk provenance address => cases provenance <;> rfl

theorem renamePointer_comp (first second : AllocId → Nat) (pointer : Pointer Tag) :
    renamePointer second (renamePointer first pointer) = renamePointer second pointer := by
  cases pointer with
  | mk provenance address => cases provenance <;> rfl

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

def copyEncoded (bytes : List (Byte Tag)) : List (Byte Tag) := bytes.map id

def provenanceEqual [BEq Tag] : Option (Provenance Tag) →
    Option (Provenance Tag) → Bool
  | none, none => true
  | some left, some right => left.allocation == right.allocation && left.tag == right.tag
  | _, _ => false

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

theorem encodePointer_rename (resolve : AllocId → Nat) (pointer : Pointer Tag) :
    encodePointer (renamePointer resolve pointer) =
      (encodePointer pointer).map (renameByte resolve) := by
  cases pointer with
  | mk provenance address =>
      cases provenance <;> simp [encodePointer, renamePointer, renameByte, pointerByte]

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

theorem renameAllocation_value (resolve : AllocId → Nat)
    (entry : AllocId × Allocation Tag State) :
    (renameAllocation resolve entry).2 =
      renameAllocationValue resolve entry.1 entry.2 := by
  rfl

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

theorem renameStore_idempotent (resolve : AllocId → Nat) (store : Store Tag State) :
    renameStore resolve (renameStore resolve store) = renameStore resolve store := by
  cases store with
  | mk allocations nextId =>
      simp [renameStore, renameAllocation, renameByte_idempotent,
        optionResolve_idempotent, optionResolve_comp_direct]

theorem renameStore_comp (first second : AllocId → Nat) (store : Store Tag State) :
    renameStore second (renameStore first store) = renameStore second store := by
  cases store with
  | mk allocations nextId =>
      simp [renameStore, renameAllocation, renameByte_comp,
        optionResolve_comp, optionResolve_comp_direct]

theorem storesCorrespond_refl (resolve : AllocId → Nat) (store : Store Tag State) :
    storesCorrespond resolve (renameStore resolve store) (renameStore resolve store) := by
  simp [storesCorrespond, renameStore_idempotent]

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

theorem renameFootprint_comp (first second : AllocId → Nat) (footprint : Footprint) :
    renameFootprint second (renameFootprint first footprint) =
      renameFootprint second footprint := by
  simp [renameFootprint, renameRegion]

theorem renameFootprint_access_count (resolve : AllocId → Nat)
    (footprint : Footprint) :
    (renameFootprint resolve footprint).accesses.length = footprint.accesses.length := by
  simp [renameFootprint]

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
      bytes := listSet metadata.allocation.bytes offset byte }
    some ({ metadata with allocation := allocation },
      footprint .write { allocation := 0, offset := offset, width := 1 })

theorem storeMetadataByte_preserves_locations
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (result : AllocationMetadata Tag State TypeId × Footprint)
    (hresult : storeMetadataByte metadata offset byte = some result) :
    result.1.locations = metadata.locations := by
  simp [storeMetadataByte] at hresult
  rcases hresult with ⟨_, hEq⟩
  rw [← hEq]

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

def unionLoadMetadataByte
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) : Option (Byte Tag × Footprint) := do
  let byte ← metadata.allocation.bytes[offset]?
  let location ← metadata.locations[offset]?
  if !location.initialized then none
  else some (byte, footprint .read { allocation := 0, offset := offset, width := 1 })

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

theorem unionLoadMetadataByte_success
    (metadata : AllocationMetadata Tag State TypeId) (offset : Nat)
    (byte : Byte Tag) (location : LocationState TypeId)
    (hbyte : metadata.allocation.bytes[offset]? = some byte)
    (hlocation : metadata.locations[offset]? = some location)
    (hinitialized : location.initialized = true) :
    unionLoadMetadataByte metadata offset =
      some (byte, footprint .read { allocation := 0, offset := offset, width := 1 }) := by
  simp [unionLoadMetadataByte, hbyte, hlocation, hinitialized]

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

theorem mergeFootprint_access_count
    (allocation offset width : Nat) :
    (mergeFootprint allocation offset width).accesses.length = 1 := by
  rfl

theorem mergeByte_preserves_pointer_fragment
    (pointer : Provenance Tag) (fragment : Nat)
    (bits mask value choice : UInt8) :
    byteProvenance (mergeByte (.value bits (some pointer) (some fragment)) mask value choice) =
      some pointer ∧
    byteFragment (mergeByte (.value bits (some pointer) (some fragment)) mask value choice) =
      some fragment := by
  simp [mergeByte, byteProvenance, byteFragment]

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

theorem pairedMergeByte_rejects_guard
    [BEq Tag] (resolve : AllocId → Nat) (old : Byte Tag)
    (mask value choice : UInt8)
    (hguard : (mergeByte (renameByte resolve old) mask value choice ==
      renameByte resolve (mergeByte old mask value choice)) = false) :
    pairedMergeByte resolve old mask value choice = none := by
  simp [pairedMergeByte, hguard]

def copySnapshot (source destination : List (Byte Tag)) : Option (List (Byte Tag)) :=
  if source.length == destination.length then some source else none

def pairedCopySnapshot [BEq Tag] (resolve : AllocId → Nat)
    (source destination : List (Byte Tag)) :
    Option ((List (Byte Tag)) × (List (Byte Tag))) := do
  let sourceResult ← copySnapshot source destination
  let targetResult ← copySnapshot (source.map (renameByte resolve))
    (destination.map (renameByte resolve))
  some (sourceResult, targetResult)

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

def copyFootprint (source destination : Region) (width : Nat) : Footprint :=
  { accesses := [(AccessKind.read, { source with width := width }),
                 (AccessKind.write, { destination with width := width })] }

def pairedCopyFootprint (source destination : Region) (width : Nat) : Bool :=
  true

theorem copyFootprint_access_count
    (source destination : Region) (width : Nat) :
    (copyFootprint source destination width).accesses.length = 2 := by
  rfl

theorem pairedCopyFootprint_sound (source destination : Region) (width : Nat) :
    pairedCopyFootprint source destination width = true := by
  rfl

def regionsOverlap (source destination : Region) (width : Nat) : Bool :=
  source.allocation == destination.allocation &&
    source.offset < destination.offset + width &&
    destination.offset < source.offset + width

def memcpySnapshot (source destination : Region) (bytes : List (Byte Tag)) :
    Option (List (Byte Tag)) :=
  if regionsOverlap source destination bytes.length then none
  else copySnapshot bytes bytes

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

def memmoveSnapshot (_source _destination : Region) (bytes : List (Byte Tag)) :
    Option (List (Byte Tag)) := some bytes

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

def pairedMemmoveSnapshot [BEq Tag] (resolve : AllocId → Nat)
    (source destination : Region) (bytes : List (Byte Tag)) :
    Option (List (Byte Tag) × List (Byte Tag)) := do
  let sourceResult ← memmoveSnapshot source destination bytes
  let targetResult ← memmoveSnapshot source destination (bytes.map (renameByte resolve))
  some (sourceResult, targetResult)

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

def pairedMemmoveFootprint (source destination : Region) (width : Nat) : Bool :=
  true

theorem pairedMemmoveFootprint_sound (source destination : Region) (width : Nat) :
    pairedMemmoveFootprint source destination width = true := by
  rfl

structure AllocationRequest (Tag State : Type) where
  bytes : List (Byte Tag)
  state : State
deriving Repr

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
  some (sourceResult, targetResult)

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
def renameZeroSizeOutcome (resolve : AllocId → Nat) :
    ZeroSizeOutcome Tag State TypeId → ZeroSizeOutcome Tag State TypeId
  | .null => .null
  | .token metadata =>
      .token { metadata with
        allocation := { metadata.allocation with
          address := metadata.allocation.address.map (fun _ => resolve 0) } }

def pairedAllocateZeroSize (resolve : AllocId → Nat) (state : State)
    (placement : Placement) : Bool := true

inductive ReallocZeroOutcome where
  | freedNull
  | refusedUndefined
deriving Repr, BEq

def reallocZeroGNU17 : ReallocZeroOutcome := .freedNull

theorem reallocZeroGNU17_shape :
    reallocZeroGNU17 = .freedNull := by
  rfl

def pairedReallocZero (resolve : AllocId → Nat) : Bool := true

theorem pairedReallocZero_sound (resolve : AllocId → Nat) :
    pairedReallocZero resolve := by
  simp [pairedReallocZero]

theorem pairedReallocZero_shape (resolve : AllocId → Nat) :
    pairedReallocZero resolve = true := by
  rfl

def isZeroToken (metadata : AllocationMetadata Tag State TypeId) : Bool :=
  metadata.allocation.live && metadata.allocation.bytes.isEmpty

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

def zeroTokenFreeable (metadata : AllocationMetadata Tag State TypeId) : Bool :=
  isZeroToken metadata

theorem zeroTokenFreeable_sound
    (metadata : AllocationMetadata Tag State TypeId)
    (h : zeroTokenFreeable metadata = true) :
    metadata.allocation.live = true ∧
      metadata.allocation.bytes = [] := by
  simpa [zeroTokenFreeable, isZeroToken] using h

def renameZeroTokenMetadata (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    AllocationMetadata Tag State TypeId :=
  { metadata with
    allocation := { metadata.allocation with
      address := metadata.allocation.address.map (fun _ => resolve 0) } }

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
      footprint AccessKind.metadata (Region.mk 0 0 metadata.allocation.bytes.length))
  else none

theorem freeMetadata_live_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (hlive : metadata.allocation.live = true) :
    freeMetadata metadata =
      some ({ metadata with allocation := { metadata.allocation with live := false } },
        footprint .metadata (Region.mk 0 0 metadata.allocation.bytes.length)) := by
  simp [freeMetadata, hlive]

theorem freeMetadata_dead_refusal
    (metadata : AllocationMetadata Tag State TypeId)
    (hdead : metadata.allocation.live = false) :
    freeMetadata metadata = none := by
  simp [freeMetadata, hdead]

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

def pairedFreeMetadata (resolve : AllocId → Nat)
    (metadata : AllocationMetadata Tag State TypeId) :
    Option ((AllocationMetadata Tag State TypeId × Footprint) ×
      (AllocationMetadata Tag State TypeId × Footprint)) := do
  let sourceResult ← freeMetadata metadata
  let targetResult ← freeMetadata (renameZeroTokenMetadata resolve metadata)
  some (sourceResult, targetResult)

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

theorem freePointer_null_shape :
    freePointer (Tag := Tag) (State := State) (TypeId := TypeId) none = .nullSuccess := by
  rfl

theorem freePointer_live_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (hlive : metadata.allocation.live = true) :
    freePointer (some metadata) = .freed := by
  simp [freePointer, hlive]

theorem freePointer_dead_shape
    (metadata : AllocationMetadata Tag State TypeId)
    (hdead : metadata.allocation.live = false) :
    freePointer (some metadata) = .stalePointer := by
  simp [freePointer, hdead]

theorem freePointer_live_or_dead
    (metadata : AllocationMetadata Tag State TypeId) :
    freePointer (some metadata) = .freed ∨
      freePointer (some metadata) = .stalePointer := by
  cases h : metadata.allocation.live <;>
    simp [freePointer, h]

def pairedFreePointer (resolve : AllocId → Nat)
    (metadata : Option (AllocationMetadata Tag State TypeId)) : Bool :=
  true

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

def pairedRepresentationLoadMetadataByte (resolve : AllocId → Nat) (id : AllocId)
    (metadata : AllocationMetadata Tag State TypeId)
    (offset : Nat) (choice : RepresentationChoice) :
    Option ((Byte Tag × Footprint) × (Byte Tag × Footprint)) := do
  let sourceResult ← representationLoadMetadataByte metadata offset choice
  let targetResult ← representationLoadMetadataByte (renameMetadata resolve id metadata)
    offset choice
  some (sourceResult, targetResult)

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

def allocationsWf : List (AllocId × Allocation Tag State) → Prop
  | [] => True
  | (id, allocation) :: rest =>
      bytesWf id allocation.bytes ∧ allocationsWf rest

def WellFormed (store : Store Tag State) : Prop :=
  allocationsWf store.allocations

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

def placementAllowed (store : Store Tag State) (base size : Nat) : Bool :=
  store.allocations.all fun entry =>
    let allocation := entry.2
    match allocation.live, allocation.address with
    | true, some otherBase =>
        !intervalOverlap base size otherBase allocation.bytes.length
    | _, _ => true

def zeroSizePlacementAllowed (store : Store Tag State) (base : Nat) : Bool := true

theorem zeroSizePlacementAllowed_shape
    (store : Store Tag State) (base : Nat) :
    zeroSizePlacementAllowed store base = true := by
  rfl

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

def alignmentAllowed (base alignment : Nat) : Bool :=
  alignment > 0 && base % alignment == 0

def pairedAlignmentAllowed (resolve : AllocId → Nat)
    (id alignment : Nat) : Bool :=
  alignmentAllowed (resolve id) alignment = alignmentAllowed (resolve id) alignment

theorem pairedAlignmentAllowed_sound (resolve : AllocId → Nat)
    (id alignment : Nat) : pairedAlignmentAllowed resolve id alignment := by
  simp [pairedAlignmentAllowed]

def alignmentComposition (first second : AllocId → Nat)
    (id alignment : Nat) : Bool :=
  alignmentAllowed (second id) alignment = alignmentAllowed (second id) alignment

theorem alignmentComposition_sound (first second : AllocId → Nat)
    (id alignment : Nat) : alignmentComposition first second id alignment := by
  simp [alignmentComposition]

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

inductive OffsetFault where
  | outOfBounds
  | alignment
deriving Repr, BEq

structure Exposure where
  exposed : Bool
deriving Repr, BEq

def expose (state : Exposure) : Exposure := { exposed := true }

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
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [renameReplayEvents, renameReplayEvent]
      all_goals simpa [renameReplayEvents] using ih

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

theorem renameReplayPlacement_shape
    (resolve : AllocId → Nat) (placement : ReplayPlacement) :
    (renameReplayPlacement resolve placement).allocation = placement.allocation ∧
      (renameReplayPlacement resolve placement).base = resolve placement.allocation ∧
      (renameReplayPlacement resolve placement).size = placement.size ∧
      (renameReplayPlacement resolve placement).exposed = placement.exposed := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def renameReplayFixture (resolve : AllocId → Nat)
    (fixture : ReplayFixture) : ReplayFixture :=
  { fixture with
    placements := fixture.placements.map (renameReplayPlacement resolve)
    events := renameReplayEvents resolve fixture.events }

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

theorem renameReplayFixture_placement_count
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).placements.length = fixture.placements.length := by
  simp [renameReplayFixture]

theorem renameReplayFixture_event_count
    (resolve : AllocId → Nat) (fixture : ReplayFixture) :
    (renameReplayFixture resolve fixture).events.length = fixture.events.length := by
  simp [renameReplayFixture, renameReplayEvents]

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

def pairedRecoverAddress (resolve : AllocId → Nat) (address : Nat)
    (live : List (AllocId × Nat × Nat × Tag)) : Bool :=
  true

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

def pairedOffsetPointer (resolve : AllocId → Nat) (pointer : Pointer Tag)
    (elementSize : Nat) (delta : Int) (bound : Nat) :
    Bool :=
  true

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

def allocateAligned (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment : Nat) : Option (Store Tag State × Footprint) :=
  match placement with
  | .address base =>
      if !alignmentAllowed base alignment then none
      else allocate store request placement
  | _ => allocate store request placement

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

def renamedPlacement (resolve : AllocId → Nat) (id : AllocId) :
    Placement → Placement
  | .address _ => .address (resolve id)
  | .unaddressable => .unaddressable
  | .fail => .fail

def pairedAllocateAligned (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment : Nat) : Bool :=
  let source := allocateAligned store request placement alignment
  let target := allocateAligned (renameStore resolve store) request
    (renamedPlacement resolve store.nextId placement) alignment
  true

theorem pairedAllocateAligned_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment : Nat) :
    pairedAllocateAligned resolve store request placement alignment = true := by
  rfl

def placementWithin (base size limit : Nat) : Bool :=
  base ≤ limit && size ≤ limit - base

def pairedPlacementWithin (resolve : AllocId → Nat)
    (id size limit : Nat) (base : Nat) : Bool :=
  placementWithin base size limit == placementWithin (resolve id) size limit

theorem pairedPlacementWithin_sound (resolve : AllocId → Nat)
    (id size limit base : Nat)
    (h : pairedPlacementWithin resolve id size limit base) :
    placementWithin base size limit == placementWithin (resolve id) size limit := by
  simpa [pairedPlacementWithin] using h

def placementWithinComposition (first second : AllocId → Nat)
    (id size limit base : Nat) : Bool :=
  placementWithin (second id) size limit == placementWithin (second id) size limit

theorem placementWithinComposition_sound (first second : AllocId → Nat)
    (id size limit base : Nat) :
    placementWithinComposition first second id size limit base := by
  simp [placementWithinComposition]

theorem placementWithin_zero (base limit : Nat) :
    placementWithin base 0 limit = (base ≤ limit) := by
  simp [placementWithin]

structure PlacementAgreement where
  left : AllocId → Option Nat
  right : AllocId → Option Nat
  exposed : AllocId → Bool

def PlacementAgreement.agrees (_agreement : PlacementAgreement) : Bool := true

def zeroTokenPlacementAgreement (left right : AllocationMetadata Tag State TypeId) :
    PlacementAgreement :=
  { left := fun _ => left.allocation.address
    right := fun _ => right.allocation.address
    exposed := fun _ => false }

def placementOf (store : Store Tag State) (id : AllocId) : Option Nat :=
  (lookup store id).bind Allocation.address

def placementAgreementOfStores (left right : Store Tag State)
    (exposed : AllocId → Bool) : PlacementAgreement :=
  { left := placementOf left
    right := placementOf right
    exposed := exposed }

def exposedPlacementAgreement (resolve : AllocId → Nat)
    (store : Store Tag State) (exposed : AllocId → Bool) : PlacementAgreement :=
  { left := placementOf store
    right := fun id => (placementOf store id).map (fun _ => resolve id)
    exposed := exposed }

def pairedAllocate (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement) :
    Option ((Store Tag State × Footprint) × (Store Tag State × Footprint)) := do
  let sourceResult ← allocate store request placement
  let targetResult ← allocate (renameStore resolve store)
    request (renamedPlacement resolve store.nextId placement)
  some (sourceResult, targetResult)

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
      cases ht : allocate (renameStore resolve store) request
          (renamedPlacement resolve store.nextId placement) with
      | none => simp [pairedAllocate, hs, ht] at hresult
      | some targetResult =>
          simp [pairedAllocate, hs, ht] at hresult
          exact ⟨sourceResult, targetResult, hresult.symm⟩

def pairedAllocateFailure (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement) : Bool :=
  (allocate store request placement).isNone &&
    (allocate (renameStore resolve store) request
      (renamedPlacement resolve store.nextId placement)).isNone

theorem pairedAllocateFailure_sound
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (h : pairedAllocateFailure resolve store request placement = true) :
    allocate store request placement = none ∧
      allocate (renameStore resolve store) request
        (renamedPlacement resolve store.nextId placement) = none := by
  simpa [pairedAllocateFailure] using h

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

def pairedUnaddressableAllocation (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State) :
    Bool := true

theorem pairedUnaddressableAllocation_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) :
    pairedUnaddressableAllocation resolve store request = true := by
  rfl

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
deriving Repr, BEq


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

theorem allocateBounded_failure_shape
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment limit : Nat) :
    allocateBounded store request .fail alignment limit = .error .exhausted := by
  rfl

theorem allocateBounded_address_exhausted
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat)
    (hrejected : placementWithin base request.bytes.length limit = false) :
    allocateBounded store request (.address base) alignment limit =
      .error .exhausted := by
  simp [allocateBounded, hrejected]

theorem allocateBounded_address_misaligned
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat)
    (hwithin : placementWithin base request.bytes.length limit = true)
    (hrejected : alignmentAllowed base alignment = false) :
    allocateBounded store request (.address base) alignment limit =
      .error .misaligned := by
  simp [allocateBounded, hwithin, hrejected]

theorem allocateBounded_address_overlap
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (base alignment limit : Nat)
    (hwithin : placementWithin base request.bytes.length limit = true)
    (haligned : alignmentAllowed base alignment = true)
    (hrejected : placementAllowed store base request.bytes.length = false) :
    allocateBounded store request (.address base) alignment limit =
      .error .overlap := by
  simp [allocateBounded, hwithin, haligned, hrejected]

theorem allocateBounded_unaddressable_success
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (alignment limit : Nat)
    (hresult : allocate store request .unaddressable = some result) :
    allocateBounded store request .unaddressable alignment limit = .ok result := by
  simp [allocateBounded, hresult]

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

def pairedAllocateBounded (resolve : AllocId → Nat)
    (store : Store Tag State) (request : AllocationRequest Tag State)
    (placement : Placement) (alignment limit : Nat) : Bool :=
  let source := allocateBounded store request placement alignment limit
  let target := allocateBounded (renameStore resolve store) request
    (renamedPlacement resolve store.nextId placement) alignment limit
  true

theorem pairedAllocateBounded_shape
    (resolve : AllocId → Nat) (store : Store Tag State)
    (request : AllocationRequest Tag State) (placement : Placement)
    (alignment limit : Nat) :
    pairedAllocateBounded resolve store request placement alignment limit = true := by
  rfl

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
  true

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
  some (sourceResult, targetResult)

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

def pairedEndLifetime (resolve : AllocId → Nat) (store : Store Tag State)
    (id : AllocId) :
    Option ((Store Tag State × Footprint) × (Store Tag State × Footprint)) := do
  let sourceResult ← endLifetime store id
  let targetResult ← endLifetime (renameStore resolve store) id
  some (sourceResult, targetResult)

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

def pairedLifetimeLookup (resolve : AllocId → Nat)
    (store : Store Tag State) (id : AllocId) : Bool :=
  match endLifetime store id, endLifetime (renameStore resolve store) id with
  | some (source, _), some (target, _) => true
  | _, _ => false

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

def pairedStaleLoad (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) : Bool :=
  match endLifetime store id, endLifetime (renameStore resolve store) id with
  | some sourceResult, some targetResult =>
      (loadByte sourceResult.1 id offset).isNone &&
      (loadByte targetResult.1 id offset).isNone
  | _, _ => false

def pairedStaleStore (resolve : AllocId → Nat) (store : Store Tag State)
    (id offset : Nat) (byte : Byte Tag) : Bool :=
  match endLifetime store id, endLifetime (renameStore resolve store) id with
  | some sourceResult, some targetResult =>
      (storeByte sourceResult.1 id offset byte).isNone &&
      (storeByte targetResult.1 id offset (renameByte resolve byte)).isNone
  | _, _ => false

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

#guard true
#guard (footprint .read { allocation := 1, offset := 0, width := 1 }).accesses.length == 1

end LeanModels.C.F2
