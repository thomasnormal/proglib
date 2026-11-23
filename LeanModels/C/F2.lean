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

inductive Value (Tag : Type) where
  | scalar (bytes : List UInt8)
  | pointer (pointer : Pointer Tag)
  | aggregate (members : List (Value Tag))
deriving Repr

def encodePointer (pointer : Pointer Tag) : List (Byte Tag) :=
  (List.range 8).map (fun fragment =>
    .value (UInt8.ofNat ((pointer.address / (256 ^ fragment)) % 256))
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

inductive ReallocZeroOutcome where
  | freedNull
  | refusedUndefined
deriving Repr, BEq

def reallocZeroGNU17 : ReallocZeroOutcome := .freedNull

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
  | .address base | .unaddressable =>
      let id := store.nextId
      let allocation : Allocation Tag State :=
        { live := true
          address := match placement with | .address _ => some base | .unaddressable => none
          bytes := request.bytes
          state := request.state }
      some ({ allocations := store.allocations ++ [(id, allocation)],
              nextId := id + 1 },
            footprint .metadata { allocation := id, offset := 0,
              width := request.bytes.length })

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

def loadByte (store : Store Tag State) (id offset : Nat) :
    Option (Byte Tag × Footprint) := do
  let allocation ← lookup store id
  if !allocation.live then none
  else
    let byte ← allocation.bytes[offset]?
    some (byte, footprint .read { allocation := id, offset := offset, width := 1 })

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
