import LeanModels.C.F2

namespace LeanModels.C.F2Tests
open LeanModels.C.F2

abbrev TestByte := Byte Unit
abbrev TestStore := Store Unit Unit

def empty : TestStore := { allocations := [], nextId := 0 }
def oneByte : TestByte := .value 65 none (some 0)
def one : TestStore :=
  { allocations := [(0, { live := true, address := some 32,
                           bytes := [oneByte], state := () })]
    nextId := 1 }
def dead : TestStore :=
  { allocations := [(0, { live := false, address := some 32,
                           bytes := [oneByte], state := () })]
    nextId := 1 }
def resolve : AllocId → Nat := fun id => if id == 0 then 100 else 200
def fragmentByte : TestByte := .value 7 (some { allocation := 3, tag := () }) (some 4)
def location : LocationState String := { effectiveType := .typed "int", initialized := true }
def metadata : AllocationMetadata Unit Unit String :=
  { allocation := { live := true, address := some 32, bytes := [oneByte], state := () }
    locations := [location] }
def paddingMetadata : AllocationMetadata Unit Unit String :=
  { metadata with locations := [{ effectiveType := .padding, initialized := false }] }
def unionMetadata : AllocationMetadata Unit Unit String :=
  { metadata with locations := [{ effectiveType := .untyped, initialized := true }] }

def pointer : Pointer Unit := { provenance := some { allocation := 3, tag := () }, address := 16 }

#guard pointerEqual pointer pointer .unequal == false

#guard placementAllowed one 8 1
#guard !placementAllowed one 32 1
#guard (allocate one { bytes := [Byte.uninitialized], state := () } (.address 32)).isNone
#guard alignmentAllowed 16 8
#guard !alignmentAllowed 18 8
#guard pairedAlignmentAllowed resolve 0 8
#guard pairedPlacementAllowed resolve one 128 0
#guard (allocateAligned empty { bytes := [oneByte], state := () } (.address 16) 8).isSome
#guard (allocateAligned empty { bytes := [oneByte], state := () } (.address 18) 8).isNone
#guard pairedAllocateAligned resolve empty { bytes := [oneByte], state := () } (.address 16) 8
#guard placementWithin 8 4 16
#guard !placementWithin 14 4 16
#guard pairedPlacementWithin resolve 0 4 16 100
#guard pairedAllocateBounded resolve empty { bytes := [oneByte], state := () } (.address 8) 8 16
#guard match allocateBounded empty { bytes := [oneByte], state := () } (.address 16) 1 16 with
  | .error .exhausted => true
  | _ => false
#guard match allocateBounded empty { bytes := [oneByte], state := () } (.address 9) 8 16 with
  | .error .misaligned => true
  | _ => false
#guard match allocateBounded one { bytes := [oneByte], state := () } (.address 32) 1 64 with
  | .error .overlap => true
  | _ => false
#guard (PlacementAgreement.mk (fun _ => some 8) (fun _ => some 8) (fun _ => true)).agrees
#guard (zeroTokenPlacementAgreement metadata metadata).agrees
#guard (allocate empty { bytes := [.uninitialized], state := () } (.address 32)).isSome
#guard (allocate empty { bytes := [.uninitialized], state := () } .unaddressable).isSome
#guard (allocate empty { bytes := [.uninitialized], state := () } .fail).isNone
#guard (pairedAllocate resolve one { bytes := [.uninitialized], state := () } (.address 100)).isSome
#guard pairedAllocateFailure resolve one { bytes := [.uninitialized], state := () } .fail
#guard pairedUnaddressableAllocation resolve empty { bytes := [.uninitialized], state := () }
#guard (allocateMetadata { bytes := [oneByte], state := () } [location] (.address 8)).isSome
#guard (allocateMetadata { bytes := [oneByte], state := () } [location] (.address 8)) ==
  some ({ allocation := { live := true, address := some 8, bytes := [oneByte], state := () },
          locations := [location] },
        footprint .metadata { allocation := 0, offset := 0, width := 1 })
#guard (allocateMetadata { bytes := [oneByte], state := () } ([] : List (LocationState String)) (.address 8)).isNone
#guard (allocateMetadata { bytes := [oneByte], state := () } [location] .fail).isNone
#guard pairedAllocateMetadata resolve 0 { bytes := [oneByte], state := () } [location] (.address 8)
#guard (storeMetadataByte metadata 0 (.value 66 none (some 0))).isSome
#guard (typedStoreMetadataByte metadata 0 "long" oneByte).isSome
#guard match typedStoreMetadataByte metadata 0 "long" oneByte with
  | some (stored, resultFootprint) =>
      stored.locations[0]? == some { effectiveType := .typed "long", initialized := true } &&
        resultFootprint == footprint .write { allocation := 0, offset := 0, width := 1 }
  | none => false
#guard (pairedTypedStoreMetadataByte resolve 0 metadata 0 "long" fragmentByte).isSome
#guard (typedLoadMetadataByte ((typedStoreMetadataByte metadata 0 "long" oneByte).getD (metadata, { accesses := [] })).1 0 "long").isSome
#guard match typedLoadMetadataByte metadata 0 "int" with
  | some (value, resultFootprint) =>
      value == oneByte && resultFootprint == footprint .read { allocation := 0, offset := 0, width := 1 }
  | none => false
#guard (typedLoadMetadataByte metadata 0 "short").isNone
#guard (representationLoadMetadataByte metadata 0 (.byte 7)).isSome
#guard (representationLoadMetadataByte paddingMetadata 0 (.byte 7)).isSome
#guard match representationLoadMetadataByte paddingMetadata 0 (.byte 7) with
  | some (value, resultFootprint) =>
      value == (.value 7 none none) &&
        resultFootprint == footprint .read { allocation := 0, offset := 0, width := 1 }
  | none => false
#guard (unionLoadMetadataByte unionMetadata 0).isSome
#guard match unionLoadMetadataByte unionMetadata 0 with
  | some (value, resultFootprint) =>
      value == oneByte && resultFootprint == footprint .read { allocation := 0, offset := 0, width := 1 }
  | none => false
#guard byteFragment (mergeByte fragmentByte 1 0 0) == some 4
#guard (mergeBytes (Tag := Unit) [.uninitialized] [255] [1] [0]) ==
  some [mergeByte .uninitialized 1 255 0]
#guard (mergeBytes (Tag := Unit) [.uninitialized, .value 255 none none] [1, 2] [1, 1] [0, 0]).isSome
#guard (mergeBytes (Tag := Unit) [.uninitialized] [1, 2] [1] [0]).isNone
#guard (mergeBytes (Tag := Unit) [.uninitialized] [1] [1, 2] [0, 0]).isNone
#guard (mergeBytes (Tag := Unit) [.uninitialized] [1] [1, 2] [0]).isNone
#guard (copySnapshot [oneByte] [.uninitialized]) == some [oneByte]
#guard (copySnapshot [oneByte] []).isNone
#guard memcpySnapshot { allocation := 1, offset := 0, width := 2 }
  { allocation := 2, offset := 0, width := 2 } [oneByte, oneByte] ==
    some [oneByte, oneByte]
#guard (pairedCopySnapshot resolve [oneByte] [.uninitialized]).isSome
#guard pairedCopyFootprint { allocation := 1, offset := 0, width := 2 }
  { allocation := 2, offset := 4, width := 2 } 2
#guard (memcpySnapshot { allocation := 1, offset := 0, width := 2 }
  { allocation := 1, offset := 1, width := 2 } [oneByte, oneByte]).isNone
#guard (memmoveSnapshot { allocation := 1, offset := 0, width := 2 } { allocation := 1, offset := 1, width := 2 } [oneByte, oneByte]).isSome
#guard memmoveSnapshot { allocation := 1, offset := 0, width := 2 }
  { allocation := 1, offset := 1, width := 2 } [oneByte, oneByte] ==
    some [oneByte, oneByte]
#guard (pairedMemmoveSnapshot resolve
  { allocation := 1, offset := 0, width := 2 }
  { allocation := 1, offset := 1, width := 2 } [fragmentByte]).isSome
#guard pairedMemmoveFootprint { allocation := 1, offset := 0, width := 2 }
  { allocation := 1, offset := 1, width := 2 } 2
#guard (reallocMetadata metadata { bytes := [oneByte], state := () } [location] .fail).isSome
#guard match reallocMetadata metadata { bytes := [oneByte], state := () } [location] .fail with
  | some (.failed old, resultFootprint) =>
      old == metadata && resultFootprint == footprint .metadata { allocation := 0, offset := 0, width := 1 }
  | _ => false
#guard (reallocMetadata metadata { bytes := [oneByte], state := () } [location] (.address 64)).isSome
#guard (reallocMetadata metadata { bytes := [oneByte], state := () } [location] .unaddressable).isSome
#guard (reallocMetadata metadata { bytes := [oneByte], state := () }
  ([] : List (LocationState String)) (.address 64)).isNone
#guard (pairedReallocMetadata resolve metadata { bytes := [oneByte], state := () } [location] (.address 64)).isSome
#guard match allocateZeroSize (Tag := Unit) (TypeId := String) () .fail with
  | (.null, _) => true
  | _ => false
#guard match allocateZeroSize (Tag := Unit) (TypeId := String) () (.address 128) with
  | (.token metadata, resultFootprint) =>
      metadata.allocation.address == some 128 &&
        resultFootprint == footprint .metadata { allocation := 0, offset := 0, width := 0 }
  | _ => false
#guard pairedAllocateZeroSize resolve () (.address 128)
#guard ((allocateZeroSize (Tag := Unit) (TypeId := String) () (.address 128)).2.accesses.length == 1)
#guard reallocZeroGNU17 == .freedNull
#guard (freeMetadata metadata).isSome
#guard match freeMetadata metadata with
  | some (freed, resultFootprint) =>
      !freed.allocation.live &&
        resultFootprint == footprint .metadata { allocation := 0, offset := 0, width := 1 }
  | none => false
#guard (pairedFreeMetadata resolve metadata).isSome
#guard (freeMetadata ((freeMetadata metadata).getD (metadata, { accesses := [] })).1).isNone
#guard freePointer (Tag := Unit) (State := Unit) (TypeId := String) none == .nullSuccess
#guard freePointer (Tag := Unit) (State := Unit) (TypeId := String) (some metadata) == .freed
#guard freePointer (Tag := Unit) (State := Unit) (TypeId := String)
  (some ((freeMetadata metadata).getD (metadata, { accesses := [] })).1) == .stalePointer
#guard (loadByte one 0 0).isSome
#guard (loadByte empty 0 0).isNone
#guard (loadByte dead 0 0).isNone
#guard (loadByte one 0 1).isNone
#guard (storeByte one 0 0 (.value 66 none (some 0))).isSome
#guard (storeByte empty 0 0 (.value 66 none (some 0))).isNone
#guard (storeByte dead 0 0 (.value 66 none (some 0))).isNone
#guard (storeByte one 0 1 (.value 66 none (some 0))).isNone
#guard (pairedStoreByte resolve one 0 0 (.value 66 none (some 0))).isSome
#guard (pairedLoadByte resolve one 0 0).isSome
#guard (pairedStoreLoadByte resolve one 0 0 (.value 66 none (some 0))).isSome
#guard match pairedStoreByte resolve one 0 0 (.value 66 none (some 0)) with
  | some ((_, sourceFootprint), (_, targetFootprint)) =>
      sourceFootprint == footprint .write { allocation := 0, offset := 0, width := 1 } &&
        targetFootprint == footprint .write { allocation := 0, offset := 0, width := 1 }
  | none => false
#guard match pairedLoadByte resolve one 0 0 with
  | some ((_, sourceFootprint), (_, targetFootprint)) =>
      sourceFootprint == footprint .read { allocation := 0, offset := 0, width := 1 } &&
        targetFootprint == footprint .read { allocation := 0, offset := 0, width := 1 }
  | none => false
#guard (storeByte one 0 0 (.value 66 none (some 0))).any
  (fun result => result.2 == footprint .write { allocation := 0, offset := 0, width := 1 })
#guard (loadByte one 0 0).any
  (fun result => result.2 == footprint .read { allocation := 0, offset := 0, width := 1 })
#guard (endLifetime one 0).isSome
#guard (endLifetime empty 0).isNone
#guard (endLifetime dead 0).isNone
#guard (pairedEndLifetime resolve one 0).isSome
#guard match pairedEndLifetime resolve one 0 with
  | some ((_, sourceFootprint), (_, targetFootprint)) =>
      sourceFootprint == footprint .metadata { allocation := 0, offset := 0, width := 1 } &&
        targetFootprint == footprint .metadata { allocation := 0, offset := 0, width := 1 }
  | none => false
#guard (loadByte ((endLifetime one 0).getD (one, { accesses := [] })).1 0 0).isNone
#guard pairedStaleLoad resolve one 0 0
#guard pairedStaleStore resolve one 0 0 (.value 66 none (some 0))
#guard (offsetPointer pointer 1 0 pointer.address).isOk
#guard match offsetPointer pointer 0 1 pointer.address with | .error _ => true | _ => false
#guard match offsetPointer pointer 1 (-1) pointer.address with | .ok _ => true | _ => false
#guard pairedOffsetPointer resolve pointer 1 0 pointer.address
#guard match recoverAddress 100 [(3, 96, 104, ())] with | .recovered _ => true | _ => false
#guard match recoverAddress 104 [(3, 96, 104, ())] with | .empty _ => true | _ => false
#guard pairedRecoverAddress resolve 100 ([] : List (AllocId × Nat × Nat × Unit))
#guard renameReplayEvents resolve [.io "write" "stdout" "ok", .volatileRead [1, 2]] == [.io "write" "stdout" "ok", .volatileRead [1, 2]]

end LeanModels.C.F2Tests
