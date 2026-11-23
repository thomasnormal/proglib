import LeanModels.C.F2

namespace LeanModels.C.F2Tests

open LeanModels.C.F2

abbrev TestByte := Byte Unit
abbrev TestAllocation := Allocation Unit Unit
abbrev TestStore := Store Unit Unit

def empty : TestStore := { allocations := [], nextId := 0 }

def oneByte : TestByte := .value 65 none (some 0)

def one : TestStore :=
  { allocations := [(0, { live := true, address := some 32,
                           bytes := [oneByte], state := () })]
    nextId := 1 }

#guard placementAllowed one 8 1
#guard !placementAllowed one 32 1
#guard (allocate one { bytes := [Byte.uninitialized], state := () }
  (.address 32)).isNone
#guard alignmentAllowed 16 8
#guard !alignmentAllowed 18 8
#guard (allocateAligned empty { bytes := [oneByte], state := () }
  (.address 16) 8).isSome
#guard (allocateAligned empty { bytes := [oneByte], state := () }
  (.address 18) 8).isNone
#guard placementWithin 8 4 16
#guard !placementWithin 14 4 16
#guard (allocateBounded empty { bytes := [oneByte], state := () }
  (.address 8) 8 16).isOk
#guard (allocateBounded empty { bytes := [oneByte], state := () }
  (.address 14) 1 16) == .error .exhausted
#guard (PlacementAgreement.mk (fun _ => some 8) (fun _ => some 8)
  (fun _ => true)).agrees
#guard footprintAgrees (mergeFootprint 1 0 2) (mergeFootprint 1 0 2)

def footprintWidth : Footprint → Nat
  | { accesses := [(_, region)] } => region.width
  | _ => 0

#guard (allocate empty { bytes := [.uninitialized], state := () }
  (.address 32)).isSome
#guard (allocate empty { bytes := [.uninitialized], state := () }
  .unaddressable).isSome
#guard (allocate empty { bytes := [.uninitialized], state := () }
  .fail).isNone
#guard (storeByte one 0 0 (.value 66 none (some 0))).isSome
#guard (loadByte one 0 0).isSome
#guard (loadByte one 0 0).map (fun result => footprintWidth result.2) == some 1
#guard (endLifetime one 0).isSome
#guard (endLifetime (endLifetime one 0).getD (one, {})).isNone
def dead : TestStore := (endLifetime one 0).getD (one, {}) |>.1
#guard (loadByte dead 0 0).isNone
#guard (storeByte dead 0 0 oneByte).isNone

def location : LocationState String :=
  { effectiveType := .typed "int", initialized := true }
#guard location.initialized
#guard HookChoice.unspecified 3 == HookChoice.unspecified 3

def locations : LocationStore String := [(3, 0, location)]
#guard (setLocation locations 3 0 { effectiveType := .padding, initialized := false }).isSome
#guard (setLocation locations 4 0 location).isNone

def metadata : AllocationMetadata Unit Unit String :=
  { allocation := one.allocations.head!.2
    locations := [location] }
#guard metadata.locations.length == metadata.allocation.bytes.length
#guard (allocateMetadata { bytes := [oneByte], state := () } [location] (.address 8)).isSome
#guard (allocateMetadata { bytes := [oneByte], state := () } [] (.address 8)).isNone
#guard (storeMetadataByte metadata 0 (.value 66 none (some 0))).isSome
#guard (storeMetadataByte metadata 1 oneByte).isNone
#guard (typedStoreMetadataByte metadata 0 "long" oneByte).isSome
#guard (typedStoreMetadataByte metadata 1 "long" oneByte).isNone
def typedMetadata : AllocationMetadata Unit Unit String :=
  (typedStoreMetadataByte metadata 0 "long" oneByte).getD (metadata, {}).1
#guard (typedLoadMetadataByte typedMetadata 0 "long").isSome
#guard (typedLoadMetadataByte typedMetadata 0 "int").isNone
#guard (unionLoadMetadataByte typedMetadata 0).isSome
def paddingMetadata : AllocationMetadata Unit Unit String :=
  { metadata with locations := [{ effectiveType := .padding, initialized := false }] }
#guard (representationLoadMetadataByte paddingMetadata 0 (.byte 7)).isSome
#guard (representationLoadMetadataByte metadata 0 (.byte 7)).isSome
#guard mergeByte .uninitialized 1 1 0 == .value 1 none none
#guard mergeByte (.value 255 none none) 1 0 0 == .value 254 none none
#guard (mergeBytes [.uninitialized, .value 255 none none]
  [1, 2] [1, 1] [0, 0]).isSome
#guard (mergeBytes [.uninitialized] [1, 2] [1, 1] [0, 0]).isNone
#guard (mergeFootprint 3 4 2).accesses.length == 1
def fragmentByte := Byte.value 7 (some { allocation := 3, tag := () }) (some 4)
#guard (mergeByte fragmentByte 1 0 0).fragment == some 4
#guard copySnapshot [oneByte] [.uninitialized] == some [oneByte]
#guard copySnapshot [oneByte] [] |>.isNone
#guard (copyFootprint { allocation := 1, offset := 0, width := 0 }
  { allocation := 2, offset := 4, width := 0 } 1).accesses.length == 2
#guard regionsOverlap { allocation := 1, offset := 0, width := 2 }
  { allocation := 1, offset := 1, width := 2 } 2
#guard (memcpySnapshot { allocation := 1, offset := 0, width := 2 }
  { allocation := 1, offset := 1, width := 2 } [oneByte, oneByte]).isNone
#guard (memmoveSnapshot { allocation := 1, offset := 0, width := 2 }
  { allocation := 1, offset := 1, width := 2 } [oneByte, oneByte]).isSome
#guard match reallocMetadata metadata { bytes := [oneByte], state := () } [location] .fail with
  | some (.failed old, _) => old.allocation.address == metadata.allocation.address
  | _ => false
#guard match reallocMetadata metadata { bytes := [oneByte], state := () } [location] (.address 64) with
  | some (.replaced _, _) => true
  | _ => false
#guard match allocateZeroSize () (.address 128) with
  | (.token metadata, _) => metadata.allocation.bytes.length == 0
  | _ => false
#guard reallocZeroGNU17 == .freedNull
#guard (freeMetadata metadata).isSome
#guard (freeMetadata (freeMetadata metadata).getD (metadata, {})).isNone
#guard match allocateZeroSize () (.address 128) with
  | (.token token, _) => zeroTokenFreeable token && zeroTokenEqual token token
  | _ => false
#guard freePointer none == .nullSuccess
#guard freePointer (some metadata) == .freed
#guard freePointer (some ((freeMetadata metadata).getD (metadata, {})).1) == .stalePointer

def pointer : Pointer Unit := { provenance := some { allocation := 3, tag := () }, address := 0x1020304050607080 }

def resolve : AllocId → Nat := fun id => if id == 0 then 100 else 200
def renamedOne : TestStore := renameStore resolve one
#guard renamedOne.allocations.head!.2.address == some 100
#guard (renameStore resolve renamedOne) == renamedOne
#guard (WellFormed (renameStore resolve one) : Prop) = True
#guard (renamePointer resolve pointer).provenance == pointer.provenance
#guard (renameByte resolve fragmentByte).fragment == fragmentByte.fragment
#guard (renameByte resolve fragmentByte).provenance == fragmentByte.provenance
#guard match renameByte resolve (.value 7 (some { allocation := 0, tag := () }) (some 0)) with
  | .value bits (some provenance) (some fragment) =>
      bits == 100 && provenance.allocation == 0 && fragment == 0
  | _ => false
#guard (pairedStoreByte resolve one 0 0 (.value 66 none (some 0))).isSome
#guard match pairedStoreByte resolve one 0 0 (.value 66 none (some 0)) with
  | some (sourceResult, targetResult) =>
      targetResult.1 = renameStore resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2
  | none => false
#guard (pairedLoadByte resolve one 0 0).isSome
#guard match pairedLoadByte resolve one 0 0 with
  | some (sourceResult, targetResult) =>
      targetResult.1 = renameByte resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2
  | none => false
def pointerStore : TestStore :=
  { allocations := [(0, { live := true, address := some 32,
                           bytes := [.value 7 (some { allocation := 0, tag := () }) (some 0)],
                           state := () })]
    nextId := 1 }
#guard match pairedLoadByte resolve pointerStore 0 0 with
  | some (sourceResult, targetResult) =>
      targetResult.1 = .value 100 (some { allocation := 0, tag := () }) (some 0) &&
      targetResult.2 = sourceResult.2
  | none => false
#guard match pairedStoreLoadByte resolve pointerStore 0 0
    (.value 9 (some { allocation := 0, tag := () }) (some 0)) with
  | some pair =>
      pair.targetStore.1 = renameStore resolve pair.sourceStore.1 &&
      pair.targetLoad.1 = renameByte resolve pair.sourceLoad.1 &&
      pair.targetLoad.2 = pair.sourceLoad.2
  | none => false
#guard (pairedEndLifetime resolve one 0).isSome
#guard match pairedEndLifetime resolve one 0 with
  | some (sourceResult, targetResult) =>
      targetResult.1 = renameStore resolve sourceResult.1 &&
      targetResult.2 = sourceResult.2 &&
      targetResult.1.allocations.head!.2.live == false
  | none => false
#guard pairedStaleLoad resolve one 0 0
#guard pairedStaleStore resolve one 0 0 (.value 66 none (some 0))

#guard decodePointer (encodePointer pointer) == some pointer
#guard copyEncoded (encodePointer pointer) == encodePointer pointer
#guard pointerEqual pointer pointer .equal
#guard !(pointerEqual pointer pointer .unequal)
#guard (offsetPointer pointer 1 0 pointer.address) == .ok pointer
#guard (offsetPointer pointer 0 1 pointer.address).isError
#guard (expose { exposed := false }).exposed
#guard match recoverAddress 100 [(3, 96, 104, ())] with
  | .recovered _ => true
  | _ => false
#guard match recoverAddress 104 [(3, 96, 104, ())] with
  | .empty _ => true
  | _ => false

def fixture : ReplayFixture :=
  { sourceHash := "source-sha256"
    compilerVersion := "clang version 21.1.8"
    targetTriple := "x86_64-linux-gnu"
    placements := [{ allocation := 3, base := 96, size := 8, exposed := true }]
    events := [.io "write" "stdout" "ok"]
    ending := .exit 0 }

#guard fixture.wellFormed

end LeanModels.C.F2Tests
