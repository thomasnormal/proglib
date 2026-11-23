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

def pointer : Pointer Unit := { provenance := some { allocation := 3, tag := () }, address := 0x1020304050607080 }

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
