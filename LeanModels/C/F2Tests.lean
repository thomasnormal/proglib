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
