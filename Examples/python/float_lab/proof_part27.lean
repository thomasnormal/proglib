import Examples.python.float_lab.base

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

theorem floor_tenth :
    float_lab.floor_tenth() ==> Float64.ofBits 0x4022000000000000 := by
  have floorStep : Float64.floorRemWithNaN ⟨0x3ff0000000000000⟩ ⟨0x3fb999999999999a⟩ =
      .ok (⟨0x4022000000000000⟩, ⟨0x3fb9999999999996⟩) :=
    rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  simp only [callIn.eq_2]
  py_simp [pythonRecursionLimit, pythonTopCallDepth, Run.finishCallAt, Run.leaveCallDepth,
    benignImportBindsStructured,
    float_lab, evalBinOpH, setLikeRefH, evalFloatDivmod, floatNumber, Float64.ofBits, floorStep]
  rfl

