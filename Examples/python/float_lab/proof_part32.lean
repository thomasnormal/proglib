import Examples.python.float_lab.base

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

theorem floor_augmented :
    float_lab.floor_augmented() ==> Float64.ofBits 0x3ff0000000000000 := by
  have floorStep : Float64.floorRemWithNaN ⟨0x3ff0000000000000⟩ ⟨0x3fb999999999999a⟩ =
      .ok (⟨0x4022000000000000⟩, ⟨0x3fb9999999999996⟩) :=
    rfl
  have remainderStep : Float64.floorRemWithNaN ⟨0x4022000000000000⟩ ⟨0x4010000000000000⟩ =
      .ok (⟨0x4000000000000000⟩, ⟨0x3ff0000000000000⟩) := by rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  simp only [initial_world, publicThawArgs]
  rw [callIn.eq_2]
  py_simp [pythonRecursionLimit, pythonTopCallDepth, Run.finishCallAt, Run.leaveCallDepth,
    benignImportBindsStructured,
    float_lab, evalBinOpH, setLikeRefH, evalFloatDivmod, floatNumber, Float64.ofBits, floorStep, remainderStep]

