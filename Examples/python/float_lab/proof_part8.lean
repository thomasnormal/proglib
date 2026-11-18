import Examples.python.float_lab.base

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

theorem augmented :
    float_lab.augmented() ==> Float64.ofBits 0xbff4000000000000 := by
  have addStep : Float64.arithmetic .add ⟨0x3fe0000000000000⟩ ⟨0x3fd0000000000000⟩ =
      .ok ⟨0x3fe8000000000000⟩ := add_quarter
  have subtractStep : Float64.arithmetic .sub ⟨0x3fe8000000000000⟩ ⟨0x3fc0000000000000⟩ =
      .ok ⟨0x3fe4000000000000⟩ := subtract_eighth
  have multiplyStep : Float64.arithmetic .mult ⟨0x3fe4000000000000⟩ ⟨0xc000000000000000⟩ =
      .ok ⟨0xbff4000000000000⟩ := multiply_negative_two
  have negateStep : (⟨0x4000000000000000⟩ : Float64).neg = ⟨0xc000000000000000⟩ := rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  simp only [callIn.eq_2]
  py_simp [pythonRecursionLimit, pythonTopCallDepth, Run.finishCallAt, Run.leaveCallDepth,
    benignImportBindsStructured,
    float_lab, evalBinOpH, setLikeRefH, evalFloatArithmetic, floatNumber,
    addStep, subtractStep, multiplyStep, negateStep]
  rfl

