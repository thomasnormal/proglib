import Examples.python.float_lab.base

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

theorem cancel (value : PyFloat) (finite : value.exponent ≠ 2047) :
    float_lab.cancel(value) ==> Float64.ofBits 0 := by
  have notNaN : value.isNaN = false := by
    simp [Float64.isNaN, finite]
  have notInvalid :
      floatArithmeticInvalid .sub value value = false := by
    simp [floatArithmeticInvalid, Float64.isInf, finite]
  refine ⟨32, ?_⟩
  unfold callFunction
  simp only [callIn.eq_2]
  py_simp [pythonRecursionLimit, pythonTopCallDepth, Run.finishCallAt, Run.leaveCallDepth,
    benignImportBindsStructured,
    float_lab, evalBinOpH, setLikeRefH, evalFloatArithmetic, floatNumber,
    Float64.arithmetic_sub_self, finite, notNaN, notInvalid]

