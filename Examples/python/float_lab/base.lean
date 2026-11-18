import LeanModels.Python.Surface
import LeanModels.Python.Float64Tests

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

load_program float_lab from "Examples/python/float_lab/float_lab.json"

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

theorem initial_world :
    initWorld float_lab = (⟨#[], [], [], [], 0⟩ : World) := by
  rfl

theorem floatCastArgsH_str (h : Heap) (s : String) :
    floatCastArgsH h [.str s] = floatCastArgs [.str s] := by
  rfl

theorem float_ne_fstring : ("float" == fstringFormatBuiltinName) = false := by decide
theorem float_ne_lenMult : ("float" == lenMultBuiltinName) = false := by decide
theorem float_ne_starArg : ("float" == starArgBuiltinName) = false := by decide
theorem float_ne_starTuple : ("float" == starTupleBuiltinName) = false := by decide
theorem float_ne_starList : ("float" == starListBuiltinName) = false := by decide

theorem divmod_ne_fstring : ("divmod" == fstringFormatBuiltinName) = false := by decide
theorem divmod_ne_lenMult : ("divmod" == lenMultBuiltinName) = false := by decide
theorem divmod_ne_starArg : ("divmod" == starArgBuiltinName) = false := by decide
theorem divmod_ne_starTuple : ("divmod" == starTupleBuiltinName) = false := by decide
theorem divmod_ne_starList : ("divmod" == starListBuiltinName) = false := by decide


theorem add_quarter :
    Float64.arithmetic .add (Float64.ofBits 0x3fe0000000000000)
      (Float64.ofBits 0x3fd0000000000000) = .ok (Float64.ofBits 0x3fe8000000000000) := rfl

theorem subtract_eighth :
    Float64.arithmetic .sub (Float64.ofBits 0x3fe8000000000000)
      (Float64.ofBits 0x3fc0000000000000) = .ok (Float64.ofBits 0x3fe4000000000000) := rfl

theorem multiply_negative_two :
    Float64.arithmetic .mult (Float64.ofBits 0x3fe4000000000000)
      (Float64.ofBits 0xc000000000000000) = .ok (Float64.ofBits 0xbff4000000000000) := rfl


theorem remainder_nine_four :
    Float64.floorRem (Float64.ofBits 0x4022000000000000)
      (Float64.ofBits 0x4010000000000000) =
      .ok (Float64.ofBits 0x4000000000000000, Float64.ofBits 0x3ff0000000000000) := rfl

