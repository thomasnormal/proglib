import Examples.python.float_lab.base

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

theorem floor_nan_pair :
    float_lab.floor_pair(Float64.ofBits 0x7ff8000000000001,
      Float64.ofBits 0x3ff0000000000000) ==>
      Val.tuple #[
        .float (Float64.ofBits 0x7ff8000000000001),
        .float (Float64.ofBits 0x7ff8000000000001),
        .tuple #[
          .float (Float64.ofBits 0x7ff8000000000001),
          .float (Float64.ofBits 0x7ff8000000000001)
        ]
      ] := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [initial_world]
  simp only [callIn.eq_2]
  have nanStep : Float64.floorRemWithNaN ⟨0x7ff8000000000001⟩ ⟨0x3ff0000000000000⟩ =
      .ok (⟨0x7ff8000000000001⟩, ⟨0x7ff8000000000001⟩) := rfl
  py_simp [pythonRecursionLimit, pythonTopCallDepth, Run.finishCallAt, Run.leaveCallDepth,
    benignImportBindsStructured,
    float_lab, evalBinOpH, setLikeRefH, evalFloatDivmod, floatNumber,
    Float64.ofBits, nanStep,
    divmod_ne_fstring, divmod_ne_lenMult, divmod_ne_starArg,
    divmod_ne_starTuple, divmod_ne_starList, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, topLevelDefFree,
    Stmt.defFreeList, Stmt.defFree, starArgBuiltinName, starListBuiltinName,
    starTupleBuiltinName, fstringFormatBuiltinName, lenMultBuiltinName,
    hasUnboundLocal, unboundLocalMarker, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Env.lookup,
    lookupG, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  rfl

