import Examples.python.float_lab.base

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

set_option maxHeartbeats 400000 in
theorem count_nan_head :
    float_lab.count_head(Float64.ofBits 0x7ff8000000000000,
      Float64.ofBits 0x3ff0000000000000) ==> Float64.ofBits 0x7ff8000000000000 := by
  refine ⟨64, ?_⟩
  unfold callFunction
  simp only [initial_world, publicThawArgs]
  rw [callIn.eq_2]
  py_simp [float_lab, evalBinOpH, setLikeRefH, evalFloatDivmod, floatNumber,
    float_ne_fstring, float_ne_lenMult, float_ne_starArg, float_ne_starTuple,
    float_ne_starList, funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree, moduleGenFree,
    funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    topLevelDefFree, Stmt.defFreeList, Stmt.defFree, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    lenMultBuiltinName, hasUnboundLocal, unboundLocalMarker,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Env.lookup, lookupG, Run.bind, Run.liftRes,
    pythonRecursionLimit, pythonTopCallDepth, Run.finishCallAt,
    Run.leaveCallDepth, Run.toPublic, Run.toPublic_ok, RVal.freezeB]
  rfl

