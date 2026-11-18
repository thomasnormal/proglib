import Examples.python.float_lab.proof_part28

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

theorem floor_infinite :
    float_lab.floor_infinite() ==> Float64.ofBits 0xbff0000000000000 := by
  have floorStep : Float64.floorRemWithNaN ⟨0x4014000000000000⟩ ⟨0xfff0000000000000⟩ =
      .ok (⟨0xbff0000000000000⟩, ⟨0xfff0000000000000⟩) := rfl
  have parsed : Float64.fromText "-inf" = .ok (Float64.ofBits 0xfff0000000000000) := rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [initial_world]
  simp only [callIn.eq_2]
  py_simp [pythonRecursionLimit, pythonTopCallDepth, Run.finishCallAt, Run.leaveCallDepth,
    benignImportBindsStructured,
    float_lab, evalBinOpH, floatCastArgsH_str,
    floatCastArgs, floatCastVal, evalFloatDivmod, floatNumber,
    Float64.ofBits, floorStep, parsed,
    float_ne_fstring, float_ne_lenMult, float_ne_starArg, float_ne_starTuple,
    float_ne_starList, funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree, moduleGenFree,
    funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    topLevelDefFree, Stmt.defFreeList, Stmt.defFree, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    lenMultBuiltinName, hasUnboundLocal, unboundLocalMarker,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Env.lookup, lookupG, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]
  rfl

theorem remainder_infinite :
    float_lab.remainder_infinite() ==> Float64.ofBits 0xfff0000000000000 := by
  have floorStep : Float64.floorRemWithNaN ⟨0x4014000000000000⟩ ⟨0xfff0000000000000⟩ =
      .ok (⟨0xbff0000000000000⟩, ⟨0xfff0000000000000⟩) := rfl
  have parsed : Float64.fromText "-inf" = .ok (Float64.ofBits 0xfff0000000000000) := rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [initial_world]
  simp only [callIn.eq_2]
  py_simp [pythonRecursionLimit, pythonTopCallDepth, Run.finishCallAt, Run.leaveCallDepth,
    benignImportBindsStructured, float_lab, evalBinOpH, floatCastArgsH_str,
    floatCastArgs, floatCastVal, evalFloatDivmod, floatNumber,
    Float64.ofBits, floorStep, parsed, float_ne_fstring, float_ne_lenMult,
    float_ne_starArg, float_ne_starTuple, float_ne_starList, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList,
    Expr.heapFree, moduleGenFree, funsGenAllocFree, Stmt.genAllocFree,
    Stmt.genAllocFreeList, topLevelDefFree, Stmt.defFreeList, Stmt.defFree,
    starArgBuiltinName, starListBuiltinName, starTupleBuiltinName,
    fstringFormatBuiltinName, lenMultBuiltinName, hasUnboundLocal,
    unboundLocalMarker, isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Env.lookup, lookupG, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]
  rfl

end Examples.python.float_lab.proof
