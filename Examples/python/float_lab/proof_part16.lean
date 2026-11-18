import Examples.python.float_lab.base

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

theorem constructor_invalid_caught :
    float_lab.constructor_invalid_caught() ==> (17 : PyInt) := by
  have invalid : Float64.fromText "1._0" = .error .invalid := rfl
  have rendered : LeanModels.Python.reprStr "1._0" = some "'1._0'" := rfl
  have failure : floatCastArgs [.str "1._0"] =
      .exn (.valueError "could not convert string to float: '1._0'") := by
    simp only [floatCastArgs, floatCastVal, invalid, rendered]
    congr 2
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [initial_world]
  simp only [callIn.eq_2]
  py_simp [pythonRecursionLimit, pythonTopCallDepth, Run.finishCallAt, Run.leaveCallDepth,
    benignImportBindsStructured,
    float_lab, failure, floatCastArgsH_str,
    float_ne_fstring, float_ne_lenMult, float_ne_starArg, float_ne_starTuple,
    float_ne_starList, funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree, moduleGenFree,
    funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    topLevelDefFree, Stmt.defFreeList, Stmt.defFree, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    lenMultBuiltinName, hasUnboundLocal, unboundLocalMarker,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Env.lookup, lookupG, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB, excHandlerNames, excHandlerTuple, excHandlerBare,
    excHandlerPrimary, excHandlerAdmitted, excHandlerMatches, dynamicShadowHandlerName,
    userExcCatches, classAtExc, builtinExcNameCatches, builtinExcCatches]
  rfl

