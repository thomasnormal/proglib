/-
The system-function expression wall for IEEE 1800-2023 §20.2.2.
The parser-native call is retained as `SysCall` and the current value tier
refuses its external plusarg environment explicitly.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.system_function_plusargs.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 systemFunctionPlusargs
  from "Examples/system-verilog/sem2/system_function_plusargs/system_function_plusargs.sv.json"

#guard systemFunctionPlusargs.pdesign.others == []
#guard match systemFunctionPlusargs.pdesign.processes with
  | [.alwaysComb (.block [.blockingAssign "y"
      (.ternary (.sysCall .testPlusargs _)
        (.ident "in") (.lit _))])] => true
  | _ => false

private def flat : Design2 := systemFunctionPlusargs.pdesign.instantiateD2 []

#guard match flat.processes.toList with
  | [.alwaysComb (.block #[.blockingAssign (.ident "y")
      (.ternary (.unsupported "SysCall"
          "$test$plusargs argument outside the declared-signal tier")
        (.ident "in") (.lit _))])] => true
  | _ => false


end Examples.«system-verilog».sem2.system_function_plusargs.agree
