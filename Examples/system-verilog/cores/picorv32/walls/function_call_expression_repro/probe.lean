import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».cores.picorv32.walls.function_call_expression_repro

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 functionCallExpressionRepro
  from "Examples/system-verilog/cores/picorv32/walls/function_call_expression_repro/function_call_expression_repro.sv.json"

#guard functionCallExpressionRepro.pdesign.others == []

/- `$test$plusargs` remains a parser-native system-call expression.  The
   canonical E route evaluates it only after the caller supplies its explicit
   plus-argument environment. -/
#guard functionCallExpressionRepro.sem.hasUnsupported

private def flagArg : PExpr := .lit (LVec.ofNat 32 0x666c6167)

#guard match functionCallExpressionRepro.e with
  | .ok E =>
        (E.withPlusargs []).evalSysCall E.env E.elems E.initial [] .testPlusargs flagArg ==
          .ok (LVec.ofNat 1 0) &&
        (E.withPlusargs ["flag"]).evalSysCall E.env E.elems E.initial [] .testPlusargs flagArg ==
          .ok (LVec.ofNat 1 1)
  | _ => false

#guard match functionCallExpressionRepro.e with
  | .ok d => d.processes.size == 1
  | _ => false

def eRunMessage : String := match functionCallExpressionRepro.e with
  | .ok d => match d.initialState with
    | .ok st => match runCoreMemRows d st [[("in", LVec.ofNat 1 0)]] with
      | .ok _ => "ok"
      | .timeout => "timeout"
      | .unsupported msg => msg
    | .timeout => "initial-state timeout"
    | .unsupported msg => msg
  | .timeout => "elaboration timeout"
  | .unsupported msg => msg

#guard eRunMessage == "ok"

end Examples.«system-verilog».cores.picorv32.walls.function_call_expression_repro
