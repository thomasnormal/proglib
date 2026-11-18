import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».cores.picorv32.walls.function_call_expression_repro

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 functionCallExpressionRepro
  from "Examples/system-verilog/cores/picorv32/walls/function_call_expression_repro/function_call_expression_repro.sv.json"

#guard functionCallExpressionRepro.pdesign.others == []

/- `$test$plusargs` is retained as a parser-native system-call expression.
   Its value depends on the simulator invocation, so canonical E refuses it
   at the declared-signal tier instead of selecting a plus-argument result. -/
#guard functionCallExpressionRepro.sem.hasUnsupported

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

#guard eRunMessage == "unsupported expression 'SysCall'"

end Examples.«system-verilog».cores.picorv32.walls.function_call_expression_repro
