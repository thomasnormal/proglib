import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».seq_function.proof

open LeanModels.Sv

load_design_sv2 functionEval from "Examples/system-verilog/seq_function/function_call_eval.sv.json"

#guard functionEval.sem.hasUnsupported
#guard match functionEval.sem.processes.toList with
  | [.assign (.ident "y") (.unsupported "CallExpression:user-function" _)] => true
  | _ => false

end Examples.«system-verilog».seq_function.proof
