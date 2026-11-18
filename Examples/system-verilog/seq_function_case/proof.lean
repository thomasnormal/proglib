import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».seq_function_case.proof

open LeanModels.Sv

load_design_sv2 functionCase from "Examples/system-verilog/seq_function_case/function_case_eval.sv.json"

#guard functionCase.sem.hasUnsupported
#guard match functionCase.sem.processes.toList with
  | [.assign (.ident "y") (.unsupported "CallExpression:user-function" _)] => true
  | _ => false

end Examples.«system-verilog».seq_function_case.proof
