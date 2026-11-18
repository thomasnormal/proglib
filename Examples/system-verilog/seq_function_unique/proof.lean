import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».seq_function_unique.proof

open LeanModels.Sv

load_design_sv2 functionUnique from "Examples/system-verilog/seq_function_unique/function_unique_case_eval.sv.json"

#guard functionUnique.sem.hasUnsupported
#guard match functionUnique.sem.processes.toList with
  | [.assign (.ident "y") (.unsupported "CallExpression:user-function" _)] => true
  | _ => false

end Examples.«system-verilog».seq_function_unique.proof
