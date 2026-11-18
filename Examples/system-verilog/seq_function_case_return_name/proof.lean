import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».seq_function_case_return_name.proof
open LeanModels.Sv
load_design_sv2 functionCaseReturnName from "Examples/system-verilog/seq_function_case_return_name/function_case_return_name.sv.json"
#guard functionCaseReturnName.sem.hasUnsupported
#guard match functionCaseReturnName.sem.processes.toList with
  | [.assign (.ident "y") (.unsupported "CallExpression:user-function" _)] => true
  | _ => false
end Examples.«system-verilog».seq_function_case_return_name.proof
