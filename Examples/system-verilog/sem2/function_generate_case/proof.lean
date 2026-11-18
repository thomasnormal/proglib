import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.function_generate_case.proof

open LeanModels.Sv

load_design_sv2 functionGenerateCase
  from "Examples/system-verilog/sem2/function_generate_case/function_generate_case.sv.json"

#guard functionGenerateCase.sem.hasUnsupported
#guard functionGenerateCase.sem.processes.toList.all fun p =>
  match p with
  | .assign (.slice "y" _ 5) (.unsupported "CallExpression:user-function" _) => true
  | _ => false

end Examples.«system-verilog».sem2.function_generate_case.proof
