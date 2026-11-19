import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.initial_error_refuse
open LeanModels.Sv
load_design_sv2 initialError
  from "Examples/system-verilog/sem2/initial_error_refuse/initial_error_refuse.sv.json"
#guard initialError.pdesign.processes.length == 2
#guard match initialError.pdesign.processes with
  | [.initial (.unsupported "SysCall:$error" _), .assign "y" (.ident "x")] => true
  | _ => false
end Examples.«system-verilog».sem2.initial_error_refuse
