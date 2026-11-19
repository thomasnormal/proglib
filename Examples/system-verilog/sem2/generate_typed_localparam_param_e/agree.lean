import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.generate_typed_localparam_param_e
open LeanModels.Sv
load_design_sv2 generateTypedLocalparamParam from
  "Examples/system-verilog/sem2/generate_typed_localparam_param_e/generate_typed_localparam_param_e.sv.json"
#guard generateTypedLocalparamParam.pdesign.others == []
#guard match generateTypedLocalparamParam.e 8 with
  | .ok d => d.processes.size == 1
  | _ => false
#guard match generateTypedLocalparamParam.e 3 with
  | .ok d => d.processes.size == 1
  | _ => false
end Examples.«system-verilog».sem2.generate_typed_localparam_param_e
