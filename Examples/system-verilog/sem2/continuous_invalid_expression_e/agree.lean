import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.continuous_invalid_expression_e
open LeanModels.Sv
load_design_sv2 bad from "Examples/system-verilog/sem2/continuous_invalid_expression_e/continuous_invalid_expression_e.sv.json"
#guard bad.pdesign.others == []
#guard match bad.e with | .ok _ => true | .timeout => true | .unsupported _ => true
end Examples.«system-verilog».sem2.continuous_invalid_expression_e
