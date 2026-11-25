import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.shift_add_datapath_refuse_e
open LeanModels.Sv
load_design_sv2 datapath from "Examples/system-verilog/sem2/shift_add_datapath_refuse_e/shift_add_datapath_refuse_e.sv.json"
#guard match datapath.e 8 with | .unsupported _ => true | _ => false
end Examples.«system-verilog».sem2.shift_add_datapath_refuse_e
