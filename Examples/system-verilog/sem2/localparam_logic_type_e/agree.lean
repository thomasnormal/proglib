import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.localparam_logic_type_e
open LeanModels.Sv
load_design_sv2 lp from "Examples/system-verilog/sem2/localparam_logic_type_e/localparam_logic_type_e.sv.json"
#guard lp.pdesign.others == []
#check lp.sem
end Examples.«system-verilog».sem2.localparam_logic_type_e
