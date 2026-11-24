import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.for_loop_e
open LeanModels.Sv
load_design_sv2 forLoopE from "Examples/system-verilog/sem2/for_loop_e/for_loop_e.sv.json"
#guard forLoopE.pdesign.others == []
#guard match forLoopE.sem with
  | .ok _ => true
  | .timeout => true
  | .unsupported _ => true
end Examples.«system-verilog».sem2.for_loop_e
