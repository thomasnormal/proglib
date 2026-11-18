import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.assignment_pattern_param_e
open LeanModels.Sv
#guard_msgs (drop error) in
load_design_sv2 assignmentPattern
  from "Examples/system-verilog/sem2/assignment_pattern_param_e/assignment_pattern_param_e.sv.json"
end Examples.«system-verilog».sem2.assignment_pattern_param_e
