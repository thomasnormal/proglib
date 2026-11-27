import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.duplicate_generate_group_e
open LeanModels.Sv
load_design_sv2 duplicateGenerateGroup from
  "Examples/system-verilog/sem2/duplicate_generate_group_e/duplicate_generate_group_e.sv.json"
#guard match duplicateGenerateGroup.e 2 with | .ok _ => true | _ => false
end Examples.«system-verilog».sem2.duplicate_generate_group_e
