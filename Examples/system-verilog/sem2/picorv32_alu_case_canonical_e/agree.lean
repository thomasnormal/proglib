import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.picorv32_alu_case_canonical_e

open LeanModels.Sv

load_design_sv2 picoAluCase
  from "Examples/system-verilog/sem2/picorv32_alu_case_canonical_e/picorv32_alu_case_canonical_e.sv.json"

#guard match picoAluCase.e 0 with
  | .ok _ => true
  | _ => false

end Examples.«system-verilog».sem2.picorv32_alu_case_canonical_e
