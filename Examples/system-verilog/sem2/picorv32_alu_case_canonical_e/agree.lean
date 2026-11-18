import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.picorv32_alu_case_canonical_e

open LeanModels.Sv

load_design_sv2 picoAluCase
  from "Examples/system-verilog/sem2/picorv32_alu_case_canonical_e/picorv32_alu_case_canonical_e.sv.json"

#guard match picoAluCase.e 0 with
  | .unsupported msg => msg == "Comb:dependency-order: 9.2.2.2/9.4.2.2: reactive process reads 'alu_out_0' from itself or a later reactive process; canonical E has no fixed-point scheduler"
  | _ => false

end Examples.«system-verilog».sem2.picorv32_alu_case_canonical_e
