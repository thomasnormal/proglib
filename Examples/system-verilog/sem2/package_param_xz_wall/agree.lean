/- Clean-room loudness receipt for an IEEE 1800-2023 §6.20.2 package parameter
   whose declared four-state default contains z bits. -/
import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.package_param_xz_wall.agree
open LeanModels.Sv
#guard_msgs (drop error) in
load_design_sv2 packageParamXz from
  "Examples/system-verilog/sem2/package_param_xz_wall/package_param_xz_wall.sv.json"
end Examples.«system-verilog».sem2.package_param_xz_wall.agree
