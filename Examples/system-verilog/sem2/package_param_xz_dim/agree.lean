/- Integer-required package-parameter use remains a loud named boundary. -/
import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.package_param_xz_dim.agree
open LeanModels.Sv
#guard_msgs (drop error) in
load_design_sv2 packageParamXzDim from
  "Examples/system-verilog/sem2/package_param_xz_dim/package_param_xz_dim.sv.json"
end Examples.«system-verilog».sem2.package_param_xz_dim.agree
