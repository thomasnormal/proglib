import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.package_walls_h4
open LeanModels.Sv
#guard_msgs (drop error) in
load_design_sv2 h4Fn from "Examples/system-verilog/sem2/package_walls_h4/h4_fn.json"
#guard_msgs (drop error) in
load_design_sv2 h4Expr from "Examples/system-verilog/sem2/package_walls_h4/h4_expr.json"
end Examples.«system-verilog».sem2.package_walls_h4
