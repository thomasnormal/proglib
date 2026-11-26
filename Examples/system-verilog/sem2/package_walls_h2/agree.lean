import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.package_walls_h2
open LeanModels.Sv
load_design_sv2 h2 from "Examples/system-verilog/sem2/package_walls_h2/h2.json"
#guard h2.pdesign.packageParams.map (fun (_, p) => p.resolved?) == [some 4, some 4, some 4]
#guard h2.pdesign.defaultArgs == .ok [4]
end Examples.«system-verilog».sem2.package_walls_h2
