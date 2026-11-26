import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.package_walls_r1

open LeanModels.Sv

load_design_sv2 r1 from "Examples/system-verilog/sem2/package_walls_r1/r1.json"

#guard r1.pdesign.packageParams.map (fun (_, p) => p.resolved?) == [some 6]
#guard r1.pdesign.defaultArgs == .ok []

end Examples.«system-verilog».sem2.package_walls_r1
