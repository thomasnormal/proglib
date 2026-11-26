import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.package_walls_h1

open LeanModels.Sv

load_design_sv2 h1 from "Examples/system-verilog/sem2/package_walls_h1/h1.json"

#guard h1.pdesign.packageParams.map (fun (_, p) => p.resolved?) ==
  [some 655372, some 589835, some 1, some 655372]
#guard h1.pdesign.defaultArgs == .ok [4]

end Examples.«system-verilog».sem2.package_walls_h1
