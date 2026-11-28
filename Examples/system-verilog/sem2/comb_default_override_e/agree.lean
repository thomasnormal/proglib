import LeanModels.Sv.Ingest2
open LeanModels.Sv LeanModels.Sv.Kernel
namespace Examples.«system-verilog».sem2.comb_default_override_e
load_design_sv2 wall from "Examples/system-verilog/sem2/comb_default_override_e/comb_default_override.sv.json"
#guard match PDesign.instantiateE2 wall.pdesign [] (PDesign.surfaceFuel []) with
  | .unsupported msg => msg.contains "Event:time-zero" && msg.contains "4.7/9.2.2.2.2"
  | _ => false
end Examples.«system-verilog».sem2.comb_default_override_e
