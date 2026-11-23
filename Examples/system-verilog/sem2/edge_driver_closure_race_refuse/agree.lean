/- Canonical-E refusal for edge races whose read visibility crosses a selected
   continuous driver and an always_comb driver. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.edge_driver_closure_race_refuse
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 edge_driver_closure_race from "Examples/system-verilog/sem2/edge_driver_closure_race_refuse/edge_driver_closure_race_refuse.sv.json"
def refused : Bool :=
  match PDesign.instantiateE2 edge_driver_closure_race.pdesign [] (PDesign.surfaceFuel []) with
  | .unsupported msg => msg.startsWith "Event:edge-blocking-race"
  | _ => false
#guard refused
end Examples.«system-verilog».sem2.edge_driver_closure_race_refuse
