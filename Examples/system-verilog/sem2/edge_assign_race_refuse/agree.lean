/- Canonical-E refusal for a same-edge blocking race hidden by a continuous
   assignment, under IEEE 1800-2023 §§4.7 and 10.4.1. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.edge_assign_race_refuse
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 edge_assign_race_refuse from "Examples/system-verilog/sem2/edge_assign_race_refuse/edge_assign_race_refuse.sv.json"
def refused : Bool :=
  match PDesign.instantiateE2 edge_assign_race_refuse.pdesign [] (PDesign.surfaceFuel []) with
  | .unsupported msg => msg.startsWith "Event:edge-blocking-race"
  | _ => false
#guard refused
end Examples.«system-verilog».sem2.edge_assign_race_refuse
