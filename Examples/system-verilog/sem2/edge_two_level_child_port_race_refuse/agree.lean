/- Canonical-E refusal for a same-edge blocking race through a grandchild
   input port connection. The flattened hierarchy aliases the grandchild clock
   back to the top-level clock before event matching. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.edge_two_level_child_port_race_refuse
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 edge_two_level_child_port_race from "Examples/system-verilog/sem2/edge_two_level_child_port_race_refuse/edge_two_level_child_port_race_refuse.sv.json"
def refused : Bool :=
  match PDesign.instantiateE2H edge_two_level_child_port_race.pdesign edge_two_level_child_port_race.plib [] with
  | .unsupported msg => msg.startsWith "Event:edge-blocking-race"
  | _ => false
#guard refused
end Examples.«system-verilog».sem2.edge_two_level_child_port_race_refuse
