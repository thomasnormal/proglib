/-
Canonical-E refusal receipt for a continuous-assignment-driven time-zero event
source. IEEE 1800-2023 §§4.7 and 9.4.2 leave the ordering between the driver
update and the first edge wait open, so canonical E refuses both source orders.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.time_zero_event_assign_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 gclk from "Examples/system-verilog/sem2/time_zero_event_assign_e/event_assign_gclk.sv.json"
load_design_sv2 gclk2 from "Examples/system-verilog/sem2/time_zero_event_assign_e/event_assign_gclk2.sv.json"
#guard match PDesign.instantiateCoreMem gclk.pdesign [] with
  | .unsupported msg => msg.contains "4.7/9.4.2"
  | _ => false
#guard match PDesign.instantiateCoreMem gclk2.pdesign [] with
  | .unsupported msg => msg.contains "4.7/9.4.2"
  | _ => false
end Examples.«system-verilog».sem2.time_zero_event_assign_e
