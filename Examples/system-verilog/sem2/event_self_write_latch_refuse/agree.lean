/- Canonical-E refusal for explicit event-list latch blocking self-writes under
   IEEE 1800-2023 §9.4.2. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.event_self_write_latch_refuse
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 event_self_write_latch from "Examples/system-verilog/sem2/event_self_write_latch_refuse/event_self_write_latch_refuse.sv.json"
def refused : Bool :=
  match PDesign.instantiateE2 event_self_write_latch.pdesign [] (PDesign.surfaceFuel []) with
  | .unsupported msg => msg.startsWith "AlwaysEvent:self-write"
  | _ => false
#guard refused
end Examples.«system-verilog».sem2.event_self_write_latch_refuse
