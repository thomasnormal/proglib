/-
Canonical-E refusal for a legacy level-event writer whose intermediate value
can be sampled by a divided clock. IEEE 1800-2023 §§4.6, 4.7, 9.2.2.2 and 9.4.2
leave the activation/update ordering open.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.legacy_event_writer_race_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 legacyEventWriter
  from "Examples/system-verilog/sem2/legacy_event_writer_race_e/legacy_event_writer_race_e.sv.json"
#guard match legacyEventWriter.pdesign.processes with
  | [.alwaysFF "clk" _, .alwaysEvent _ _, .alwaysFF "div" _] => true
  | _ => false
#guard match legacyEventWriter.e with
  | .unsupported msg => msg.startsWith "Schedule:preemptive"
  | _ => false
end Examples.«system-verilog».sem2.legacy_event_writer_race_e.agree
