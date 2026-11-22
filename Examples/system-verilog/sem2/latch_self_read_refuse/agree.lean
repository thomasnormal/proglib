/- Canonical-E refusal receipt for always_latch read-before-write bodies.
   IEEE 1800-2023 §9.2.2.3 gives always_latch the implicit sensitivity
   exclusion that makes these activation values simulator-dependent. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.latch_self_read_refuse.agree

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 latch_self_read_a from "Examples/system-verilog/sem2/latch_self_read_refuse/latch_self_read_a.sv.json"
load_design_sv2 latch_self_read_b from "Examples/system-verilog/sem2/latch_self_read_refuse/latch_self_read_b.sv.json"

def refused (p : PDesign) : Bool :=
  match LeanModels.Sv.Kernel.PDesign.instantiateE2 p [] (PDesign.surfaceFuel []) with
  | .unsupported msg => msg.startsWith "AlwaysLatch:self-read"
  | _ => false

#guard refused latch_self_read_a.pdesign
#guard refused latch_self_read_b.pdesign

end Examples.«system-verilog».sem2.latch_self_read_refuse.agree
