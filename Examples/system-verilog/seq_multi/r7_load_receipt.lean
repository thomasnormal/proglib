import LeanModels.Sv.Ingest2
import LeanModels.Sv.Sem2Run

open LeanModels.Sv LeanModels.Sv.Kernel

/-!
# R7: multi-clock loading keeps the design term

The loader exposes the literal envelope families, including canonical-E `.e`,
for a design with several input clocks.  The one-clock `run2` view remains a
separate derived route and refuses `Clock:multiple` before stepping it.
-/

load_design_sv2 two_reg_r7 from "Examples/system-verilog/seq_multi/two_reg/two_reg.sv.json"
load_design_sv2 sync2_r7 from "Examples/system-verilog/seq_multi/sync2/sync2.sv.json"

#guard (match two_reg_r7.e 4 with | .ok _ => true | _ => false)
#guard (match sync2_r7.e with | .ok _ => true | _ => false)
#guard (match run2 (two_reg_r7.sem 4) σ_src 64 [] with
  | .unsupported msg => msg.startsWith "Clock:multiple"
  | _ => false)
#guard (match run2 sync2_r7.sem σ_src 64 [] with
  | .unsupported msg => msg.startsWith "Clock:multiple"
  | _ => false)
