import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# DarkRISCV's loaded clocked profile

This theorem is about the pinned, unmodified DarkRISCV envelope.  The
clocked-stage route instantiates the real design, checks every process and
driver against `SeqProfileI`, and discharges the clocked obligations.  It is
the first kernel-checked fact about this loaded core itself.  No instruction
invariant or ISA refinement premise is assumed here.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».cores.darkriscv

load_design_sv2 dark from "Examples/system-verilog/cores/darkriscv/darkriscv.sv.json"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem dark_structure : SeqDesignI (dark.e 0) := by
  sv_structure

#print axioms dark_structure

end Examples.«system-verilog».cores.darkriscv
