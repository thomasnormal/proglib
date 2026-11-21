import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-!
Canonical-E receipt for a continuous-assignment chain feeding `always_comb`.
IEEE 1800-2023 §§4.5, 9.2.2.2, and 10.3 require the active region to settle
continuous drivers before the combinational process observes its input.
-/

namespace Examples.«system-verilog».sem2.time_zero_comb_quiesce_e

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 timeZeroCombQuiesce
  from "Examples/system-verilog/sem2/time_zero_comb_quiesce_e/time_zero_comb_quiesce_e.sv.json"

def initialOutputs : Res (String × String × String) := do
  let d ← PDesign.instantiateCoreMem timeZeroCombQuiesce.pdesign []
  let s ← d.initialState
  pure (SvState.showSignal (CoreMemState.view d s) "a",
    SvState.showSignal (CoreMemState.view d s) "b",
    SvState.showSignal (CoreMemState.view d s) "y")

#guard match initialOutputs with
  | .ok ("1", "1", "1") => true
  | _ => false

#print axioms CoreMemDesign.initialState

end Examples.«system-verilog».sem2.time_zero_comb_quiesce_e
