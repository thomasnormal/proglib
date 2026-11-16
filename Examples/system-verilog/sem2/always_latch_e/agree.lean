/- Canonical-E receipt for source-shaped `always_latch` (§9.2.2.3). -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.always_latch_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 always_latch_e from "Examples/system-verilog/sem2/always_latch_e/always_latch_e.sv.json"
def outputs : Res (List String) := do
  let d ← PDesign.instantiateE2 always_latch_e.pdesign [] (PDesign.surfaceFuel [])
  let rows ← runCoreMemRows d d.initial [
    [("en", LVec.ofNat 1 0), ("d", LVec.ofNat 1 1)],
    [("en", LVec.ofNat 1 1), ("d", LVec.ofNat 1 1)],
    [("en", LVec.ofNat 1 0), ("d", LVec.ofNat 1 0)],
    [("en", LVec.ofLogic .lx), ("d", LVec.ofNat 1 0)],
    [("en", LVec.ofLogic .lz), ("d", LVec.ofNat 1 0)],
    [("en", LVec.ofNat 1 1), ("d", LVec.ofNat 1 0)]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")
#guard outputs == .ok ["x", "1", "1", "1", "1", "0"]
end Examples.«system-verilog».sem2.always_latch_e.agree
