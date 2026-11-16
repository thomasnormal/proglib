/-
Canonical E receipt for a source-order continuous-assignment chain.  IEEE
1800-2023 §§4.5 and 10.3 keep the active region live until all continuous
drivers are current; the source order `a = b; b = x; y = a` therefore settles
without requiring a topological source ordering.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.non_topological_assign.agree

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 topo from "Examples/system-verilog/sem2/non_topological_assign/non_topological_assign.sv.json"

#guard !topo.sem.hasUnsupported

def outputs : Res (List String) := do
  let d ← PDesign.instantiateE2 topo.pdesign [] (PDesign.surfaceFuel [])
  let rows ← runCoreMemRows d d.initial [
    [("x", LVec.ofNat 1 0)],
    [("x", LVec.ofNat 1 1)],
    [("x", LVec.ofLogic .lx)],
    [("x", LVec.ofLogic .lz)]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#guard outputs == .ok ["0", "1", "x", "z"]

end Examples.«system-verilog».sem2.non_topological_assign.agree
