import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.clocked_reset_guard_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 guard from "Examples/system-verilog/sem2/clocked_reset_guard_e/clocked_reset_guard_e.sv.json"
#guard !guard.sem.hasUnsupported
#guard (guard.sem).clockAdmits
def outputs : Res (List String) := do
  let d ← PDesign.instantiateE2 guard.pdesign [] (PDesign.surfaceFuel [])
  let rows ← runCoreMemRows d d.initial [
    [("clk", LVec.ofLogic .l0), ("rst_n", LVec.ofLogic .l0), ("d", LVec.ofLogic .l0)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .l0), ("d", LVec.ofLogic .l1)],
    [("clk", LVec.ofLogic .l0), ("rst_n", LVec.ofLogic .l1), ("d", LVec.ofLogic .l1)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .l1), ("d", LVec.ofLogic .lx)],
    [("clk", LVec.ofLogic .l0), ("rst_n", LVec.ofLogic .lx), ("d", LVec.ofLogic .lz)],
    [("clk", LVec.ofLogic .lx), ("rst_n", LVec.ofLogic .l0), ("d", LVec.ofLogic .l1)],
    [("clk", LVec.ofLogic .l0), ("rst_n", LVec.ofLogic .lz), ("d", LVec.ofLogic .l0)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .l0), ("d", LVec.ofLogic .l0)]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")
#guard outputs == .ok ["0", "0", "0", "x", "z", "0", "0", "0"]
end Examples.«system-verilog».sem2.clocked_reset_guard_e.agree
