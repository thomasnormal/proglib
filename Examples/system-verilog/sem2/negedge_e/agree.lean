import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.negedge_e.agree
open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 negedge_e from "Examples/system-verilog/sem2/negedge_e/negedge_e.sv.json"

#guard (negedge_e.sem).clockAdmits

def outputs : Res (List String) := do
  let d ← PDesign.instantiateE2 negedge_e.pdesign [] (PDesign.surfaceFuel [])
  let rows ← runCoreMemRows d d.initial [
    [("clk", LVec.ofLogic .l1), ("d", LVec.ofLogic .l0)],
    [("clk", LVec.ofLogic .l0), ("d", LVec.ofLogic .l1)],
    [("clk", LVec.ofLogic .l1), ("d", LVec.ofLogic .l0)],
    [("clk", LVec.ofLogic .lx), ("d", LVec.ofLogic .l1)],
    [("clk", LVec.ofLogic .l0), ("d", LVec.ofLogic .l1)],
    [("clk", LVec.ofLogic .lz), ("d", LVec.ofLogic .l0)],
    [("clk", LVec.ofLogic .l1), ("d", LVec.ofLogic .l0)],
    [("clk", LVec.ofLogic .l0), ("d", LVec.ofLogic .l1)] ]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard outputs == .ok ["x", "1", "1", "1", "1", "1", "1", "1"]

end Examples.«system-verilog».sem2.negedge_e.agree
