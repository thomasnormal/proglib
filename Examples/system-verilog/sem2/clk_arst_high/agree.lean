import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.clk_arst_high.agree
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 clk_arst_high from "Examples/system-verilog/sem2/clk_arst_high/clk_arst_high.sv.json"
#guard !(clk_arst_high.sem 4).hasUnsupported

def outputs : Res (List String) := do
  let d ← PDesign.instantiateE2 clk_arst_high.pdesign [4] (PDesign.surfaceFuel [4])
  let rows ← runCoreMemRows d d.initial [
    [("clk", LVec.ofNat 1 0), ("rst", LVec.ofNat 1 0), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 4 1)],
    [("clk", LVec.ofNat 1 0), ("rst", LVec.ofNat 1 1), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 4 1)],
    [("clk", LVec.ofNat 1 0), ("rst", LVec.ofNat 1 0), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 6)],
    [("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 0), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 6)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .lx), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 15)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 15)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .lz), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 2)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 2)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .l1), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 2)],
    [("clk", LVec.ofLogic .l0), ("rst", LVec.ofLogic .l1), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 2)],
    [("clk", LVec.ofLogic .l0), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 2)],
    [("clk", LVec.ofLogic .lx), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 3)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 4)],
    [("clk", LVec.ofLogic .l0), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 4)],
    [("clk", LVec.ofLogic .lz), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 5)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 6)],
    [("clk", LVec.ofLogic .lx), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 7)],
    [("clk", LVec.ofLogic .lz), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 7)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .l0), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 7)] ]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard outputs == .ok ["xxxx", "0000", "0000", "0110", "1111", "1111", "0010", "0010", "0000", "0000", "0000", "0011", "0100", "0100", "0101", "0110", "0110", "0110", "0111"]
end Examples.«system-verilog».sem2.clk_arst_high.agree
