/-
Examples/system-verilog/sem2/clk_arst — ACCEPTED by the clock discipline (WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): an asynchronous active-low reset block (the reset is an input port, read as data inside the block, not a clock).
`load_design_sv2` loads it, and the instantiated design (`name.sem`) passes
`Design2.clockViolation` (the loader's check, run at the defaults and at every
probed point) with no loud process. The `harness/sv/cases2.json` row(s) named
`clk_arst` run it against Icarus 12 and the pinned Xcelium trace.

  clk_arst.sv      — the SystemVerilog source
  clk_arst.sv.json — generated envelope (extractors/sv/extract.py --top clk_arst)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.clk_arst.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 clk_arst from "Examples/system-verilog/sem2/clk_arst/clk_arst.sv.json"

#guard (clk_arst.sem 1).clockAdmits
#guard !(clk_arst.sem 1).hasUnsupported
#guard (clk_arst.sem 4).clockAdmits
#guard !(clk_arst.sem 4).hasUnsupported
#guard (clk_arst.sem 16).clockAdmits
#guard !(clk_arst.sem 16).hasUnsupported

def outputs : Res (List String) := do
  let d ← PDesign.instantiateE2 clk_arst.pdesign [4] (PDesign.surfaceFuel [4])
  let rows ← runCoreMemRows d d.initial [
    [("clk", LVec.ofNat 1 0), ("rst_n", LVec.ofNat 1 1), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 4 1)],
    [("clk", LVec.ofNat 1 0), ("rst_n", LVec.ofNat 1 0), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 4 1)],
    [("clk", LVec.ofNat 1 0), ("rst_n", LVec.ofNat 1 1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 6)],
    [("clk", LVec.ofNat 1 1), ("rst_n", LVec.ofNat 1 1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 6)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .lx), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 15)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 15)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .lz), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 2)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofLogic .l1), ("d", LVec.ofNat 4 2)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .l0), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 2)],
    [("clk", LVec.ofLogic .l0), ("rst_n", LVec.ofLogic .l0), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 2)],
    [("clk", LVec.ofLogic .l0), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 3)],
    [("clk", LVec.ofLogic .lx), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 3)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 4)],
    [("clk", LVec.ofLogic .l0), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 4)],
    [("clk", LVec.ofLogic .lz), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 5)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 6)],
    [("clk", LVec.ofLogic .lx), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 7)],
    [("clk", LVec.ofLogic .lz), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 7)],
    [("clk", LVec.ofLogic .l1), ("rst_n", LVec.ofLogic .l1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 7)] ]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard outputs == .ok ["xxxx", "0000", "0000", "0110", "1111", "1111", "0010", "0010", "0000", "0000", "0000", "0011", "0100", "0100", "0101", "0110", "0110", "0110", "0111"]

end Examples.«system-verilog».sem2.clk_arst.agree
