import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.clk_two.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 clk_two from "Examples/system-verilog/sem2/clk_two/clk_two.sv.json"

/-! The ordinary run2 runner retains the `Clock:multiple` boundary, while
canonical E's source-shaped step evaluates each input clock independently. -/
private def twoClock : Design2 where
  name := "two_clock"
  decls := #[
    { name := "clk1", width := 1, isInput := true },
    { name := "clk2", width := 1, isInput := true },
    { name := "d", width := 1, isInput := true },
    { name := "a", width := 1 }, { name := "b", width := 1 }]
  processes := #[
    .alwaysFF "clk1" (.nbaAssign (.ident "a") (.ident "d")),
    .alwaysFF "clk2" (.nbaAssign (.ident "b") (.ident "a"))]

#guard twoClock.clockNames.length == 2
#guard twoClock.clockReport.isSome


def outputs : Res (List (String × String)) := do
  let d ← PDesign.instantiateE2 clk_two.pdesign [] (PDesign.surfaceFuel [])
  let rows ← runCoreMemRows d d.initial [
    [("clk1", LVec.ofLogic .l0), ("clk2", LVec.ofLogic .l0), ("d", LVec.ofLogic .l0)],
    [("clk1", LVec.ofLogic .l1), ("clk2", LVec.ofLogic .l0), ("d", LVec.ofLogic .l1)],
    [("clk1", LVec.ofLogic .l0), ("clk2", LVec.ofLogic .l1), ("d", LVec.ofLogic .l1)],
    [("clk1", LVec.ofLogic .l1), ("clk2", LVec.ofLogic .l0), ("d", LVec.ofLogic .lx)],
    [("clk1", LVec.ofLogic .l0), ("clk2", LVec.ofLogic .lx), ("d", LVec.ofLogic .lz)],
    [("clk1", LVec.ofLogic .lz), ("clk2", LVec.ofLogic .l0), ("d", LVec.ofLogic .l1)],
    [("clk1", LVec.ofLogic .l0), ("clk2", LVec.ofLogic .l0), ("d", LVec.ofLogic .l0)],
    [("clk1", LVec.ofLogic .l1), ("clk2", LVec.ofLogic .l1), ("d", LVec.ofLogic .l1)] ]
  .ok (rows.map fun s =>
    (SvState.showSignal (CoreMemState.view d s) "a",
     SvState.showSignal (CoreMemState.view d s) "b"))

#guard outputs == .ok [("x", "x"), ("1", "x"), ("1", "1"), ("x", "1"),
  ("x", "x"), ("1", "x"), ("1", "x"), ("1", "1")]

end Examples.«system-verilog».sem2.clk_two.agree
