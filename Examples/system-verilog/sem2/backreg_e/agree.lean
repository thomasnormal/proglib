import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.backreg_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 backregE from
  "Examples/system-verilog/sem2/backreg_e/backreg_e.sv.json"

/-! Scalar continuous assignments use the scalar quiescence executor.  The
memory-cell topology refusal is checked separately after generate expansion.
This source-order chain therefore runs to the same settled values as the
pinned simulators. -/
#guard match backregE.e with
  | .ok _ => true
  | _ => false

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem backregE.pdesign []
  let rows ← runCoreMemRows d d.initial [
    [("clk", LVec.ofNat 1 0), ("x", LVec.ofNat 4 5)],
    [("clk", LVec.ofNat 1 1), ("x", LVec.ofNat 4 5)],
    [("clk", LVec.ofNat 1 0), ("x", LVec.ofNat 4 5)],
    [("clk", LVec.ofNat 1 0), ("x", LVec.ofNat 4 9)],
    [("clk", LVec.ofNat 1 1), ("x", LVec.ofNat 4 9)],
    [("clk", LVec.ofNat 1 0), ("x", LVec.ofNat 4 9)],
    [("clk", LVec.ofNat 1 0), ("x", LVec.ofLogic .lx)],
    [("clk", LVec.ofNat 1 0), ("x", LVec.ofLogic .lz)] ]
  pure (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "a")

#guard outputs == .ok ["xxxx", "0101", "0101", "0101", "1001", "1001", "1001", "1001"]
end Examples.«system-verilog».sem2.backreg_e
