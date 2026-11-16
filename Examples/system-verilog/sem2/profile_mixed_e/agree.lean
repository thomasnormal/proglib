import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.profile_mixed_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 profileMixedE from
  "Examples/system-verilog/sem2/profile_mixed_e/profile_mixed_e.sv.json"
#guard profileMixedE.pdesign.others == []
#guard profileMixedE.sem.ffResetProfileB
#guard profileMixedE.sem.ffMixedProfileB
#guard !profileMixedE.sem.ffOnlyProfileB
#guard match profileMixedE.sem.processes.toList with
  | [.alwaysFFR "clk" "rst" _ _, .assign (.ident "y") (.ident "q")] => true
  | _ => false

/-! The canonical E memory elaborator admits the same source-shaped edge and
continuous processes together.  This is the mixed-process route used by the
ordinary differential receipt; E-core-1's edge-only profile remains a
separate, deliberately narrower interface. -/
def outputs : Res (List String) := do
  let d ← profileMixedE.e
  let rows ← runCoreMemRows d d.initial [
    [("clk", LVec.ofNat 1 0), ("rst", LVec.ofNat 1 0), ("d", LVec.ofNat 1 0)],
    [("clk", LVec.ofNat 1 0), ("rst", LVec.ofNat 1 1), ("d", LVec.ofNat 1 1)],
    [("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 1), ("d", LVec.ofNat 1 1)],
    [("clk", LVec.ofNat 1 0), ("rst", LVec.ofNat 1 1), ("d", LVec.ofNat 1 0)],
    [("clk", LVec.lit "x"), ("rst", LVec.ofNat 1 1), ("d", LVec.lit "x")],
    [("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 1), ("d", LVec.lit "z")],
    [("clk", LVec.ofNat 1 0), ("rst", LVec.ofNat 1 1), ("d", LVec.ofNat 1 1)],
    [("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 1), ("d", LVec.ofNat 1 0)]]
  .ok (rows.map fun s =>
    SvState.showSignal (CoreMemState.view d s) "q" ++ " " ++
    SvState.showSignal (CoreMemState.view d s) "y")

#guard match profileMixedE.e with
  | .ok d => d.processes.size == 2
  | _ => false
#guard outputs == .ok ["0 0", "0 0", "1 1", "1 1", "x x", "z z", "z z", "0 0"]
end Examples.«system-verilog».sem2.profile_mixed_e
