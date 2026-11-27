/-
Step 10 source evidence for a mixed E slot: two source-shaped `always_comb`
processes sit beside one NBA-only `always_ff`. Canonical E settles both comb
stages before and after the edge commit, preserving the source process shapes.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.mixed_core_step10.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 mixedCoreStep10
  from "Examples/system-verilog/sem2/mixed_core_step10/mixed_core_step10.sv.json"

#guard mixedCoreStep10.pdesign.others == []
#guard !mixedCoreStep10.sem.hasUnsupported
#guard mixedCoreStep10.sem.ffMixedProfileB == true
#guard mixedCoreStep10.sem.ffOnlyProfileB == false
#guard mixedCoreStep10.sem.processes.size == 3
#guard match mixedCoreStep10.sem.processes.toList with
  | [.alwaysComb _, .alwaysComb _, .alwaysFF "clk" _] => true
  | _ => false

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem mixedCoreStep10.pdesign []
  let st ← d.initialState
  let rows ← runCoreMemRows d st [
    [("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 3)],
    [("clk", LVec.ofNat 1 1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 3)],
    [("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 4 10)],
    [("clk", LVec.ofNat 1 1), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 4 10)],
    [("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 1), ("d", LVec.lit "x101")],
    [("clk", LVec.ofNat 1 1), ("en", LVec.ofNat 1 1), ("d", LVec.lit "x101")],
    [("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 0), ("d", LVec.lit "z000")],
    [("clk", LVec.ofNat 1 1), ("en", LVec.ofNat 1 0), ("d", LVec.lit "z000")]]
  .ok (([SvState.showSignal (CoreMemState.view d st) "q" ++ " " ++
      SvState.showSignal (CoreMemState.view d st) "n" ++ " " ++
      SvState.showSignal (CoreMemState.view d st) "post"] ++
    rows.map fun s =>
      SvState.showSignal (CoreMemState.view d s) "q" ++ " " ++
      SvState.showSignal (CoreMemState.view d s) "n" ++ " " ++
      SvState.showSignal (CoreMemState.view d s) "post"))

#guard outputs == .ok [
  "xxxx xxxx xxxx", "xxxx xxxx xxxx", "0011 0000 0001", "0011 1001 1010",
  "0101 1111 0000", "0101 x000 xxxx", "x101 x000 xxxx", "x101 x101 xxxx",
  "x111 x111 xxxx"]

end Examples.«system-verilog».sem2.mixed_core_step10.agree
