import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.multi_step_lfsr_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 lfsr from "Examples/system-verilog/sem2/multi_step_lfsr_e/multi_step_lfsr_e.sv.json"
def stimuli : List SvState :=
  [[("clk",LVec.ofNat 1 0),("rstn",LVec.ofNat 1 0),("en",LVec.ofNat 1 0)],
   [("clk",LVec.ofNat 1 1),("rstn",LVec.ofNat 1 1),("en",LVec.ofNat 1 1)],
   [("clk",LVec.ofNat 1 0),("rstn",LVec.ofNat 1 1),("en",LVec.ofNat 1 1)],
   [("clk",LVec.ofNat 1 1),("rstn",LVec.ofNat 1 1),("en",LVec.ofNat 1 1)],
   [("clk",LVec.ofNat 1 0),("rstn",LVec.ofNat 1 1),("en",LVec.ofNat 1 1)],
   [("clk",LVec.ofNat 1 1),("rstn",LVec.ofNat 1 1),("en",LVec.ofNat 1 1)],
   [("clk",LVec.ofNat 1 0),("rstn",LVec.ofNat 1 1),("en",LVec.ofNat 1 1)],
   [("clk",LVec.ofNat 1 1),("rstn",LVec.ofNat 1 1),("en",LVec.ofNat 1 1)]]
def outputs : Res (List String) := do
  let d ← lfsr.e 8 184
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "state")
#guard match lfsr.e 8 184 with
  | .ok d => !d.processes.any (fun p => match p with | .unsupported _ _ => true | _ => false)
  | _ => false
#guard outputs == .ok ["00000001","01100100","01100100","10010011","10010011","00000011","00000011","10101100"]
end Examples.«system-verilog».sem2.multi_step_lfsr_e
