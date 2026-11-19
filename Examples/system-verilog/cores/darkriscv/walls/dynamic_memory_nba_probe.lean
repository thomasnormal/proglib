import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
set_option maxRecDepth 100000 in
load_design_sv2 dm from "Examples/system-verilog/cores/darkriscv/walls/dynamic_memory_nba.sv.json"
open LeanModels.Sv LeanModels.Sv.Kernel
private def stim (clk rst dptr data : Nat) : SvState :=
  [("CLK", LVec.ofNat 1 clk), ("RES", LVec.ofNat 1 rst),
   ("DPTR", LVec.ofNat 2 dptr), ("DATA", LVec.ofNat 32 data)]
#guard match PDesign.instantiateCoreMem dm.pdesign [] with
  | .ok d => match d.initialState with
    | .ok st0 => match d.step st0 (stim 0 1 0 0) with
      | .ok st1 => match d.step st1 (stim 1 0 2 0xA5) with
        | .ok st2 => match d.step st2 (stim 0 0 2 0xA5) with
          | .ok st3 => match d.step st3 (stim 1 0 1 0x5A) with
            | .ok st4 =>
              MemState.read st4.memory "REGS" 2 == some (LVec.ofNat 32 0xA5) &&
              MemState.read st4.memory "REGS" 1 == some (LVec.ofNat 32 0x5A)
            | _ => false
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false
