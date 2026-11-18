import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 reactive_backward
  from "Examples/system-verilog/cores/picorv32/walls/reactive_backward.sv.json"

#guard match reactive_backward.e with
  | .ok d => match d.initialState with
    | .ok st => match runCoreMemRows d st
        [[("a", LVec.ofNat 1 0)], [("a", LVec.ofNat 1 1)]] with
      | .ok states => states.map (fun s =>
          (SvState.showSignal (CoreMemState.view d s) "a",
           SvState.showSignal (CoreMemState.view d s) "t",
           SvState.showSignal (CoreMemState.view d s) "y")) ==
        [("0", "0", "0"), ("1", "1", "1")]
      | _ => false
    | _ => false
  | _ => false
