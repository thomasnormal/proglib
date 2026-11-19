import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 fc from "Examples/system-verilog/cores/darkriscv/walls/function_call_expression.sv.json"
def row (v : Nat) : SvState := [("in", LVec.ofNat 1 v)]
#eval match PDesign.instantiateCoreMem fc.pdesign [] with
  | .ok d => match d.initialState with
    | .ok st => match d.step st (row 1) with
      | .ok _ => "canonical-step-ok"
      | .timeout => "canonical-step-timeout"
      | .unsupported m => "canonical-step-unsupported: " ++ m
    | .timeout => "initial-timeout"
    | .unsupported m => "initial-unsupported: " ++ m
  | .timeout => "instantiate-timeout"
  | .unsupported m => "instantiate-unsupported: " ++ m
