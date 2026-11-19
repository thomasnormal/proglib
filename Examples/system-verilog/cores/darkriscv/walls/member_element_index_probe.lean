import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

set_option maxRecDepth 100000 in
load_design_sv2 memberElementIndexWall
  from "Examples/system-verilog/sem2/member_elem_loud/member_elem_loud.sv.json"

open LeanModels.Sv
open LeanModels.Sv.Kernel

def admission : String :=
  match PDesign.instantiateCoreMem memberElementIndexWall.pdesign [] with
  | .ok d =>
    match d.initialState with
    | .ok _ => "admitted"
    | .timeout => "initial-timeout"
    | .unsupported msg => "initial-unsupported: " ++ msg
  | .timeout => "instantiate-timeout"
  | .unsupported msg => "instantiate-unsupported: " ++ msg

#guard admission ==
  "initial-unsupported: unsupported expression 'ElementSelectExpression:member-index'"
