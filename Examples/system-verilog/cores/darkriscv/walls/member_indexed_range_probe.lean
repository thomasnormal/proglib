import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
set_option maxRecDepth 100000 in
load_design_sv2 memberIndexedRangeWall
  from "Examples/system-verilog/cores/darkriscv/walls/member_indexed_range.sv.json"
open LeanModels.Sv LeanModels.Sv.Kernel
def admission : String :=
  match PDesign.instantiateCoreMem memberIndexedRangeWall.pdesign [] with
  | .ok d =>
    match d.initialState with
    | .ok _ => "admitted"
    | .timeout => "initial-timeout"
    | .unsupported msg => "initial-unsupported: " ++ msg
  | .timeout => "instantiate-timeout"
  | .unsupported msg => "instantiate-unsupported: " ++ msg
#guard admission ==
  "initial-unsupported: unsupported expression 'RangeSelectExpression:member-indexed'"
