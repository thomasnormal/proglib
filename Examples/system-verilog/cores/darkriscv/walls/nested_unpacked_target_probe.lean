import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
set_option maxRecDepth 100000 in
load_design_sv2 nestedUnpackedTargetWall
  from "Examples/system-verilog/cores/darkriscv/walls/nested_unpacked_target.sv.json"
open LeanModels.Sv LeanModels.Sv.Kernel
def admission : String :=
  match PDesign.instantiateCoreMem nestedUnpackedTargetWall.pdesign [8, 2, 2] with
  | .ok _ => "admitted"
  | .timeout => "instantiate-timeout"
  | .unsupported msg => "instantiate-unsupported: " ++ msg
#guard admission ==
  "instantiate-unsupported: decl 'weights': nested unpacked memory rank outside E (UnpackedDecl:rank)"
