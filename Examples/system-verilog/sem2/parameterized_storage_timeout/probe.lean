import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 parameterizedStorage
  from "Examples/system-verilog/sem2/parameterized_storage_timeout/parameterized_storage_structure.sv.json"
private def stimulus : List SvState := [
  [("x", LVec.ofNat 8 0)], [("x", LVec.ofNat 8 1)],
  [("x", LVec.ofNat 8 16)], [("x", LVec.ofNat 8 165)],
  [("x", LVec.ofNat 8 255)], [("x", LVec.lit "xxxxxxxx")],
  [("x", LVec.lit "zzzzzzzz")], [("x", LVec.ofNat 8 90)]]
#guard match parameterizedStorage.e 1 with | .ok _ => true | _ => false
#guard match parameterizedStorage.e 2 with | .ok _ => true | _ => false
