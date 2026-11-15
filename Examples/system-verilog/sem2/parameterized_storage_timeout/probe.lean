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
def outputs (n : Nat) : Res (List String) := do
  let d ← parameterizedStorage.e n
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs 1 == .ok ["00000000", "00000001", "00010000", "10100101", "11111111", "xxxxxxxx", "zzzzzzzz", "01011010"]
#guard outputs 2 == .ok ["00000000", "00000001", "00010000", "10100101", "11111111", "xxxxxxxx", "zzzzzzzz", "01011010"]
#eval outputs 1
#eval outputs 2
