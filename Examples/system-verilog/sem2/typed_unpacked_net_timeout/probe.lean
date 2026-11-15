import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 typedUnpackedNet
  from "Examples/system-verilog/sem2/typed_unpacked_net_timeout/typed_unpacked_net.sv.json"
private def stimulus : List SvState := [
  [("x", LVec.ofNat 8 131)], [("x", LVec.ofNat 8 128)],
  [("x", LVec.ofNat 8 189)], [("x", LVec.ofNat 8 127)],
  [("x", LVec.lit "xxxxxxxx")], [("x", LVec.lit "zzzzzzzz")],
  [("x", LVec.ofNat 8 56)], [("x", LVec.ofNat 8 163)]]
def outputs : Res (List String) := do
  let d ← typedUnpackedNet.e
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["10000011", "10000000", "10111101", "01111111", "xxxxxxxx", "zzzzzzzz", "00111000", "10100011"]
