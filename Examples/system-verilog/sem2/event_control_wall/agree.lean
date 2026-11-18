import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.event_control_wall.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 event_control_wall from
  "Examples/system-verilog/sem2/event_control_wall/event_control_wall.sv.json"
def outputs : Res (List String) := do
  let d ← PDesign.instantiateE2 event_control_wall.pdesign [] (PDesign.surfaceFuel [])
  let rows ← runCoreMemRows d d.initial [
    [("en", LVec.ofNat 1 0), ("d", LVec.ofNat 1 0)],
    [("en", LVec.ofNat 1 0), ("d", LVec.ofNat 1 1)],
    [("en", LVec.ofNat 1 1), ("d", LVec.ofNat 1 1)],
    [("en", LVec.ofNat 1 0), ("d", LVec.ofNat 1 0)]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")
#guard outputs == .ok ["0", "0", "1", "0"]
end Examples.«system-verilog».sem2.event_control_wall.agree
