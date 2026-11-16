/- Canonical-E receipt for a runtime initial assignment (§9.6). -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.initial_storage_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 initial_storage_e from "Examples/system-verilog/sem2/initial_storage_e/initial_storage_e.sv.json"
def outputs : Res (List String) := do
  let d ← PDesign.instantiateE2 initial_storage_e.pdesign [] (PDesign.surfaceFuel [])
  let s ← d.initialState
  let rows ← runCoreMemRows d s [[], []]
  .ok (rows.map fun st => SvState.showSignal (CoreMemState.view d st) "q")
#guard outputs == .ok ["0", "0"]
end Examples.«system-verilog».sem2.initial_storage_e.agree
