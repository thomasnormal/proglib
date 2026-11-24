import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.vector_remainder_param_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 vectorRemainder from "Examples/system-verilog/sem2/vector_remainder_param_e/vector_remainder_param_e.sv.json"
private def outputs : Res (List String) := do
  let d ← vectorRemainder.e 13
  let rows ← runCoreMemRows d d.initial [[]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["00000011"]
end Examples.«system-verilog».sem2.vector_remainder_param_e
