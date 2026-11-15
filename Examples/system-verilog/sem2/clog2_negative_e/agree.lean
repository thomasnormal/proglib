import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.clog2_negative_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 clog2Negative from "Examples/system-verilog/sem2/clog2_negative_e/clog2_negative_e.sv.json"
private def outputs : Res (List String) := do
  let d ← clog2Negative.e
  let rows ← runCoreMemRows d d.initial [[]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard match clog2Negative.e with
  | .ok d => d.memories.size == 0 && d.processes.size == 1
  | _ => false
#guard outputs == .ok ["100000"]
end Examples.«system-verilog».sem2.clog2_negative_e
