import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.bits_package_parameter_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 bitsPackage from "Examples/system-verilog/sem2/bits_package_parameter_e/bits_package_parameter_e.sv.json"
private def outputs : Res (List String) := do
  let d ← bitsPackage.e
  let rows ← runCoreMemRows d d.initial [[]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard match bitsPackage.e with
  | .ok d => d.memories.size == 0 && d.processes.size == 1
  | _ => false
#guard outputs == .ok ["00001000"]
end Examples.«system-verilog».sem2.bits_package_parameter_e
