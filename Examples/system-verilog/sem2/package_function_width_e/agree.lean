import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.package_function_width_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 packageFunctionWidth from "Examples/system-verilog/sem2/package_function_width_e/package_function_width_e.sv.json"
private def outputs : Res (List String) := do
  let d ← packageFunctionWidth.e 1
  let rows ← runCoreMemRows d d.initial [[]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["0"]
end Examples.«system-verilog».sem2.package_function_width_e
