import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.bits_type_alias_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 bitsTypeAlias from "Examples/system-verilog/sem2/bits_type_alias_e/bits_type_alias_e.sv.json"
private def outputs : Res (List String) := do
  let d ← bitsTypeAlias.e
  let rows ← runCoreMemRows d d.initial [[]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["000000001100"]
end Examples.«system-verilog».sem2.bits_type_alias_e
