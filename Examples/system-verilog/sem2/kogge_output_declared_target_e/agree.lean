import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.kogge_output_declared_target_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 kogge from "Examples/system-verilog/sem2/kogge_output_declared_target_e/kogge_output_declared_target_e.sv.json"
def stimulus : List SvState :=
  [[("a", LVec.ofNat 4 0)], [("a", LVec.ofNat 4 3)],
   [("a", LVec.lit "xxxx")], [("a", LVec.lit "zzzz")]]
def outputs : Res (List String) := do
  let d ← kogge.e 4
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "o_sum")
#guard match kogge.e 4 with
  | .ok d => d.processes.size == 5
  | _ => false
#guard outputs == .ok ["0000", "0011", "xxxx", "zzzz"]
#print axioms CoreMemDesign.step
end Examples.«system-verilog».sem2.kogge_output_declared_target_e
