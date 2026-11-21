import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.duplicate_active_scope_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 duplicateActiveScope from
  "Examples/system-verilog/sem2/duplicate_active_scope_e/duplicate_active_scope_e.sv.json"
def stimulus : List SvState :=
  [[("x", LVec.ofNat 2 0)], [("x", LVec.ofNat 2 3)],
   [("x", LVec.lit "xx")], [("x", LVec.lit "zz")]]
def outputs : Res (List String) := do
  let d ← duplicateActiveScope.e 2
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard match duplicateActiveScope.e 2 with
  | .ok d => d.scalar.decls.size == 4 && d.processes.size == 4
  | _ => false
#guard outputs == .ok ["00", "11", "xx", "zz"]
#print axioms CoreMemDesign.step
end Examples.«system-verilog».sem2.duplicate_active_scope_e
