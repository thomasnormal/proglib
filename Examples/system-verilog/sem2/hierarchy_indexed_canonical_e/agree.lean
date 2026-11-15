import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.hierarchy_indexed_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 hierarchyE from "Examples/system-verilog/sem2/hierarchy_indexed_canonical_e/hierarchy_indexed_canonical_e.sv.json"
def outputs : Res (List String) := do
  let d ← hierarchyE.e 8
  let rows ← runCoreMemRows d d.initial [
    [("a", LVec.lit "00000000")], [("a", LVec.lit "00000001")],
    [("a", LVec.lit "10100101")], [("a", LVec.lit "11110000")],
    [("a", LVec.lit "xxxxxxxx")]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["00000000", "00000001", "10100101", "11110000", "xxxxxxxx"]
#guard match hierarchyE.e 8 with
  | .ok d => decide d.EquationGate
  | _ => false
end Examples.«system-verilog».sem2.hierarchy_indexed_canonical_e
