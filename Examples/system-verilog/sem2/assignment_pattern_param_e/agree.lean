import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.assignment_pattern_param_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 assignmentPattern
  from "Examples/system-verilog/sem2/assignment_pattern_param_e/assignment_pattern_param_e.sv.json"
def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem assignmentPattern.pdesign [0]
  let rows ← runCoreMemRows d d.initial
    [[("x", LVec.ofNat 4 0)], [("x", LVec.ofNat 4 10)],
     [("x", LVec.lit "zzzz")]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["0000", "1010", "xxxx"]
end Examples.«system-verilog».sem2.assignment_pattern_param_e
