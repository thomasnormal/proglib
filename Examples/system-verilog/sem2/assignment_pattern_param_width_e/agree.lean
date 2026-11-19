import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.assignment_pattern_param_width_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 assignmentPatternParamWidth
  from "Examples/system-verilog/sem2/assignment_pattern_param_width_e/assignment_pattern_param_width_e.sv.json"
def rows (w : Int) : Res (List String) := do
  let (point, args) ← match assignmentPatternParamWidth.pdesign.atPoint [some w, none] with
    | .ok value => .ok value
    | .error message => .unsupported message
  let d ← PDesign.instantiateCoreMem point args
  let rows ← runCoreMemRows d d.initial
    [[("x", LVec.ofNat w.toNat 0)], [("x", LVec.ofNat w.toNat 1)],
     [("x", LVec.ofNat w.toNat ((2^w.toNat)-1))]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard rows 2 == .ok ["00", "01", "11"]
#guard rows 4 == .ok ["0000", "0001", "1111"]
end Examples.«system-verilog».sem2.assignment_pattern_param_width_e.agree
