import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.initial_quiet_assign
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 q from "Examples/system-verilog/sem2/initial_quiet_assign/initial_quiet_assign.sv.json"
#check q.pdesign
def d : Res CoreMemDesign := PDesign.instantiateE2 q.pdesign []
#guard !q.sem.hasUnsupported
#guard match d with
  | .ok e => e.hasComb = false && e.readmemh = []
  | _ => false
#guard match d with
  | .ok e => match e.initialState with
    | .ok st => CoreMemState.view e st != CoreMemState.view e e.initial
    | _ => false
  | _ => false
#guard match d with
  | .ok e => match e.initialState with
    | .ok st => (CoreMemState.view e st).lookup "y" == some (LVec.lit "1")
    | _ => false
  | _ => false
end Examples.«system-verilog».sem2.initial_quiet_assign
