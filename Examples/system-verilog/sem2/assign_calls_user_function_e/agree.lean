import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.assign_calls_user_function_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 assignCallsUserFunction from "Examples/system-verilog/sem2/assign_calls_user_function_e/assign_calls_user_function_e.sv.json"
private def rows : Res (List String) := do
  let d ← assignCallsUserFunction.e
  let states := [[("a", LVec.ofNat 4 0)], [("a", LVec.ofNat 4 5)], [("a", LVec.xVec 4)]]
  let rs ← runCoreMemRows d d.initial states
  .ok (rs.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard rows == .ok ["1111", "1010", "xxxx"]
end Examples.«system-verilog».sem2.assign_calls_user_function_e
