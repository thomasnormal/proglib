import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.initial_parameter_check_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 initialParameterCheck from
  "Examples/system-verilog/sem2/initial_parameter_check_e/initial_parameter_check_e.sv.json"

def trace (n : Nat) : Res (List String) := do
  let d ← initialParameterCheck.e n
  let s ← d.initialState
  let rows ← runCoreMemRows d s [[], [], [], [], [], [], [], []]
  pure (rows.map (fun s => SvState.showSignal (CoreMemState.view d s) "y"))

#guard trace 1 == .ok ["1", "1", "1", "1", "1", "1", "1", "1"]
#guard trace 0 == .ok ["0", "0", "0", "0", "0", "0", "0", "0"]
end Examples.«system-verilog».sem2.initial_parameter_check_e
