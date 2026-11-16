import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.clog2_guard_negative_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 clog2GuardNegative from
  "Examples/system-verilog/sem2/clog2_guard_negative_e/clog2_guard_negative_e.sv.json"

#guard (evalGenGuard32 { nvals := [("N", (-1, 32, true))] }
  (.sysCall .clog2 (.paramRef "N" none))).toOption == some 32

def outputAt (n : Int) : Res String := do
  let d ← PDesign.instantiateCoreMem clog2GuardNegative.pdesign [n]
  let rows ← runCoreMemRows d d.initial [[]]
  match rows with
  | [s] => .ok (SvState.showSignal (CoreMemState.view d s) "y")
  | _ => .unsupported "unexpected row count"

#guard outputAt (-1) == .ok "1"
#guard outputAt 0 == .ok "0"
#print axioms outputAt
end Examples.«system-verilog».sem2.clog2_guard_negative_e
