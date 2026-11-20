/-
Canonical-E admission receipt for a literal delay inside an initial
assertion-only diagnostic check. The delay remains source-shaped and is
accepted only by the elaboration-check adapter under IEEE 1800-2023 §§9.4 and
9.6.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.initial_delay_check_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 initialDelayCheck
  from "Examples/system-verilog/sem2/initial_delay_check_e/initial_delay_check_e.sv.json"

#guard match initialDelayCheck.pdesign.processes with
  | [.assign "y" (.ident "x"),
     .initial (.block [
       .unsupported "TimedStatement:DelayControl" "#1;",
       .ifStmt (.binary .cne (.ident "y") (.ident "x"))
         (.unsupported "SysCall:$error" _) none])] => true
  | _ => false


def trace : Res (List String) := do
  let d ← initialDelayCheck.e
  let st ← d.initialState
  let rows ← runCoreMemRows d st [[], [], [], [], [], [], [], []]
  pure (rows.map (fun s => SvState.showSignal (CoreMemState.view d s) "y"))

#guard trace == .ok ["x", "x", "x", "x", "x", "x", "x", "x"]

end Examples.«system-verilog».sem2.initial_delay_check_e
