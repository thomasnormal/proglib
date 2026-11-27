import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.implicit_event_loop_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 implicit from
  "Examples/system-verilog/sem2/implicit_event_loop_e/implicit_event_loop.sv.json"

#guard match implicit.e 4 with | .ok d => CoreMemDesign.Structure d | _ => false

def stimulus : List SvState :=
  [[("a", LVec.ofNat 4 0)], [("a", LVec.ofNat 4 1)],
   [("a", LVec.ofNat 4 10)], [("a", LVec.lit "xxxx")],
   [("a", LVec.lit "zzzz")]]

def outputs : Res (List String) := do
  let d ← implicit.e 4
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#guard outputs == .ok ["0000", "0011", "0000", "0000", "0000"]

end Examples.«system-verilog».sem2.implicit_event_loop_e
