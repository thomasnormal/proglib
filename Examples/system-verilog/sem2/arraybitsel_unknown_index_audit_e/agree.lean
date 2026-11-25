import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.arraybitsel_unknown_index_audit_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 arrayBitSelAudit from
  "Examples/system-verilog/sem2/arraybitsel_unknown_index_audit_e/arraybitsel_unknown_index_audit_e.sv.json"

def stimuli : List SvState :=
  [[("d", LVec.ofNat 1 0)], [("d", LVec.ofNat 1 1)],
   [("d", LVec.lit "x")], [("d", LVec.lit "z")]]

def outputs : Res (List String) := do
  let d ← arrayBitSelAudit.e 2
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard match arrayBitSelAudit.e 2 with
  | .ok d => d.memories.size == 1 && d.processes.size == 3 &&
      match d.processes[0]? with
      | some (CoreMemProc.assign (.arrayBitSel "mem" [_] _) _) => true
      | _ => false
  | _ => false

#guard outputs == .ok ["1", "1", "1", "1"]

end Examples.«system-verilog».sem2.arraybitsel_unknown_index_audit_e
