import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E refusal for the IEEE 1800-2023 §4.7 preemption wall. -/

namespace Examples.«system-verilog».sem2.preempt_block_refuse

open LeanModels.Sv LeanModels.Sv.Kernel

def check : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/sem2/preempt_block_refuse/preempt_block_refuse.sv.json"
  let pd ← match loadPDesignString text with
    | .ok x => pure x
    | .error msg => throw (IO.userError msg)
  match PDesign.instantiateE2 pd [] with
  | .unsupported msg =>
      unless msg.startsWith "Schedule:preemptive" do
        throw (IO.userError s!"unexpected canonical-E refusal: {msg}")
  | .timeout => throw (IO.userError "canonical E timed out")
  | .ok _ => throw (IO.userError "canonical E admitted a preemptive blocking race")
  IO.println "canonical E: multi-write blocking preemption shape REFUSED"

#eval check

end Examples.«system-verilog».sem2.preempt_block_refuse
