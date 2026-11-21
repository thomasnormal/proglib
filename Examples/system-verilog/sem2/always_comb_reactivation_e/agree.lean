/-
Canonical-E refusal receipt for IEEE 1800-2023 §9.2.2.2.1. An always_comb
process is not reactivated by a variable written by that same process. The
canonical executor previously iterated its startup pass and could expose the
newly written value, while event-driven simulators retain the previous value.
The source-shaped self-read body is therefore refused instead of assigning one
of those orderings to E.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.always_comb_reactivation_e

open LeanModels.Sv LeanModels.Sv.Kernel

def check : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/sem2/rbw_comb/rbw_comb.sv.json"
  let pd ← match loadPDesignString text with
    | .ok x => pure x
    | .error msg => throw (IO.userError msg)
  match PDesign.instantiateE2 pd [] with
  | .unsupported msg =>
      unless msg.startsWith "AlwaysComb:self-read" do
        throw (IO.userError s!"unexpected refusal: {msg}")
      IO.println "canonical E: AlwaysComb:self-read refusal"
  | .ok _ => throw (IO.userError "canonical E admitted an always_comb self-read")
  | .timeout => throw (IO.userError "canonical E timeout")

#eval check

end Examples.«system-verilog».sem2.always_comb_reactivation_e
