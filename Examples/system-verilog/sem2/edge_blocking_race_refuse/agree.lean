/- Canonical E refusal for same-edge blocking read/write races. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.edge_blocking_race_refuse
open LeanModels.Sv LeanModels.Sv.Kernel

def refused (path : String) : IO Bool := do
  let text ← IO.FS.readFile s!"Examples/system-verilog/sem2/edge_blocking_race_refuse/{path}.sv.json"
  let pd ← match loadPDesignString text with
    | .ok x => pure x
    | .error e => throw (IO.userError e)
  pure (match PDesign.instantiateE2 pd [] with
    | .unsupported msg => msg.contains "Event:edge-blocking-race" && msg.contains "4.7/10.4.1"
    | _ => false)

#eval do
  unless (← refused "edge_blocking_race_refuse") && (← refused "edge_blocking_race_refuse2") do
    throw (IO.userError "same-edge blocking race was admitted")

end Examples.«system-verilog».sem2.edge_blocking_race_refuse
