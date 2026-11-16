/- Canonical-E receipt for an internally generated clock (§4.4, §9.4.2).
The ordinary Design2 loader keeps its Clock:source refusal; this receipt calls
PDesign.instantiateE2 directly, the canonical E definition. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.internal_clock_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel

def outputs : IO (Res (List String)) := do
  let text ← IO.FS.readFile "Examples/system-verilog/sem2/internal_clock_e/internal_clock_e.sv.json"
  let pd ← match loadPDesignString text with | .ok p => pure p | .error e => throw (IO.userError e)
  let d ← match PDesign.instantiateE2 pd [] (PDesign.surfaceFuel []) with | .ok d => pure d | .timeout => throw (IO.userError "instantiate timeout") | .unsupported e => throw (IO.userError e)
  let rows ← match runCoreMemRows d d.initial [
    [("enable", LVec.ofLogic .l0), ("data", LVec.ofLogic .l0)],
    [("enable", LVec.ofLogic .l1), ("data", LVec.ofLogic .l1)],
    [("enable", LVec.ofLogic .lx), ("data", LVec.ofLogic .l0)],
    [("enable", LVec.ofLogic .lz), ("data", LVec.ofLogic .l1)],
    [("enable", LVec.ofLogic .l1), ("data", LVec.ofLogic .l0)]] with
    | .ok r => pure r
    | .timeout => throw (IO.userError "run timeout")
    | .unsupported e => throw (IO.userError e)
  pure (.ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "result"))

#eval outputs
end Examples.«system-verilog».sem2.internal_clock_e.agree
