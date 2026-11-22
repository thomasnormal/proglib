/- Canonical-E aggregate output port target receipt for IEEE 1800-2023 §23.2.2. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem
namespace Examples.«system-verilog».sem2.port_connection_target_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel

def outputs : IO (Res (List String)) := do
  let text ← IO.FS.readFile "Examples/system-verilog/sem2/port_connection_target_e/port_connection_target_e.sv.json"
  let env ← match parseEnvelope2String text with | .ok e => pure e | .error e => throw (IO.userError e)
  let d ← match PDesign.instantiateE2H env.design env.lib [] with | .ok d => pure d | .timeout => throw (IO.userError "instantiate timeout") | .unsupported e => throw (IO.userError e)
  let rows ← match runCoreMemRows d d.initial [
    [("d",LVec.ofLogic .l0)],
    [("d",LVec.ofLogic .l1)],
    [("d",LVec.ofLogic .lx)],
    [("d",LVec.ofLogic .lz)]] with
    | .ok r => pure r
    | .timeout => throw (IO.userError "run timeout")
    | .unsupported e => throw (IO.userError e)
  pure (.ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y"))
#eval outputs
end Examples.«system-verilog».sem2.port_connection_target_e.agree
