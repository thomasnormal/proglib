/- Direct canonical-E receipt for two independent input clocks. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.multi_clock_domain_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel

def outputs : IO (Res (List (String × String))) := do
  let text ← IO.FS.readFile "Examples/system-verilog/sem2/multi_clock_domain_e/multi_clock_domain_e.sv.json"
  let pd ← match loadPDesignString text with | .ok p => pure p | .error e => throw (IO.userError e)
  let d ← match PDesign.instantiateE2 pd [] (PDesign.surfaceFuel []) with | .ok d => pure d | .timeout => throw (IO.userError "instantiate timeout") | .unsupported e => throw (IO.userError e)
  let rows ← match runCoreMemRows d d.initial [
    [("aclk",LVec.ofLogic .l0),("bclk",LVec.ofLogic .l0),("d",LVec.ofLogic .l0)],
    [("aclk",LVec.ofLogic .l1),("bclk",LVec.ofLogic .l0),("d",LVec.ofLogic .l1)],
    [("aclk",LVec.ofLogic .l0),("bclk",LVec.ofLogic .l1),("d",LVec.ofLogic .l1)],
    [("aclk",LVec.ofLogic .l1),("bclk",LVec.ofLogic .l0),("d",LVec.ofLogic .lx)],
    [("aclk",LVec.ofLogic .l0),("bclk",LVec.ofLogic .lx),("d",LVec.ofLogic .lz)],
    [("aclk",LVec.ofLogic .lz),("bclk",LVec.ofLogic .l0),("d",LVec.ofLogic .l1)],
    [("aclk",LVec.ofLogic .l0),("bclk",LVec.ofLogic .l0),("d",LVec.ofLogic .l0)],
    [("aclk",LVec.ofLogic .l1),("bclk",LVec.ofLogic .l1),("d",LVec.ofLogic .l1)]] with
    | .ok r => pure r
    | .timeout => throw (IO.userError "run timeout")
    | .unsupported e => throw (IO.userError e)
  pure (.ok (rows.map fun s => (SvState.showSignal (CoreMemState.view d s) "x", SvState.showSignal (CoreMemState.view d s) "y")))
#eval outputs
end Examples.«system-verilog».sem2.multi_clock_domain_e.agree
