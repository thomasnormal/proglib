/- Recursive canonical-E hierarchy receipt for §23.3 child instances. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem
namespace Examples.«system-verilog».sem2.child_instance_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel

def outputs : IO (Res (List String)) := do
  let text ← IO.FS.readFile "Examples/system-verilog/sem2/child_instance_e/child_instance_e.sv.json"
  let env ← match parseEnvelope2String text with | .ok e => pure e | .error e => throw (IO.userError e)
  let d ← match PDesign.instantiateE2H env.design env.lib [] with | .ok d => pure d | .timeout => throw (IO.userError "instantiate timeout") | .unsupported e => throw (IO.userError e)
  let rows ← match runCoreMemRows d d.initial [
    [("clk",LVec.ofLogic .l0),("rst_n",LVec.ofLogic .l0),("d",LVec.ofLogic .l0)],
    [("clk",LVec.ofLogic .l1),("rst_n",LVec.ofLogic .l1),("d",LVec.ofLogic .l1)],
    [("clk",LVec.ofLogic .l0),("rst_n",LVec.ofLogic .l1),("d",LVec.ofLogic .l0)],
    [("clk",LVec.ofLogic .l1),("rst_n",LVec.ofLogic .l1),("d",LVec.ofLogic .l0)]] with
    | .ok r => pure r
    | .timeout => throw (IO.userError "run timeout")
    | .unsupported e => throw (IO.userError e)
  pure (.ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q"))
#eval outputs
end Examples.«system-verilog».sem2.child_instance_e.agree
