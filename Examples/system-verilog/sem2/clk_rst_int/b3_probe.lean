import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv LeanModels.Sv.Kernel

def probe : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/sem2/clk_rst_int/clk_rst_int.sv.json"
  let pd ← match loadPDesignString text with
    | .ok p => pure p
    | .error e => throw (IO.userError e)
  let d ← match PDesign.instantiateE2 pd [] (PDesign.surfaceFuel []) with
    | .ok d => pure d
    | .timeout => throw (IO.userError "instantiate timeout")
    | .unsupported e => throw (IO.userError e)
  let rows ← match runCoreMemRows d d.initial [
    [("clk", LVec.ofLogic .l0), ("rst", LVec.ofLogic .l1), ("d", LVec.ofLogic .l1)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .l1), ("d", LVec.ofLogic .l1)],
    [("clk", LVec.ofLogic .l0), ("rst", LVec.ofLogic .l0), ("d", LVec.ofLogic .l0)],
    [("clk", LVec.ofLogic .l1), ("rst", LVec.ofLogic .l0), ("d", LVec.ofLogic .l0)] ] with
    | .ok rows => pure rows
    | .timeout => throw (IO.userError "run timeout")
    | .unsupported e => throw (IO.userError e)
  let qs := rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q"
  if qs != ["x", "0", "0", "0"] then throw (IO.userError s!"bad q trace {qs}")
  IO.println "canonical E B3 internal-reset NBA event: 4 rows PASS"

#eval probe
