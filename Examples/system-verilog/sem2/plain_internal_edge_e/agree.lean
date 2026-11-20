/- Canonical-E R13 receipt. A plain `always @(posedge g)` and its
`always_ff` twin must observe the same internally generated edge. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.plain_internal_edge_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel

def rows : List SvState :=
  [[("clk", LVec.ofLogic .l0), ("d", LVec.ofLogic .l0)],
   [("clk", LVec.ofLogic .l1), ("d", LVec.ofLogic .l1)],
   [("clk", LVec.ofLogic .l0), ("d", LVec.ofLogic .l1)],
   [("clk", LVec.ofLogic .lx), ("d", LVec.ofLogic .lx)],
   [("clk", LVec.ofLogic .lz), ("d", LVec.ofLogic .lz)],
   [("clk", LVec.ofLogic .l1), ("d", LVec.ofLogic .lx)]]

def outputs : IO (Res (List (String × String))) := do
  let text ← IO.FS.readFile "Examples/system-verilog/sem2/plain_internal_edge_e/plain_internal_edge_e.sv.json"
  let pd ← match loadPDesignString text with | .ok p => pure p | .error e => throw (IO.userError e)
  match PDesign.instantiateE2 pd [] (PDesign.surfaceFuel []) with
  | .timeout => pure .timeout
  | .unsupported e => pure (.unsupported e)
  | .ok d =>
      match runCoreMemRows d d.initial rows with
      | .ok states => pure (.ok (states.map (fun s =>
          (SvState.showSignal (CoreMemState.view d s) "q_plain",
           SvState.showSignal (CoreMemState.view d s) "q_ff"))))
      | .timeout => pure .timeout
      | .unsupported e => pure (.unsupported e)

def twinEquality : IO Unit := do
  match ← outputs with
  | .ok rows =>
      unless rows.all (fun row => row.1 == row.2) do
        throw (IO.userError "plain always and always_ff twins diverged")
      unless rows == [("x", "x"), ("1", "1"), ("1", "1"), ("1", "1"), ("1", "1"), ("1", "1")] do
        throw (IO.userError "R13 differential rows changed")
  | .timeout => throw (IO.userError "R13 receipt timed out")
  | .unsupported e => throw (IO.userError e)

#eval outputs
#eval twinEquality


end Examples.«system-verilog».sem2.plain_internal_edge_e.agree
