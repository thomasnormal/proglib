import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.plain_internal_edge_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 plain from "Examples/system-verilog/sem2/plain_internal_edge_e/plain_internal_edge_e.sv.json"
load_design_sv2 ff from "Examples/system-verilog/sem2/plain_internal_edge_e/ff_internal_edge_e.sv.json"

def firstRow : SvState := [("clk", LVec.ofLogic .l0), ("d", LVec.ofLogic .l0), ("e", LVec.ofLogic .l0)]
def risingRow : SvState := [("clk", LVec.ofLogic .l1), ("d", LVec.ofLogic .l1), ("e", LVec.ofLogic .l1)]

/-! The second process must be discovered after the first process commits `g`.
This is the direct in-slot check that distinguishes the source-shaped route from
a pass that only counts retained `.edge` constructors. -/
def detectsInternalFollowup : Res CoreMemDesign → Bool
  | .ok E =>
      match E.initialState with
      | .ok s0 =>
          match E.step s0 firstRow with
          | .ok s1 =>
              match E.stepOnePassTrace s1 risingRow with
              | .ok (_, caused) => caused
              | _ => false
          | _ => false
      | _ => false
  | _ => false

#guard detectsInternalFollowup plain.e
#guard detectsInternalFollowup ff.e

-- Every requested four-state transition of g is exercised. The e input changes
-- on each row so a fired second process is observable in q.
def stimulus : List (Logic × Logic × Logic) :=
  [(.l0,.l0,.l0),
   (.l1,.l0,.l0), (.l0,.l0,.l0),
   (.l1,.lx,.l1), (.l0,.lx,.l1),
   (.l1,.l0,.l0), (.l0,.l0,.l0),
   (.l1,.lz,.l1), (.l0,.lz,.l1),
   (.l1,.l0,.l0), (.l0,.l0,.l0),
   (.l1,.lx,.l0), (.l0,.lx,.l0),
   (.l1,.l1,.l1), (.l0,.l1,.l1),
   (.l1,.lx,.l0), (.l0,.lx,.l0),
   (.l1,.lz,.l1), (.l0,.lz,.l1),
   (.l1,.l1,.l0), (.l0,.l1,.l0)]

def simulate (top : String) : IO (List String) := do
  let text ← IO.FS.readFile s!"Examples/system-verilog/sem2/plain_internal_edge_e/{top}.sv.json"
  let pd ← IO.ofExcept (loadPDesignString text)
  let states := do
    let design ← PDesign.instantiateE2 pd []
    let initial ← design.initialState
    let rows := stimulus.map fun (clk, d, e) =>
      [("clk", LVec.ofLogic clk), ("d", LVec.ofLogic d), ("e", LVec.ofLogic e)]
    let states ← runCoreMemRows design initial rows
    pure (states.map fun s =>
      let view := CoreMemState.view design s
      view.showSignal "g" ++ view.showSignal "q")
  match states with
  | .ok xs => pure xs
  | .timeout => throw (IO.userError s!"{top} timed out")
  | .unsupported e => throw (IO.userError s!"{top}: {e}")

def checkTwins : IO Unit := do
  let expected := ["xx", "0x", "0x", "x1", "x1", "01", "01", "z1", "z1", "01", "01", "x0", "x0", "11", "11", "x1", "x1", "z1", "z1", "10", "10"]
  let plain ← simulate "plain_internal_edge_e"
  let ff ← simulate "ff_internal_edge_e"
  unless plain == ff && plain == expected do
    throw (IO.userError s!"(g,q) mismatch: always {plain}, always_ff {ff}")
  for gq in plain do
    IO.println s!"ROW {gq}"

#eval checkTwins

end Examples.«system-verilog».sem2.plain_internal_edge_e.agree
