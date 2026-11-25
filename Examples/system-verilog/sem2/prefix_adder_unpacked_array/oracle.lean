import Examples.«system-verilog».sem2.prefix_adder_unpacked_array.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.prefix_adder_unpacked_array

def rows : Res (List String) := do
  let d ← PDesign.instantiateCoreMem prefixAdder.pdesign [4]
  let st ← d.initialState
  let states : List SvState :=
    [[("a", LVec.ofNat 4 0)], [("a", LVec.ofNat 4 5)],
     [("a", LVec.ofNat 4 10)], [("a", LVec.ofNat 4 15)],
     [("a", LVec.xVec 4)]]
  let outs ← states.mapM fun input => do
    let rs ← runCoreMemRows d st [input]
    let final := rs.getD 0 st
    pure (SvState.showSignal (CoreMemState.view d final) "y")
  pure (outs.zipIdx.map fun (row, i) => s!"ROW a={i} y={row}")

def main : IO Unit := do
  match rows with
  | .ok xs => xs.forM IO.println
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError s!"E refusal: {msg}")
