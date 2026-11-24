import Examples.«system-verilog».sem2.clocked_derived_shift_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.clocked_derived_shift_e

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("rst_n", LVec.ofNat 1 0), ("load", LVec.ofNat 1 0), ("d", LVec.ofNat 4 0), ("mask", LVec.ofNat 4 0)],
   [("clk", LVec.ofNat 1 0), ("rst_n", LVec.ofNat 1 1), ("load", LVec.ofNat 1 1), ("d", LVec.ofNat 4 3), ("mask", LVec.ofNat 4 1)],
   [("clk", LVec.ofNat 1 1), ("rst_n", LVec.ofNat 1 1), ("load", LVec.ofNat 1 1), ("d", LVec.ofNat 4 3), ("mask", LVec.ofNat 4 1)],
   [("clk", LVec.ofNat 1 0), ("rst_n", LVec.ofNat 1 1), ("load", LVec.ofNat 1 0), ("d", LVec.ofNat 4 0), ("mask", LVec.ofNat 4 2)],
   [("clk", LVec.ofNat 1 1), ("rst_n", LVec.ofNat 1 1), ("load", LVec.ofNat 1 0), ("d", LVec.ofNat 4 0), ("mask", LVec.ofNat 4 2)],
   [("clk", LVec.ofNat 1 0), ("rst_n", LVec.ofNat 1 1), ("load", LVec.ofNat 1 1), ("d", LVec.ofNat 4 9), ("mask", LVec.ofNat 4 4)],
   [("clk", LVec.ofNat 1 1), ("rst_n", LVec.ofNat 1 1), ("load", LVec.ofNat 1 1), ("d", LVec.ofNat 4 9), ("mask", LVec.ofNat 4 4)],
   [("clk", LVec.ofNat 1 0), ("rst_n", LVec.ofNat 1 1), ("load", LVec.ofNat 1 0), ("d", LVec.lit "xxxx"), ("mask", LVec.lit "xxxx")],
   [("clk", LVec.ofNat 1 1), ("rst_n", LVec.ofNat 1 1), ("load", LVec.ofNat 1 0), ("d", LVec.lit "xxxx"), ("mask", LVec.lit "xxxx")]]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateE2 derivedShift.pdesign [4]
  let states ← runCoreMemRows d d.initial stimulus
  .ok (states.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

def main : IO Unit := do
  match outputs with
  | .ok rows => for (row, i) in rows.zipIdx do IO.println s!"ROW i={i} q={row}"
  | .unsupported m => throw (IO.userError m)
  | .timeout => throw (IO.userError "timeout")
