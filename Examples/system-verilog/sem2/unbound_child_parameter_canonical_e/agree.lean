import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.unbound_child_parameter_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 unboundChild
  from "Examples/system-verilog/sem2/unbound_child_parameter_canonical_e/unbound_child_parameter_top.sv.json"

#guard unboundChild.pdesign.crossCheckFull == ([], 2)
def stimulus : List SvState := [
  [("x", LVec.ofNat 8 0)], [("x", LVec.ofNat 8 1)],
  [("x", LVec.ofNat 8 42)], [("x", LVec.ofNat 8 255)],
  [("x", LVec.lit "xxxxxxxx")], [("x", LVec.lit "zzzzzzzz")],
  [("x", LVec.ofNat 8 127)], [("x", LVec.ofNat 8 128)]]
def outputs : Res (List String) := do
  let d ← unboundChild.e
  let st ← d.initialState
  let rows ← stimulus.foldlM (init := (st, [])) fun (st, rows) input => do
    let st' ← d.step st input
    .ok (st', rows ++ [SvState.showSignal (CoreMemState.view d st') "y"])
  .ok rows.2
#guard outputs == .ok ["00000000", "00000001", "00101010", "11111111", "xxxxxxxx", "zzzzzzzz", "01111111", "10000000"]
end Examples.«system-verilog».sem2.unbound_child_parameter_canonical_e
