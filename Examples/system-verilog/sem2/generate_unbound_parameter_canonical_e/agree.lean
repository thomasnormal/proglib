import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.generate_unbound_parameter_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 generateUnbound
  from "Examples/system-verilog/sem2/generate_unbound_parameter_canonical_e/generate_unbound_parameter_top.sv.json"
def stimulus : List SvState := [
  [("x", LVec.ofNat 1 1)], [("x", LVec.ofNat 1 1)],
  [("x", LVec.ofNat 1 1)], [("x", LVec.ofNat 1 1)],
  [("x", LVec.lit "z")], [("x", LVec.ofNat 1 1)],
  [("x", LVec.ofNat 1 0)], [("x", LVec.ofNat 1 1)]]
def outputs : Res (List String) := do
  let d ← generateUnbound.e
  let st ← d.initialState
  let rows ← stimulus.foldlM (init := (st, [])) fun (st, rows) input => do
    let st' ← d.step st input
    .ok (st', rows ++ [SvState.showSignal (CoreMemState.view d st') "y"])
  .ok rows.2
#guard outputs == .ok ["1", "1", "1", "1", "z", "1", "0", "1"]
end Examples.«system-verilog».sem2.generate_unbound_parameter_canonical_e
