import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle
namespace Examples.«system-verilog».sem2.mixed_array_edge_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 mixedArrayEdge from
  "Examples/system-verilog/sem2/mixed_array_edge_e/mixed_array_edge_e.sv.json"
private def d : MemDesign2 := mixedArrayEdge.pdesign.instantiateMemD2 []
def outputs : Res (List String) := do
  let rows ← runMem2 d 128
    [[("clk", .ofNat 1 1), ("d", .ofNat 8 1)],
     [("clk", .ofNat 1 0), ("d", .ofNat 8 1)],
     [("clk", .ofNat 1 1), ("d", .ofNat 8 16)],
     [("clk", .ofNat 1 0), ("d", .ofNat 8 16)],
     [("clk", .ofNat 1 1), ("d", .ofNat 8 255)]]
  .ok (rows.map (SvState.showSignal · "o"))
#eval outputs
#guard match runMem2 d 128
    [[("clk", .ofNat 1 1), ("d", .ofNat 8 1)],
     [("clk", .ofNat 1 0), ("d", .ofNat 8 1)],
     [("clk", .ofNat 1 1), ("d", .ofNat 8 16)],
     [("clk", .ofNat 1 0), ("d", .ofNat 8 16)],
     [("clk", .ofNat 1 1), ("d", .ofNat 8 255)]] with
  | .ok [s0, _, s2, _, s4] =>
      SvState.showSignal s0 "o" == "0000001000000001" &&
      SvState.showSignal s2 "o" == "0001000100010000" &&
      SvState.showSignal s4 "o" == "0000000011111111"
  | _ => false
end Examples.«system-verilog».sem2.mixed_array_edge_e
