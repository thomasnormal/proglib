import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_countbits.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 countBitsProp from
  "Examples/system-verilog/sem2/sva_countbits/sva_countbits.sv.json"

private def env : IEnv := { widths := [("clk", 1), ("a", 4), ("q", 1)] }
private def edge (clk a q : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                       ("q", LVec.ofNat 1 q)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                        ("q", LVec.ofNat 1 q)] } }

private def edgeLit (clk : Nat) (a : String) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.lit a),
                       ("q", LVec.ofNat 1 0)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.lit a),
                        ("q", LVec.ofNat 1 0)] } }

#guard match countBitsProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 0 1 0, edge 1 1 0] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

#guard match countBitsProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edgeLit 1 "10xz"] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_countbits.proof
