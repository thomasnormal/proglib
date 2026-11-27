/-
Canonical-E admission receipt for the generated invalid continuous-assignment
chain under IEEE 1800-2023 §10.6. The parser nodes remain source-shaped.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.invalid_chain2_wall.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 invalidChain2Wall
  from "Examples/system-verilog/sem2/invalid_chain2_wall/invalid_chain2_wall.sv.json"

#guard invalidChain2Wall.pdesign.others == []
#guard match invalidChain2Wall.pdesign.processes with
  | [.assign "result" (.unsupported "HierarchicalValueExpression" "chain[3].running_sum")] => true
  | _ => false

#guard match invalidChain2Wall.pdesign.generates with
  | [.genFor (some "chain") "row" _ _ _ (some 4) _] => true
  | _ => false

private def flat : Design2 := invalidChain2Wall.pdesign.instantiateD2 []

#guard flat.processes.size == 9
#guard match flat.processes.toList with
  | _ :: .unsupported "GenerateDecl:UnpackedDecl" _ :: _ => true
  | _ => false

private def eResult :=
  PDesign.instantiateE2 invalidChain2Wall.pdesign []
    (PDesign.surfaceFuel [])

#guard match eResult with
  | .ok _ => true
  | _ => false

end Examples.«system-verilog».sem2.invalid_chain2_wall.agree
