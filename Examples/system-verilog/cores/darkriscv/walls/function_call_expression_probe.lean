import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 fc from "Examples/system-verilog/cores/darkriscv/walls/function_call_expression.sv.json"
def row (v : Nat) : SvState := [("in", LVec.ofNat 1 v)]

private def rowWith (v : LVec) : SvState := [("in", v)]

private def output (plusargs : List String) (v : LVec) : Option String :=
  match PDesign.instantiateCoreMem fc.pdesign [] with
  | .ok d =>
      let d := d.withPlusargs plusargs
      match d.initialState with
      | .ok st =>
          match d.step st (rowWith v) with
          | .ok st' => (SvState.lookup (d.scalar.view st'.scalar) "y").map LVec.toBinString
          | _ => none
      | _ => none
  | _ => none

#guard output [] (LVec.ofNat 1 0) == some "0"
#guard output [] (LVec.ofNat 1 1) == some "0"
#guard output [] (LVec.lit "x") == some "0"
#guard output [] (LVec.lit "z") == some "0"
#guard output ["flag"] (LVec.ofNat 1 0) == some "0"
#guard output ["flag"] (LVec.ofNat 1 1) == some "1"
#guard output ["flag"] (LVec.lit "x") == some "x"
#guard output ["flag"] (LVec.lit "z") == some "z"

#eval match output ["flag"] (LVec.ofNat 1 1) with
  | some bits => "canonical-step-ok: y=" ++ bits
  | none => "canonical-step-failed"
