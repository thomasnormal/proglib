/- Clean-room receipt for a four-state package parameter in casez, inside,
   and case-equality operand positions. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.Sem2Run
namespace Examples.«system-verilog».sem2.package_param_xz_ops.agree
open LeanModels.Sv
#guard_msgs (drop error) in
load_design_sv2 packageParamXzOps from
  "Examples/system-verilog/sem2/package_param_xz_ops/package_param_xz_ops.sv.json"

private def packageEnv : IEnv :=
  { packageFvals := [(("package_param_xz_ops_pkg", "MASK"), (.lit "1z0z", 4, false))] }
private def packageRef : PExpr :=
  .paramRef "MASK" (some "package_param_xz_ops_pkg")
private def packageValue : LVec :=
  match instExpr2 packageEnv [] none packageRef with
  | .lit value => value
  | _ => .xVec 0

#guard packageValue.toBinString == "1z0z"
#guard caseHit .casez (.lit "1101") packageValue
#guard !(caseHit .casez (.lit "1111") packageValue)
#guard caseHit .inside (.lit "1101") packageValue
#guard !(caseHit .inside (.lit "1111") packageValue)
#guard LVec.eqCase (.lit "1z0z") packageValue == .l1
#guard LVec.eqCase (.lit "1101") packageValue == .l0
end Examples.«system-verilog».sem2.package_param_xz_ops.agree
