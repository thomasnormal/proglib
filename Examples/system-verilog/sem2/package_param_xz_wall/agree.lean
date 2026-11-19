/- Clean-room loudness receipt for an IEEE 1800-2023 §6.20.2 package parameter
   whose declared four-state default contains z bits. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.Sem2Run
namespace Examples.«system-verilog».sem2.package_param_xz_wall.agree
open LeanModels.Sv
#guard_msgs (drop error) in
load_design_sv2 packageParamXz from
  "Examples/system-verilog/sem2/package_param_xz_wall/package_param_xz_wall.sv.json"

private def packageEnv : IEnv :=
  { packageFvals := [(("package_param_xz_wall_pkg", "INSTR_LUI"), (.lit ("zzzzzzzzzzzzzzzzzzzzzzzzz0110111"), 32, false))] }

private def packageRef : PExpr :=
  .paramRef "INSTR_LUI" (some "package_param_xz_wall_pkg")

private def packageValue : LVec :=
  match instExpr2 packageEnv [] none packageRef with
  | .lit value => value
  | _ => .xVec 0

-- Ordinary operand positions retain the package's four-state vector.
#guard packageValue.toBinString == "zzzzzzzzzzzzzzzzzzzzzzzzz0110111"

-- The same value is consumed by the existing casez/inside/=== semantics.
#guard caseHit .casez (.lit "0000110111") (.resizeU packageValue 10)
#guard !(caseHit .casez (.lit "0001110111") (.resizeU packageValue 10))
#guard caseHit .inside (.lit "0000110111") (.resizeU packageValue 10)
#guard !(caseHit .inside (.lit "0001110111") (.resizeU packageValue 10))
#guard LVec.eqCase packageValue packageValue == .l1
#guard LVec.eqCase (.lit "zzzzzzzzzzzzzzzzzzzzzzzzz0110111") packageValue == .l1

-- Integer-required uses refuse at the named package parameter.
#guard (match evalAt packageEnv (32, false) packageRef with
  | .error message => message ==
      "package parameter 'package_param_xz_wall_pkg::INSTR_LUI' contains x/z bits in an integer-required constant context"
  | _ => false)

-- For a known package value, the new table's integer view is the old one.
#guard (IEnv.packageIntView? (IEnv.bindPackageFVal {} "pkg" "K" (.lit "0101") 4 false)
    "pkg" "K") == some 5
end Examples.«system-verilog».sem2.package_param_xz_wall.agree
