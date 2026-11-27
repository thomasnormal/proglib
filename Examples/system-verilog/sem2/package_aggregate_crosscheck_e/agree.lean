import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.package_aggregate_crosscheck_e

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 packageAggregateCrosscheck
  from "Examples/system-verilog/sem2/package_aggregate_crosscheck_e/package_aggregate_crosscheck.sv.json"

#guard packageAggregateCrosscheck.pdesign.packageParams.length == 1
#guard match packageAggregateCrosscheck.pdesign.packageParams with
  | (pkg, p) :: _ =>
      pkg == "package_aggregate_crosscheck_pkg" &&
      p.name == "TABLE" && p.resolvedBits? == some "001110"
  | _ => false

def outputs : Res (List String) := do
  let d ← packageAggregateCrosscheck.e
  let st ← d.initialState
  let states ← runCoreMemRows d st [[]]
  .ok (states.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#eval outputs

end Examples.«system-verilog».sem2.package_aggregate_crosscheck_e
