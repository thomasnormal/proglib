import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.package_aggregate_param_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 packageAggregate
  from "Examples/system-verilog/sem2/package_aggregate_param_e/package_aggregate_param_e.sv.json"
def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem packageAggregate.pdesign []
  let rows ← runCoreMemRows d d.initial
    [[("i", LVec.ofNat 2 0)], [("i", LVec.ofNat 2 1)],
     [("i", LVec.ofNat 2 2)], [("i", LVec.ofNat 2 3)],
     [("i", LVec.lit "xx")]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["000000", "101010", "010101", "111111", "xxxxxx"]
end Examples.«system-verilog».sem2.package_aggregate_param_e
