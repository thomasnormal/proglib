import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.constant_struct_pattern_package_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 constantStructPatternPackageE
  from "Examples/system-verilog/sem2/constant_struct_pattern_package_e/constant_struct_pattern_package_e.sv.json"
#guard match PDesign.instantiateCoreMem constantStructPatternPackageE.pdesign [1] with
  | .ok d => d.scalar.decls.toList.any (fun x => x.name == "y")
  | _ => false
def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem constantStructPatternPackageE.pdesign [1]
  let rows ← runCoreMemRows d d.initial [[]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#eval outputs
end Examples.«system-verilog».sem2.constant_struct_pattern_package_e
