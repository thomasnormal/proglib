import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.constant_function_module_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 constantFunctionModuleE
  from "Examples/system-verilog/sem2/constant_function_module_e/constant_function_module_e.sv.json"

def widthAt (n : Int) : Res Nat := do
  let d ← PDesign.instantiateE2 constantFunctionModuleE.pdesign [n]
  match d.scalar.decls.toList.find? (fun x => x.name == "z") with
  | some x => .ok x.width
  | none => .unsupported "missing z"

#guard constantFunctionModuleE.pdesign.functions.length == 1
#guard widthAt 1 == .ok 1
#guard widthAt 8 == .ok 3
#guard widthAt 16 == .ok 4
end Examples.«system-verilog».sem2.constant_function_module_e
