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

def emit (n : Int) : IO Unit := do
  match widthAt n with
  | .ok w => IO.println s!"ROW N={n} W={w}"
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError msg)

end Examples.«system-verilog».sem2.constant_function_module_e

open Examples.«system-verilog».sem2.constant_function_module_e

def main : IO Unit := do
  emit 1
  emit 8
  emit 16
