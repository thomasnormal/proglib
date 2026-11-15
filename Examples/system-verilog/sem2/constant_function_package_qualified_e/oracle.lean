import LeanModels.Sv.Ingest2
open LeanModels.Sv

load_design_sv2 constantFunctionPackageQualifiedE
  from "Examples/system-verilog/sem2/constant_function_package_qualified_e/constant_function_package_qualified_e.sv.json"

def widthAt (n : Int) : Res Nat := do
  let d ← PDesign.instantiateE2Scalar constantFunctionPackageQualifiedE.pdesign [n]
  match d.decls.toList.find? (fun x => x.name == "z") with
  | some x => .ok x.width
  | none => .unsupported "missing z"

def emit (n : Int) : IO Unit := do
  match widthAt n with
  | .ok w => IO.println s!"ROW N={n} W={w}"
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError msg)

def main : IO Unit := do
  emit 1
  emit 8
  emit 16
