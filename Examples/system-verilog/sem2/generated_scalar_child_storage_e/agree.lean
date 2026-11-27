/-
  Scalar storage declared in an active generate arm of a child module is
  retained by hierarchy elaboration.  IEEE 1800-2023 §§23.3.3 and 27.4 require
  the selected child scope and its declaration to remain distinct at the
  instance boundary.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem
namespace Examples.«system-verilog».sem2.generated_scalar_child_storage_e
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 generated from
  "Examples/system-verilog/sem2/generated_scalar_child_storage_e/generated_scalar_child_storage.sv.json"

#guard generated.pdesign.defaultArgs == .ok [8, 2]
#guard match generated.e 8 2 with
  | .ok d => CoreMemDesign.Structure d && d.scalar.decls.toList.any (fun x => x.name == "child.shift.pipe")
  | _ => false

private def rows : IO (List String) := do
  let d ← match generated.e 8 2 with
    | .ok d => pure d
    | .timeout => throw (IO.userError "instantiate timeout")
    | .unsupported e => throw (IO.userError e)
  let rs ← match runCoreMemRows d d.initial [
      [("clk", LVec.lit "0"), ("data", LVec.lit "00000000")],
      [("clk", LVec.lit "1"), ("data", LVec.lit "00000000")],
      [("clk", LVec.lit "0"), ("data", LVec.lit "10101100")],
      [("clk", LVec.lit "1"), ("data", LVec.lit "10101100")],
      [("clk", LVec.lit "0"), ("data", LVec.lit "11110000")],
      [("clk", LVec.lit "1"), ("data", LVec.lit "11110000")],
      [("clk", LVec.lit "0"), ("data", LVec.lit "xxxxxxxx")],
      [("clk", LVec.lit "1"), ("data", LVec.lit "xxxxxxxx")],
      [("clk", LVec.lit "0"), ("data", LVec.lit "zzzzzzzz")],
      [("clk", LVec.lit "1"), ("data", LVec.lit "zzzzzzzz")]] with
    | .ok rs => pure rs
    | .timeout => throw (IO.userError "run timeout")
    | .unsupported e => throw (IO.userError e)
  pure (rs.map fun s => SvState.showSignal (CoreMemState.view d s) "out")

#eval rows

end Examples.«system-verilog».sem2.generated_scalar_child_storage_e
