/-
  A packed dimension shared by two ANSI inputs is elaborated in the declaring
  module scope. IEEE 1800-2023 §§6.8 and 23.2.2 require both declarations to
  retain the parameterized width and the ordinary hierarchy route to preserve
  that width at the instance boundary.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem
namespace Examples.«system-verilog».sem2.packed_dimension_crosscheck_e
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 packed from
  "Examples/system-verilog/sem2/packed_dimension_crosscheck_e/packed_dimension_crosscheck.sv.json"

private def yes : Nat := 7955827
#guard packed.pdesign.defaultArgs == .ok [8, 23, 2, yes]
#guard match packed.e 8 23 2 yes with
  | .ok d => CoreMemDesign.Structure d && d.scalar.decls.toList.any (fun x => x.name == "a") &&
      d.scalar.decls.toList.any (fun x => x.name == "b")
  | _ => false

 def outputs : Res (List String) := do
  let d ← match packed.e 8 23 2 yes with
    | .ok d => pure d
    | .timeout => .timeout
    | .unsupported e => .unsupported e
  let states ← runCoreMemRows d d.initial [
    [("clk", LVec.lit "0"), ("rst", LVec.lit "0"), ("valid_in", LVec.lit "0"),
      ("a", LVec.lit "00000000000000000000000001011010"),
      ("b", LVec.lit "00000000000000000000000010100101")],
    [("clk", LVec.lit "1"), ("rst", LVec.lit "0"), ("valid_in", LVec.lit "1"),
      ("a", LVec.lit "00000000000000000000000001011010"),
      ("b", LVec.lit "00000000000000000000000010100101")]]
  .ok (states.map fun s => SvState.showSignal (CoreMemState.view d s) "result")

#eval outputs
end Examples.«system-verilog».sem2.packed_dimension_crosscheck_e
