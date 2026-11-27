import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.package_array_function_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 packageArrayFunction from
  "Examples/system-verilog/sem2/package_array_function_e/package_array_function_e.sv.json"
#guard packageArrayFunction.pdesign.crossCheckFull == ([], 3)
def outputs : Res (List String) := do
  let d ← packageArrayFunction.e
  let rows ← runCoreMemRows d d.initial
    [[("i", LVec.ofInt 8 0)], [("i", LVec.ofInt 8 255)],
     [("i", LVec.xVec 8)], [("i", LVec.lit "zzzzzzzz")]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "o")
#guard outputs == .ok ["00000111", "00000110", "xxxxxxxx", "xxxxxxxx"]
end Examples.«system-verilog».sem2.package_array_function_e.agree
