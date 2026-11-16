import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.constant_width_conversion_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 constantWidthConversion from
  "Examples/system-verilog/sem2/constant_width_conversion_e/constant_width_conversion_e.sv.json"
def outputs (e : Int) : Res (List String) := do
  let d ← PDesign.instantiateCoreMem constantWidthConversion.pdesign [e]
  let rows ← runCoreMemRows d d.initial [
    [("x", LVec.ofNat 1 0)], [("x", LVec.ofNat 1 1)],
    [("x", LVec.lit "x")], [("x", LVec.lit "z")]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs 8 == .ok ["0", "1", "x", "x"]
#guard outputs 4 == .ok ["0", "1", "x", "x"]
end Examples.«system-verilog».sem2.constant_width_conversion_e
