import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.comb_unpacked_output_partial_def
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 combUnpacked from "Examples/system-verilog/sem2/comb_unpacked_output_partial_def/comb_unpacked_output_partial_def.sv.json"
private def rows : Res (List (String × String)) := do
  let d ← combUnpacked.e 4
  let states ← runCoreMemRows d d.initial
    [[("a", LVec.ofNat 4 0)], [("a", LVec.ofNat 4 10)],
     [("a", LVec.xVec 4)], [("a", LVec.lit "zzzz")]]
  .ok (states.map (fun s =>
    (((MemState.read s.memory "y" 0).getD (LVec.xVec 4)).toBinString,
     ((MemState.read s.memory "y" 3).getD (LVec.xVec 4)).toBinString)))
#guard rows == .ok [("0000", "0000"), ("1010", "1010"), ("xxxx", "xxxx"), ("zzzz", "zzzz")]
end Examples.«system-verilog».sem2.comb_unpacked_output_partial_def
