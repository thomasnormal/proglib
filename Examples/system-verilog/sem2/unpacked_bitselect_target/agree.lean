import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.unpacked_bitselect_target
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 unpackedBitTarget from "Examples/system-verilog/sem2/unpacked_bitselect_target/unpacked_bitselect_target.sv.json"
def outputs : Res (List String) := do
  let d ← unpackedBitTarget.e 4
  let rows ← runCoreMemRows d d.initial
    [[("a", LVec.ofNat 4 0), ("b", LVec.ofNat 4 0)],
     [("a", LVec.ofNat 4 10), ("b", LVec.ofNat 4 3)],
     [("a", LVec.xVec 4), ("b", LVec.ofNat 4 5)],
     [("a", LVec.lit "zzzz"), ("b", LVec.ofNat 4 5)]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["0000", "1001", "xxxx", "xxxx"]
end Examples.«system-verilog».sem2.unpacked_bitselect_target
