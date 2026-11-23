import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.unpacked_bitselect_target
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 unpackedBitTarget from "Examples/system-verilog/sem2/unpacked_bitselect_target/unpacked_bitselect_target.sv.json"
private def run : Res (List CoreMemState) := do
  let d ← unpackedBitTarget.e 4
  runCoreMemRows d d.initial [[]]
#guard run matches .unsupported _
end Examples.«system-verilog».sem2.unpacked_bitselect_target
