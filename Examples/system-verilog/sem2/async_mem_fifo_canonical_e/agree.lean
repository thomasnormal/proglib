import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.async_mem_fifo_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 asyncMem from "Examples/system-verilog/sem2/async_mem_fifo_canonical_e/async_mem_fifo_canonical_e.sv.json"
def outputs : Res (List String) := do
  let d ← asyncMem.e 8 4
  let rows ← runCoreMemRows d d.initial [
    [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 0), ("d", LVec.ofNat 8 3)],
    [("clk", LVec.ofNat 1 0), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 17)],
    [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 17)],
    [("clk", LVec.ofNat 1 0), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 34)],
    [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 34)]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")
#guard outputs == .ok ["00000000", "00000000", "00010001", "00010001", "00100010"]
end Examples.«system-verilog».sem2.async_mem_fifo_canonical_e
