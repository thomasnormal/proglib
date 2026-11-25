import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.generated_unpacked_fifo_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 generatedUnpackedFifo from
  "Examples/system-verilog/sem2/generated_unpacked_fifo_e/generated_unpacked_fifo_e.sv.json"
def stimuli : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 8 0)],
   [("clk", LVec.ofNat 1 1), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 8 0)],
   [("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 8 0xa5)],
   [("clk", LVec.ofNat 1 1), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 8 0xa5)],
   [("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 0), ("d", LVec.lit "xxxxxxxx")],
   [("clk", LVec.ofNat 1 1), ("en", LVec.ofNat 1 0), ("d", LVec.lit "xxxxxxxx")],
   [("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 1), ("d", LVec.lit "zzzzzzzz")],
   [("clk", LVec.ofNat 1 1), ("en", LVec.ofNat 1 1), ("d", LVec.lit "zzzzzzzz")]]
def outputs : Res (List String) := do
  let d ← generatedUnpackedFifo.e 2 8
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")
#guard match generatedUnpackedFifo.e 2 8 with
  | .ok d => d.memories.size == 1 && d.processes.size == 3
  | _ => false
#guard outputs == .ok ["xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "10100101", "10100101", "10100101", "10100101", "zzzzzzzz"]
end Examples.«system-verilog».sem2.generated_unpacked_fifo_e
