import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E receipt for a parameterized one-rank FIFO memory.

The source retains the unpacked storage declaration, run-time read and write
indices, asynchronous reset event, continuous scalar drivers, and one edge
process.  `instantiateCoreMem` keeps the declaration as one native `MemShape`
and evaluates the memory accesses at run time.  The ordinary scalar structure
tactic is intentionally not used here because its scalar route times out on
this source-shaped parameterized FIFO.
-/

namespace Examples.«system-verilog».sem2.parameterized_fifo_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 fifo
  from "Examples/system-verilog/sem2/parameterized_fifo_canonical_e/parameterized_fifo_canonical_e.sv.json"

#guard match PDesign.instantiateCoreMem fifo.pdesign [8, 4] with
  | .ok d => d.memories.size == 1 && d.processes.size == 6
  | _ => false

#guard match PDesign.instantiateCoreMem fifo.pdesign [32, 16] with
  | .ok d => d.memories.size == 1 && d.processes.size == 6 &&
      match d.memories[0]? with
      | some md => md.source.name == "storage" && md.shape.elemWidth == 32
      | _ => false
  | _ => false

#guard match PDesign.instantiateCoreMem fifo.pdesign [32, 16] with
  | .ok d => d.processes.toList.any fun p =>
      match p with
      | .edge e => e.reset == some "rst_n" && !e.resetHigh && e.clock == "clk"
      | _ => false
  | _ => false

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.parameterized_fifo_canonical_e
