import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E receipt for the one-rank source-shaped memory initializer.

The declaration remains one native `MemState` memory.  The parser's initial
process runs once at time zero (§9.2.1), then the ordinary continuous
assignment settles `q` from the initialized cell.
-/

set_option maxRecDepth 100000 in
load_design_sv2 initial_memory_wall
  from "Examples/system-verilog/cores/darkriscv/walls/initial_memory.sv.json"

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#guard match PDesign.instantiateCoreMem initial_memory_wall.pdesign [8, 2] with
  | .ok d => d.memories.size == 1 && d.processes.size == 2 &&
      match d.initialState with
      | .ok st => match d.settleCanonical d.env d.elems st d.processes.toList with
        | .ok settled =>
            MemState.read settled.memory "mem" 0 == some (LVec.lit "00111100") &&
              SvState.lookup (CoreMemState.view d settled) "q" == some (LVec.lit "00111100")
        | _ => false
      | _ => false
  | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#guard match PDesign.instantiateCoreMem initial_memory_wall.pdesign [32, 32] with
  | .ok d => match d.initialState with
      | .ok st => match d.settleCanonical d.env d.elems st d.processes.toList with
        | .ok settled =>
            MemState.read settled.memory "mem" 0 == some (LVec.lit "00000000000000000000000000111100") &&
              SvState.lookup (CoreMemState.view d settled) "q" ==
                some (LVec.lit "00000000000000000000000000111100")
        | _ => false
      | _ => false
  | _ => false
