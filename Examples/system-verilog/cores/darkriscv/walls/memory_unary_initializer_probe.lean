import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

set_option maxRecDepth 100000 in
load_design_sv2 memory_unary_initializer_wall
  from "Examples/system-verilog/cores/darkriscv/walls/memory_unary_initializer.sv.json"

open LeanModels.Sv
open LeanModels.Sv.Kernel

private def d : CoreMemDesign :=
  match memory_unary_initializer_wall.e 1 with
  | .ok design => design
  | _ => default

#guard d.memories.size == 1
#guard d.processes.size == 2

#guard match d.initialState with
  | .ok st =>
      match d.settleCanonical d.env d.elems st d.processes.toList with
      | .ok settled =>
          MemState.read settled.memory "mem" 0 == some (LVec.lit "11") &&
          SvState.lookup (CoreMemState.view d settled) "q" == some (LVec.lit "11")
      | _ => false
  | _ => false
