import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycle
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.prefix_adder_unpacked_array

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 prefixAdder from
  "Examples/system-verilog/sem2/prefix_adder_unpacked_array/prefix_adder_unpacked_array.sv.json"

/-! The retained source-shaped route keeps the unpacked declaration as a
native `MemShape` and each generated packed-element assignment as an
`arrayBitSel`.  The reusable memory equations and a hand-built two-cell
receipt are in `mem_lemmas.lean`; the memory-backed settled-value theorem and
its thin tactic wrapper remain the next wall. -/

#guard match prefixAdder.e 4 with
  | .ok d => d.memories.toList.map (fun m => m.source.name) == ["mem"]
  | _ => false

#guard match prefixAdder.e 4 with
  | .ok d => d.scalar.decls.toList.map (fun x => x.name) == ["a", "y"]
  | _ => false

#guard match prefixAdder.e 4 with
  | .ok d => d.processes.toList.any (fun p =>
      match p with
      | .assign (.arrayBitSel "mem" [.int 0] (.int 0))
          (.bitSel (.ident "a") (.int 0)) => true
      | _ => false)
  | _ => false

#guard match prefixAdder.e 4 with
  | .ok d => d.processes.toList.any (fun p =>
      match p with
      | .assign (.arrayBitSel _ [_] _) _ => true
      | _ => false)
  | _ => false

#guard match prefixAdder.e 4 with
  | .ok d =>
      match d.processes[1]? with
      | some p => d.procOkIB 1 p = false
      | none => false
  | _ => false

end Examples.«system-verilog».sem2.prefix_adder_unpacked_array
