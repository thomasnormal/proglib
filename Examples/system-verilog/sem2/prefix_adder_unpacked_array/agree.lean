import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycle
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.prefix_adder_unpacked_array

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 prefixAdder from
  "Examples/system-verilog/sem2/prefix_adder_unpacked_array/prefix_adder_unpacked_array.sv.json"

/-! The current loader's measured boundary for this clean-room source is
precise but still open.  The unpacked declaration is flattened to scalar
names, while the generated element assignments remain packed `PLhs.bitSel`
targets.  The native `MemState` combinational theorem cannot apply until the
loader preserves the unpacked declaration and maps generated element writes to
that memory identity (or the canonical profile admits the retained bit-select
form with equivalent cell equations). -/

#guard match prefixAdder.e 4 with
  | .ok d => d.memories.toList.isEmpty
  | _ => false

#guard match prefixAdder.e 4 with
  | .ok d => d.scalar.decls.toList.any (fun x => x.name == "mem[0]")
  | _ => false

#guard match prefixAdder.e 4 with
  | .ok d => d.processes.toList.any (fun p =>
      match p with
      | .assign (.bitSel "mem[0]" (.int 0))
          (.bitSel (.ident "a") (.int 0)) => true
      | _ => false)
  | _ => false

#guard match prefixAdder.e 4 with
  | .ok d => d.processes.toList.any (fun p =>
      match p with
      | .assign (.bitSel _ _) _ => true
      | _ => false)
  | _ => false

#guard match prefixAdder.e 4 with
  | .ok d =>
      match d.processes[1]? with
      | some p => d.procOkIB 1 p = false
      | none => false
  | _ => false

end Examples.«system-verilog».sem2.prefix_adder_unpacked_array
