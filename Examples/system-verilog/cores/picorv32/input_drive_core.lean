import Examples.«system-verilog».cores.picorv32.R2
import LeanModels.Sv.Kernel.CoreMemFast
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

namespace Examples.«system-verilog».cores.picorv32

open LeanModels.Sv LeanModels.Sv.Kernel
open LeanModels.Refine LeanModels.Rv

/- The loaded design is compiled once so the input-driven receipt can execute
the source-shaped E route without re-elaborating the multi-megabyte envelope
for every temporary probe. -/
opaque picorv32_core_mem : Res CoreMemDesign :=
  picorv32_r2.e 1 1 1 1 0 1 0 0 0 0 1 1 0 0 0 0 0 1 1 0 0 0 4294967295 0 16 4294967295

/-! A loaded canonical-E design is useful to an invariant only when its
    source-shaped design identity is retained alongside the machine adapter.
    The equality is a certificate supplied by the loader result.  It does not
    assert that the adapter's exact-step field has been proved. -/

structure PicoRV32LoadedCanonicalE where
  design : CoreMemDesign
  loaded : picorv32_core_mem = .ok design
  machine : rvfi_core_adapter.CoreRvfiMachine design

/-! The canonical machine starts from the exact E initial state.  This small
    reset relation records the state shape needed by an R2 invariant while
    leaving the architectural-to-core register and memory correspondence as
    an explicit future premise. -/

structure PicoRV32ResetRelation
    (design : CoreMemDesign) (program : Memory)
    (state : CoreMemState) (memoryState : RvMemoryState) : Prop where
  state_eq : state = design.initial
  arch_eq : memoryState.arch = ArchState.init 0
  memory_eq : memoryState.memory = program
  scalar_store : state.scalar = design.scalarStore state.scalarCache
  scalar_size : state.scalarCache.size = design.scalar.decls.size

theorem picoRV32_reset_relation_initial (design : CoreMemDesign)
    (program : Memory) :
    PicoRV32ResetRelation design program design.initial
      { arch := ArchState.init 0, memory := program } := by
  refine { state_eq := rfl, arch_eq := rfl, memory_eq := rfl, scalar_store := ?_, scalar_size := ?_ }
  · rfl
  · simp [CoreMemDesign.initial, CoreMemDesign.scalarCacheOf]

#print axioms picoRV32_reset_relation_initial

end Examples.«system-verilog».cores.picorv32
