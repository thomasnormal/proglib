import LeanModels.Refine.RvfiTrap
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 illegal-instruction class

The trap family has two distinct parser outcomes.  An undecodable word enters
the illegal-instruction trap directly, while a decoded Zicsr word with an
unimplemented address takes the separate illegal-CSR path.  Both fixed words
are checked by the exact decoder and threaded through the precise trap
boundary for arbitrary architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_illegal

open LeanModels.Rv
open LeanModels.Refine

def illegalWord : Word := 0x00000000
def illegalCsrWord : Word := 0x7ff110f3

def illegalCsrKind : CsrOpKind :=
  { op := .rw, rd := 1, src := .reg 2, addr := 0x7ff }

theorem illegal_decode :
    Fetched.decode (.word illegalWord) = none := by
  decide

theorem illegal_csr_decode :
    Fetched.decode (.word illegalCsrWord) = some illegalCsrKind.toInstr := by
  decide

theorem illegal_csr_row : findCsr? illegalCsrKind.addr = none := by
  decide

theorem picorv32_illegal_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.illegalBoundary arch input illegalWord) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := illegalNext arch, memory := input.memory }
        (illegalRetirement arch input) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  exact rvfi_core_adapter.CoreIllegalBoundary.to_rv32i_boundary
    (⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode,
      hboundary⟩ : rvfi_core_adapter.CoreIllegalBoundary d st entry arch input illegalWord)

theorem picorv32_illegal_csr_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.illegalBoundary arch input illegalCsrWord) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := illegalNext arch, memory := input.memory } (illegalRetirement arch input) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  exact rvfi_core_adapter.CoreIllegalBoundary.to_rv32i_boundary
    (⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode,
      hboundary⟩ : rvfi_core_adapter.CoreIllegalBoundary d st entry arch input illegalCsrWord)

#print axioms picorv32_illegal_loaded_rv32i_boundary_of_step
#print axioms picorv32_illegal_csr_loaded_rv32i_boundary_of_step

theorem picorv32_illegal_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word illegalWord) 0 =
      (illegalNext state, memory) := by
  exact isaStepMemWith_illegal cv32e40pProfile state memory illegalWord
    illegal_decode

theorem picorv32_illegal_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word illegalWord, memory := memory, irq := 0 } =
      (illegalNext state,
        illegalRetirement state
          { fetched := .word illegalWord, memory := memory, irq := 0 }) := by
  exact rvMachineWith_illegal cv32e40pProfile state memory illegalWord
    illegal_decode

theorem picorv32_illegal_csr_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word illegalCsrWord) 0 =
      (illegalNext state, memory) := by
  exact isaStepMemWith_illegal_csr cv32e40pProfile state memory
    illegalCsrWord illegalCsrKind illegal_csr_decode illegal_csr_row

theorem picorv32_illegal_csr_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word illegalCsrWord, memory := memory, irq := 0 } =
      (illegalNext state,
        illegalRetirement state
          { fetched := .word illegalCsrWord, memory := memory, irq := 0 }) := by
  exact rvMachineWith_illegal_csr cv32e40pProfile state memory
    illegalCsrWord illegalCsrKind illegal_csr_decode illegal_csr_row

/-! The raw trap fields determine the exact ISA step for both undecodable
    words and decoded CSR operations whose address is unimplemented. -/

theorem picorv32_illegal_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word)
    (hfields : observation.illegalFields state input word) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (illegalNext state, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) = none := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_illegal profile state memory word hdecode

theorem picorv32_illegal_csr_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (kind : CsrOpKind)
    (hfields : observation.illegalCsrFields state input word kind) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (illegalNext state, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) = some kind.toInstr :=
    hfields.2.2.1
  have hrow : findCsr? kind.addr = none := hfields.2.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_illegal_csr profile state memory word kind hdecode hrow

#print axioms picorv32_illegal_fields_isa_step
#print axioms picorv32_illegal_csr_fields_isa_step

#print axioms picorv32_illegal_class_step
#print axioms picorv32_illegal_class_commit
#print axioms picorv32_illegal_csr_class_step
#print axioms picorv32_illegal_csr_class_commit

end Examples.«system-verilog».cores.picorv32.r1_illegal
