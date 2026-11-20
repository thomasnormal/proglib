import LeanModels.Refine.RvfiTrap
import Examples.«system-verilog».cores.picorv32.input_drive_core
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
open LeanModels.Sv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32

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

/-! The two trap shapes share one exact-cycle consumer.  The retained
    `TrapInstruction` keeps undecodable words distinct from decoded CSR words
    whose table row is absent, while both route to the illegal RV32I step. -/

theorem picorv32_illegal_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    (instruction : TrapInstruction)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hstep : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfi_core_adapter.rvfiStep d state (machine.encode state input) =
            .ok (next, observation) ∧
          (if observation.valid then
            input = trapProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.illegalBoundary memoryState.arch input
              instruction.wordOf ∧
            rel next
              { arch := illegalNext memoryState.arch,
                memory := memoryState.memory }
          else rel next memoryState)) :
    Rv32iLegacyCycleStepRefines machine.toRvfiCycleMachine rel admit := by
  apply machine.to_rv32i_step_refines
  intro start state memoryState input hrel hadmit
  rcases hstep start state memoryState input hrel hadmit with
    ⟨next, observation, hrun, hcase⟩
  refine ⟨next, observation, hrun, ?_⟩
  cases hv : observation.valid with
  | false =>
      simpa [hv] using hcase
  | true =>
      simp only [hv, ↓reduceIte] at hcase
      rcases hcase with ⟨hinput, horder, hboundary, hnext⟩
      have hmem : input.memory = memoryState.memory := by
        rw [hinput]
        rfl
      have hrvfi : Rv32iBoundary memoryState.arch input observation
          (rv32iProgramStep memoryState (.trap instruction))
          (rv32iProgramRetirement memoryState (.trap instruction)) := by
        simpa [hmem, hinput, trapProgramInput, rv32iProgramStep,
          rv32iProgramRetirement] using
          (RvfiObservation.illegalBoundary_rv32i instruction.wordOf hboundary)
      simp only [↓reduceIte]
      exact ⟨.trap instruction, by simpa [rv32iProgramInput] using hinput,
        horder, hrvfi, hnext⟩

#print axioms picorv32_illegal_exact_cycle_step_refines

/-! The loaded illegal consumer packages one exact undecodable or
    unimplemented-CSR trap into the reset-specialized all-prefix contract. -/

end Examples.«system-verilog».cores.picorv32.r1_illegal
