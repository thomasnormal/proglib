import LeanModels.Refine.RvfiJump
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 jump class

The measured PicoRV32 jump rows cover the RV32I JAL and JALR forms.  The
fixed words are decoded by the exact ISA parser, then threaded through the
memory-preserving step and retirement boundaries for arbitrary architectural
state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_jump

open LeanModels.Rv
open LeanModels.Refine

def jalWord : Word := 0x008000ef
def jalrWord : Word := 0x100000e7

theorem jump_decodes :
    Fetched.decode (.word jalWord) = some (.jump 1 .pc 8) ∧
    Fetched.decode (.word jalrWord) = some (.jump 1 (.reg 0) 0x100) := by
  decide

def jalInstruction : JumpInstruction :=
  { word := jalWord
    kind := .jal 1 8
    decode := jump_decodes.1 }

def jalrInstruction : JumpInstruction :=
  { word := jalrWord
    kind := .jalr 1 0 0x100
    decode := jump_decodes.2 }

theorem picorv32_jal_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word jalWord) 0 =
      (jalNext state 1 8, memory) := by
  exact isaStepMemWith_jal cv32e40pProfile state memory jalWord 1 8
    jump_decodes.1

theorem picorv32_jal_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word jalWord, memory := memory, irq := 0 } =
      (jalNext state 1 8,
        jalRetirement state
          { fetched := .word jalWord, memory := memory, irq := 0 } 1 8) := by
  exact rvMachineWith_jal cv32e40pProfile state memory jalWord 1 8
    jump_decodes.1

theorem picorv32_jalr_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word jalrWord) 0 =
      (jalrNext state 1 0 0x100, memory) := by
  exact isaStepMemWith_jalr cv32e40pProfile state memory jalrWord 1 0 0x100
    jump_decodes.2

theorem picorv32_jalr_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word jalrWord, memory := memory, irq := 0 } =
      (jalrNext state 1 0 0x100,
        jalrRetirement state
          { fetched := .word jalrWord, memory := memory, irq := 0 } 1 0 0x100) := by
  exact rvMachineWith_jalr cv32e40pProfile state memory jalrWord 1 0 0x100
    jump_decodes.2

/-! The raw JAL and JALR fields determine their exact architectural steps.
    The two decoder shapes remain separate so the bridge cannot erase JALR's
    source-register read or low-bit target rule. -/

theorem picorv32_jal_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (rd : Reg) (offset : Word)
    (hfields : observation.jalFields state input word rd offset) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (jalNext state rd offset, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.jump rd .pc offset) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_jal profile state memory word rd offset hdecode

theorem picorv32_jalr_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (rd rs1 : Reg) (offset : Word)
    (hfields : observation.jalrFields state input word rd rs1 offset) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (jalrNext state rd rs1 offset, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.jump rd (.reg rs1) offset) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_jalr profile state memory word rd rs1 offset hdecode

#print axioms picorv32_jal_fields_isa_step
#print axioms picorv32_jalr_fields_isa_step

/-! These wrappers connect exact loaded-core execution and decoder premises to
    the indexed dispatcher.  JAL and JALR retain distinct raw boundaries while
    sharing one decoded jump-family witness. -/

theorem picorv32_jal_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation}
    {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.jalBoundary arch input jalWord 1 8) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := jalNext arch 1 8, memory := input.memory }
        (jalRetirement arch input 1 8) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by
    rw [d.fastStepCanonical_eq_step]
    exact hstep
  have hjump : rvfi_core_adapter.CoreJumpBoundary d st entry arch input
      jalInstruction := by
    refine ⟨next, observation,
      rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [jalInstruction, RvfiObservation.jumpBoundary] using hboundary
  simpa [jalInstruction, JumpKind.next, JumpKind.retirement] using
    hjump.to_rv32i_boundary

theorem picorv32_jalr_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation}
    {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.jalrBoundary arch input jalrWord 1 0 0x100) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := jalrNext arch 1 0 0x100, memory := input.memory }
        (jalrRetirement arch input 1 0 0x100) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by
    rw [d.fastStepCanonical_eq_step]
    exact hstep
  have hjump : rvfi_core_adapter.CoreJumpBoundary d st entry arch input
      jalrInstruction := by
    refine ⟨next, observation,
      rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [jalrInstruction, RvfiObservation.jumpBoundary] using hboundary
  simpa [jalrInstruction, JumpKind.next, JumpKind.retirement] using
    hjump.to_rv32i_boundary

#print axioms picorv32_jal_loaded_rv32i_boundary_of_step
#print axioms picorv32_jalr_loaded_rv32i_boundary_of_step

/-! The loaded jump family has one exact-cycle consumer for both JAL and
    JALR.  The retained `JumpInstruction` keeps their distinct target
    semantics in the mixed dispatcher. -/

theorem picorv32_jump_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    (instruction : JumpInstruction)
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
            input = jumpProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.jumpBoundary memoryState.arch input instruction ∧
            rel next
              { arch := JumpKind.next memoryState.arch instruction.kind,
                memory := memoryState.memory }
          else rel next memoryState)) :
    Rv32iCycleStepRefines machine.toRvfiCycleMachine rel admit := by
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
          (rv32iProgramStep memoryState (.jump instruction))
          (rv32iProgramRetirement memoryState (.jump instruction)) := by
        simpa [hmem, hinput, jumpProgramInput, rv32iProgramStep,
          rv32iProgramRetirement] using
          (RvfiObservation.jumpBoundary_rv32i instruction hboundary)
      simp only [↓reduceIte]
      exact ⟨.jump instruction, by simpa [rv32iProgramInput] using hinput,
        horder, hrvfi, by simpa [rv32iProgramStep] using hnext⟩

#print axioms picorv32_jump_exact_cycle_step_refines

#print axioms picorv32_jal_class_step
#print axioms picorv32_jal_class_commit
#print axioms picorv32_jalr_class_step
#print axioms picorv32_jalr_class_commit

end Examples.«system-verilog».cores.picorv32.r1_jump
