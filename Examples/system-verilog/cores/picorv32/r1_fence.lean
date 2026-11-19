import LeanModels.Refine.RvfiFence
import Examples.«system-verilog».cores.picorv32.input_drive_core
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 fence class

The two RV32I fence operations are sequential no-register/no-memory commits.
Their fixed words are checked by the exact decoder, then threaded through the
memory-preserving step and retirement boundary for arbitrary architectural
state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_fence

open LeanModels.Rv
open LeanModels.Sv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32

def fenceWord : Word := 0x0000000f
def fenceIWord : Word := 0x0000100f

theorem fence_decodes :
    Fetched.decode (.word fenceWord) = some (.system .fence) ∧
    Fetched.decode (.word fenceIWord) = some (.system .fenceI) := by
  decide

def fenceInstruction : FenceInstruction :=
  { word := fenceWord, kind := .fence, decode := fence_decodes.1 }
def fenceIInstruction : FenceInstruction :=
  { word := fenceIWord, kind := .fenceI, decode := fence_decodes.2 }

theorem picorv32_fence_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word fenceWord) 0 =
      (fenceNext state .fence, memory) := by
  exact isaStepMemWith_fence cv32e40pProfile state memory fenceWord .fence
    fence_decodes.1

theorem picorv32_fence_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word fenceWord, memory := memory, irq := 0 } =
      (fenceNext state .fence,
        fenceRetirement state
          { fetched := .word fenceWord, memory := memory, irq := 0 }
          .fence) := by
  exact rvMachineWith_fence cv32e40pProfile state memory fenceWord .fence
    fence_decodes.1

theorem picorv32_fenceI_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word fenceIWord) 0 =
      (fenceNext state .fenceI, memory) := by
  exact isaStepMemWith_fence cv32e40pProfile state memory fenceIWord .fenceI
    fence_decodes.2

theorem picorv32_fenceI_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word fenceIWord, memory := memory, irq := 0 } =
      (fenceNext state .fenceI,
        fenceRetirement state
          { fetched := .word fenceIWord, memory := memory, irq := 0 }
          .fenceI) := by
  exact rvMachineWith_fence cv32e40pProfile state memory fenceIWord .fenceI
    fence_decodes.2

/-! The raw fence fields determine the exact memory-preserving ISA step for
    both `fence` and `fence.i`. -/

theorem picorv32_fence_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (kind : FenceKind)
    (hfields : observation.fenceFields state input word kind) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (fenceNext state kind, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.system kind.toSysOp) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_fence profile state memory word kind hdecode

#print axioms picorv32_fence_fields_isa_step

theorem picorv32_fence_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.fenceBoundary arch input fenceWord .fence) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := fenceNext arch .fence, memory := input.memory }
        (fenceRetirement arch input .fence) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreFenceBoundary d st entry arch input fenceInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [fenceInstruction] using hboundary
  simpa [fenceInstruction] using h.to_rv32i_boundary

theorem picorv32_fenceI_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.fenceBoundary arch input fenceIWord .fenceI) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := fenceNext arch .fenceI, memory := input.memory }
        (fenceRetirement arch input .fenceI) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreFenceBoundary d st entry arch input fenceIInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [fenceIInstruction] using hboundary
  simpa [fenceIInstruction] using h.to_rv32i_boundary

/-! One exact-cycle consumer covers FENCE and FENCE.I while retaining the
    operation kind and its memory-preserving architectural result. -/

theorem picorv32_fence_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    (instruction : FenceInstruction)
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
            input = fenceProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.fenceBoundary memoryState.arch input instruction.word
              instruction.kind ∧
            rel next
              { arch := fenceNext memoryState.arch instruction.kind,
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
          (rv32iProgramStep memoryState (.fence instruction))
          (rv32iProgramRetirement memoryState (.fence instruction)) := by
        simpa [hmem, hinput, fenceProgramInput, rv32iProgramStep,
          rv32iProgramRetirement] using
          (RvfiObservation.fenceBoundary_rv32i instruction.word
            instruction.kind hboundary)
      simp only [↓reduceIte]
      exact ⟨.fence instruction, by simpa [rv32iProgramInput] using hinput,
        horder, hrvfi, hnext⟩

#print axioms picorv32_fence_exact_cycle_step_refines

/-! The loaded fence consumer packages one exact FENCE or FENCE.I
    instruction into the reset-specialized all-prefix contract. -/

theorem picorv32_loaded_fence_program_refinement_of_total
    (core : PicoRV32LoadedCanonicalE)
    (profile : PlatformProfile)
    (program : Memory)
    (initialArch : ArchState)
    (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF)
    (instruction : FenceInstruction)
    (encode : LeanModels.Sv.Kernel.CoreMemState → Input → SvState)
    (htotal : ∀ (state : LeanModels.Sv.Kernel.CoreMemState) (input : Input),
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfi_core_adapter.rvfiStep (PicoRV32LoadedCanonicalE.design core)
              state (encode state input) = .ok (next, observation))
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hstep : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfi_core_adapter.rvfiStep (PicoRV32LoadedCanonicalE.design core)
              state (encode state input) = .ok (next, observation) ∧
          (if observation.valid then
            input = fenceProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.fenceBoundary memoryState.arch input instruction.word
              instruction.kind ∧
            rel next
              { arch := fenceNext memoryState.arch instruction.kind,
                memory := memoryState.memory }
          else rel next memoryState))
    (hrel : ∀ (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState),
      PicoRV32ResetRelation
        (PicoRV32LoadedCanonicalE.design core) program state memoryState →
      rel state memoryState)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (rvfi_core_adapter.CoreRvfiMachine.ofTotal encode htotal))
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (rvfi_core_adapter.CoreRvfiMachine.ofTotal encode htotal)).init
      schedule target) :
    ∃ machine : rvfi_core_adapter.CoreRvfiMachine
        (PicoRV32LoadedCanonicalE.design core),
      picorv32_core_mem = .ok (PicoRV32LoadedCanonicalE.design core) ∧
      Rv32iAllPrefixRefinement profile
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine machine)
        rel 0
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine machine).init
        { arch := initialArch, memory := program } schedule target := by
  let machine := rvfi_core_adapter.CoreRvfiMachine.ofTotal encode htotal
  have hstep' := picorv32_fence_exact_cycle_step_refines machine instruction hstep
  have hinitial : rel machine.toRvfiCycleMachine.init
      { arch := initialArch, memory := program } :=
    hrel _ _ (picoRV32_reset_relation_initial
      (PicoRV32LoadedCanonicalE.design core) program initialArch hpc hwf)
  refine ⟨machine, PicoRV32LoadedCanonicalE.loaded core, ?_⟩
  exact rv32i_progress_refinement profile machine.toRvfiCycleMachine rel admit
    hstep' 0 _ _ hinitial hschedule progress

#print axioms picorv32_loaded_fence_program_refinement_of_total

#print axioms picorv32_fence_loaded_rv32i_boundary_of_step
#print axioms picorv32_fenceI_loaded_rv32i_boundary_of_step

#print axioms picorv32_fence_class_step
#print axioms picorv32_fence_class_commit
#print axioms picorv32_fenceI_class_step
#print axioms picorv32_fenceI_class_commit

end Examples.«system-verilog».cores.picorv32.r1_fence
