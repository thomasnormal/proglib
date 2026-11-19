import LeanModels.Refine.RvfiUpper
import Examples.«system-verilog».cores.picorv32.input_drive_core
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 upper-immediate class

The two RV32I upper-immediate instructions share the decoded ALU boundary but
select different first operands.  The fixed words below are checked by the
exact decoder, then threaded through the memory-preserving step and retirement
boundary for arbitrary architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_upper

open LeanModels.Rv
open LeanModels.Sv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32

def luiWord : Word := 0x123451b7
def auipcWord : Word := 0x12345197

theorem upper_decodes :
    Fetched.decode (.word luiWord) =
      some (.alu .add 3 (.reg 0) (.imm 0x12345000)) ∧
    Fetched.decode (.word auipcWord) =
      some (.alu .add 3 .pc (.imm 0x12345000)) := by
  decide

def luiInstruction : UpperInstruction :=
  { word := luiWord
    kind := .lui 3 0x12345000
    decode := upper_decodes.1 }

def auipcInstruction : UpperInstruction :=
  { word := auipcWord
    kind := .auipc 3 0x12345000
    decode := upper_decodes.2 }

theorem picorv32_lui_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word luiWord) 0 =
      (luiNext state 3 0x12345000, memory) := by
  exact isaStepMemWith_lui cv32e40pProfile state memory luiWord 3 0x12345000
    upper_decodes.1

theorem picorv32_lui_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word luiWord, memory := memory, irq := 0 } =
      (luiNext state 3 0x12345000,
        luiRetirement state
          { fetched := .word luiWord, memory := memory, irq := 0 }
          3 0x12345000) := by
  exact rvMachineWith_lui cv32e40pProfile state memory luiWord 3 0x12345000
    upper_decodes.1

theorem picorv32_auipc_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word auipcWord) 0 =
      (auipcNext state 3 0x12345000, memory) := by
  exact isaStepMemWith_auipc cv32e40pProfile state memory auipcWord 3
    0x12345000 upper_decodes.2

theorem picorv32_auipc_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word auipcWord, memory := memory, irq := 0 } =
      (auipcNext state 3 0x12345000,
        auipcRetirement state
          { fetched := .word auipcWord, memory := memory, irq := 0 }
          3 0x12345000) := by
  exact rvMachineWith_auipc cv32e40pProfile state memory auipcWord 3
    0x12345000 upper_decodes.2

/-! The raw upper-immediate fields determine the exact architectural step.
    LUI and AUIPC retain their distinct decoder operands in these bridges. -/

theorem picorv32_lui_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (rd : Reg) (imm : Word)
    (hfields : observation.luiFields state input word rd imm) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (luiNext state rd imm, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.alu .add rd (.reg 0) (.imm imm)) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_lui profile state memory word rd imm hdecode

theorem picorv32_auipc_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (rd : Reg) (imm : Word)
    (hfields : observation.auipcFields state input word rd imm) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (auipcNext state rd imm, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.alu .add rd .pc (.imm imm)) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_auipc profile state memory word rd imm hdecode

#print axioms picorv32_lui_fields_isa_step
#print axioms picorv32_auipc_fields_isa_step

/-! These wrappers connect exact loaded-core execution and decoder premises to
    the indexed dispatcher.  The raw upper boundary remains an explicit
    premise, so neither the source step nor the RVFI observation is inferred
    from the fixed instruction word. -/

theorem picorv32_lui_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation}
    {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.luiBoundary arch input luiWord 3 0x12345000) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := luiNext arch 3 0x12345000, memory := input.memory }
        (luiRetirement arch input 3 0x12345000) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by
    rw [d.fastStepCanonical_eq_step]
    exact hstep
  have hupper : rvfi_core_adapter.CoreUpperBoundary d st entry arch input
      luiInstruction := by
    refine ⟨next, observation,
      rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [luiInstruction, RvfiObservation.upperBoundary] using hboundary
  simpa [luiInstruction, UpperKind.next, UpperKind.retirement] using
    hupper.to_rv32i_boundary

theorem picorv32_auipc_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation}
    {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.auipcBoundary arch input auipcWord 3 0x12345000) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := auipcNext arch 3 0x12345000, memory := input.memory }
        (auipcRetirement arch input 3 0x12345000) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by
    rw [d.fastStepCanonical_eq_step]
    exact hstep
  have hupper : rvfi_core_adapter.CoreUpperBoundary d st entry arch input
      auipcInstruction := by
    refine ⟨next, observation,
      rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [auipcInstruction, RvfiObservation.upperBoundary] using hboundary
  simpa [auipcInstruction, UpperKind.next, UpperKind.retirement] using
    hupper.to_rv32i_boundary

#print axioms picorv32_lui_loaded_rv32i_boundary_of_step
#print axioms picorv32_auipc_loaded_rv32i_boundary_of_step

/-! One mixed-cycle consumer covers LUI and AUIPC while retaining the
    `UpperInstruction` witness and its exact source-shaped boundary. -/

theorem picorv32_upper_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    (instruction : UpperInstruction)
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
            input = upperProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.upperBoundary memoryState.arch input instruction ∧
            rel next
              { arch := UpperKind.next memoryState.arch instruction.kind,
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
          (rv32iProgramStep memoryState instruction.toRv32i)
          (rv32iProgramRetirement memoryState instruction.toRv32i) := by
        simpa [hmem, hinput, upperProgramInput, upper_toRv32i_step,
          upper_toRv32i_retirement] using
          (RvfiObservation.upperBoundary_rv32i instruction hboundary)
      simp only [↓reduceIte]
      exact ⟨instruction.toRv32i, by
        simpa [upper_toRv32i_input] using hinput,
        horder, hrvfi, by simpa [upper_toRv32i_step] using hnext⟩

#print axioms picorv32_upper_exact_cycle_step_refines

/-! The loaded upper-immediate consumer packages one exact
    `UpperInstruction` into the reset-specialized all-prefix contract. -/

theorem picorv32_loaded_upper_program_refinement_of_total
    (core : PicoRV32LoadedCanonicalE)
    (profile : PlatformProfile)
    (program : Memory)
    (initialArch : ArchState)
    (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF)
    (instruction : UpperInstruction)
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
            input = upperProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.upperBoundary memoryState.arch input instruction ∧
            rel next
              { arch := UpperKind.next memoryState.arch instruction.kind,
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
  have hstep' := picorv32_upper_exact_cycle_step_refines machine instruction hstep
  have hinitial : rel machine.toRvfiCycleMachine.init
      { arch := initialArch, memory := program } :=
    hrel _ _ (picoRV32_reset_relation_initial
      (PicoRV32LoadedCanonicalE.design core) program initialArch hpc hwf)
  refine ⟨machine, PicoRV32LoadedCanonicalE.loaded core, ?_⟩
  exact rv32i_progress_refinement profile machine.toRvfiCycleMachine rel admit
    hstep' 0 _ _ hinitial hschedule progress

#print axioms picorv32_loaded_upper_program_refinement_of_total

#print axioms picorv32_lui_class_step
#print axioms picorv32_lui_class_commit
#print axioms picorv32_auipc_class_step
#print axioms picorv32_auipc_class_commit

end Examples.«system-verilog».cores.picorv32.r1_upper
