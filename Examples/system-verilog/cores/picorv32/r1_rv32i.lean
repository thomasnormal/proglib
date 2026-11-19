import Examples.«system-verilog».cores.picorv32.input_drive_core
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 RV32I consumer

This is the all-family loaded-core boundary named by the R2 consumption map.
The source-step and exact decoder result remain premises of the theorem.  The
bridge therefore does not turn the finite canonical-E receipt into a universal
claim about the RTL.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_rv32i

open LeanModels.Rv
open LeanModels.Sv
open LeanModels.Sv.Kernel
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32
open Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

set_option autoImplicit false

theorem picorv32_loaded_rv32i_exact_cycle_step_refines
    (core : PicoRV32LoadedCanonicalE)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hstep : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfiStep (PicoRV32LoadedCanonicalE.design core) state
              ((CoreRvfiMachine.encode (PicoRV32LoadedCanonicalE.machine core))
                state input) = .ok (next, observation) ∧
          (if observation.valid then
            ∃ instruction : Rv32iInstruction,
              input = rv32iProgramInput memoryState instruction ∧
              observation.order = start ∧
              Rv32iBoundary memoryState.arch input observation
                (rv32iProgramStep memoryState instruction)
                (rv32iProgramRetirement memoryState instruction) ∧
              rel next (rv32iProgramStep memoryState instruction)
          else rel next memoryState)) :
    picorv32_core_mem = .ok (PicoRV32LoadedCanonicalE.design core) ∧
      Rv32iCycleStepRefines
        (CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)) rel admit := by
  refine ⟨PicoRV32LoadedCanonicalE.loaded core, ?_⟩
  exact (PicoRV32LoadedCanonicalE.machine core).to_rv32i_step_refines hstep

#print axioms picorv32_loaded_rv32i_exact_cycle_step_refines

/-! The loaded machine's reset state has a concrete canonical-E relation.
    Register-file and program-memory correspondence remain separate fields of
    the eventual R2 relation. -/

theorem picorv32_loaded_reset_relation_initial
    (core : PicoRV32LoadedCanonicalE) (program : Memory)
    (initialArch : ArchState) (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF) :
    PicoRV32ResetRelation
      (PicoRV32LoadedCanonicalE.design core) program
      (CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)).init
      { arch := initialArch, memory := program } := by
  exact picoRV32_reset_relation_initial
    (PicoRV32LoadedCanonicalE.design core) program initialArch hpc hwf

#print axioms picorv32_loaded_reset_relation_initial

/-! The reset relation carries the architectural well-formedness premise
    consumed by the mixed program fold.  This theorem transports that premise
    through every architectural instruction prefix without making any claim
    about the loaded core's future steps. -/

theorem picorv32_reset_relation_program_state_preserves_WF
    {design : CoreMemDesign} {program : Memory}
    {state : CoreMemState} {memoryState : RvMemoryState}
    (hreset : PicoRV32ResetRelation design program state memoryState)
    (instructions : List Rv32iInstruction) :
    (rv32iProgramState memoryState instructions).arch.WF := by
  exact rv32iProgramState_preserves_WF memoryState instructions hreset.arch_wf

#print axioms picorv32_reset_relation_program_state_preserves_WF

/-! The loaded reset constructor supplies the explicit relation used by the
    preceding transport theorem. -/

theorem picorv32_loaded_initial_program_state_preserves_WF
    (core : PicoRV32LoadedCanonicalE) (program : Memory)
    (initialArch : ArchState) (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF) (instructions : List Rv32iInstruction) :
    (rv32iProgramState
      { arch := initialArch, memory := program } instructions).arch.WF := by
  apply picorv32_reset_relation_program_state_preserves_WF
    (instructions := instructions)
  exact picorv32_loaded_reset_relation_initial core program initialArch hpc hwf

#print axioms picorv32_loaded_initial_program_state_preserves_WF

/-! The loaded all-family step certificate composes with the public reset
    theorem.  Initial relation, admitted inputs, and progress stay explicit
    because none follows from a finite E-RUN receipt. -/

theorem picorv32_loaded_rv32i_reset_refinement
    (core : PicoRV32LoadedCanonicalE)
    (profile : PlatformProfile)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hstep : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfiStep (PicoRV32LoadedCanonicalE.design core) state
              ((CoreRvfiMachine.encode (PicoRV32LoadedCanonicalE.machine core))
                state input) = .ok (next, observation) ∧
          (if observation.valid then
            ∃ instruction : Rv32iInstruction,
              input = rv32iProgramInput memoryState instruction ∧
              observation.order = start ∧
              Rv32iBoundary memoryState.arch input observation
                (rv32iProgramStep memoryState instruction)
                (rv32iProgramRetirement memoryState instruction) ∧
              rel next (rv32iProgramStep memoryState instruction)
          else rel next memoryState))
    (hinit : rel
      (CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)).init
      (rvMemoryMachineWith profile).init)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget
      (CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core))
      (CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)).init schedule target) :
    picorv32_core_mem = .ok (PicoRV32LoadedCanonicalE.design core) ∧
      Rv32iResetRefinement profile
        (CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)) rel schedule target := by
  have hloaded := picorv32_loaded_rv32i_exact_cycle_step_refines
    core hstep
  refine ⟨hloaded.1, ?_⟩
  exact rv32i_reset_refinement profile
    (CoreRvfiMachine.toRvfiCycleMachine
      (PicoRV32LoadedCanonicalE.machine core)) rel admit hloaded.2 hinit
    hschedule progress

#print axioms picorv32_loaded_rv32i_reset_refinement

/-! The program-image form consumes the concrete reset relation instead of
    asking a caller to restate that the loaded E machine starts at
    `design.initial`.  The bridge into the eventual architectural relation is
    still explicit, and the reset architectural state is supplied by the
    caller rather than selected here. -/

theorem picorv32_loaded_rv32i_program_refinement_from_initial_relation
    (core : PicoRV32LoadedCanonicalE)
    (profile : PlatformProfile)
    (program : Memory)
    (initialArch : ArchState)
    (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hrel : ∀ (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState),
      PicoRV32ResetRelation
        (PicoRV32LoadedCanonicalE.design core) program
        state memoryState → rel state memoryState)
    (hstep : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfiStep (PicoRV32LoadedCanonicalE.design core) state
              ((CoreRvfiMachine.encode (PicoRV32LoadedCanonicalE.machine core))
                state input) = .ok (next, observation) ∧
          (if observation.valid then
            ∃ instruction : Rv32iInstruction,
              input = rv32iProgramInput memoryState instruction ∧
              observation.order = start ∧
              Rv32iBoundary memoryState.arch input observation
                (rv32iProgramStep memoryState instruction)
                (rv32iProgramRetirement memoryState instruction) ∧
              rel next (rv32iProgramStep memoryState instruction)
          else rel next memoryState))
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget
      (CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core))
      (CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)).init schedule target) :
    picorv32_core_mem = .ok (PicoRV32LoadedCanonicalE.design core) ∧
      Rv32iAllPrefixRefinement profile
        (CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)) rel 0
        (CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)).init
        { arch := initialArch, memory := program } schedule target := by
  have hloaded := picorv32_loaded_rv32i_exact_cycle_step_refines core hstep
  have hinitial : rel
      (CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)).init
      { arch := initialArch, memory := program } :=
    hrel _ _ (picoRV32_reset_relation_initial
      (PicoRV32LoadedCanonicalE.design core) program initialArch hpc hwf)
  refine ⟨hloaded.1, ?_⟩
  exact rv32i_progress_refinement profile
    (CoreRvfiMachine.toRvfiCycleMachine
      (PicoRV32LoadedCanonicalE.machine core)) rel admit hloaded.2
    0 _ _ hinitial hschedule progress

#print axioms picorv32_loaded_rv32i_program_refinement_from_initial_relation

/-! The all-family program contract can likewise start from total canonical
    execution.  The generated machine remains tied to the exact `rvfiStep`
    witnesses, while the reset relation, admitted schedule, progress, and
    indexed RV32I boundary stay explicit premises. -/

theorem picorv32_loaded_rv32i_program_refinement_of_total
    (core : PicoRV32LoadedCanonicalE)
    (profile : PlatformProfile)
    (program : Memory)
    (initialArch : ArchState)
    (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF)
    (encode : LeanModels.Sv.Kernel.CoreMemState → Input → SvState)
    (htotal : ∀ (state : LeanModels.Sv.Kernel.CoreMemState) (input : Input),
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfiStep (PicoRV32LoadedCanonicalE.design core) state
              (encode state input) = .ok (next, observation))
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hrel : ∀ (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState),
      PicoRV32ResetRelation
        (PicoRV32LoadedCanonicalE.design core) program state memoryState →
      rel state memoryState)
    (hstep : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfiStep (PicoRV32LoadedCanonicalE.design core) state
              (encode state input) = .ok (next, observation) ∧
          (if observation.valid then
            ∃ instruction : Rv32iInstruction,
              input = rv32iProgramInput memoryState instruction ∧
              observation.order = start ∧
              Rv32iBoundary memoryState.arch input observation
                (rv32iProgramStep memoryState instruction)
                (rv32iProgramRetirement memoryState instruction) ∧
              rel next (rv32iProgramStep memoryState instruction)
          else rel next memoryState))
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
  have hmachine := rvfi_core_adapter.CoreRvfiMachine.to_rv32i_step_refines
    machine hstep
  have hinitial : rel machine.toRvfiCycleMachine.init
      { arch := initialArch, memory := program } :=
    hrel _ _ (picoRV32_reset_relation_initial
      (PicoRV32LoadedCanonicalE.design core) program initialArch hpc hwf)
  refine ⟨machine, PicoRV32LoadedCanonicalE.loaded core, ?_⟩
  exact rv32i_progress_refinement profile machine.toRvfiCycleMachine rel admit
    hmachine 0 _ _ hinitial hschedule progress

#print axioms picorv32_loaded_rv32i_program_refinement_of_total

end Examples.«system-verilog».cores.picorv32.r1_rv32i
