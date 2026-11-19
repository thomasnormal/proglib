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
    (core : PicoRV32LoadedCanonicalE) (program : Memory) :
    PicoRV32ResetRelation
      (PicoRV32LoadedCanonicalE.design core) program
      (CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)).init
      { arch := ArchState.init 0, memory := program } := by
  exact picoRV32_reset_relation_initial
    (PicoRV32LoadedCanonicalE.design core) program

#print axioms picorv32_loaded_reset_relation_initial

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

end Examples.«system-verilog».cores.picorv32.r1_rv32i
