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

end Examples.«system-verilog».cores.picorv32.r1_rv32i
