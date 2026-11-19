import LeanModels.Refine.RvfiMem
import Examples.«system-verilog».cores.picorv32.rvfi_lw_boundary
import Examples.«system-verilog».cores.picorv32.rvfi_sw_boundary
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 word-memory class

This is the next R1 class after ADDI.  The two pinned RV32I words are the
PicoRV32 memory-interface forms used by the simulator probe, and the theorem
quantifies over the architectural state and byte memory.  The exact RVFI
boundary is the premise a future loaded-core invariant must establish.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_mem

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32
open Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

def lwWord : Word := 0x10002103
def swWord : Word := 0x10102023

theorem lwWord_decode :
    Fetched.decode (.word lwWord) =
      some (.mem (.load true) .word (2 : Reg) (0 : Reg) (0x100 : Word)) := by
  decide

theorem swWord_decode :
    Fetched.decode (.word swWord) =
      some (.mem .store .word (1 : Reg) (0 : Reg) (0x100 : Word)) := by
  decide

theorem picorv32_lw_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lwWord) 0 =
      (lwNext state memory 2 0 0x100, memory) := by
  exact isaStepMemWith_lw cv32e40pProfile state memory lwWord 2 0 0x100
    lwWord_decode

theorem picorv32_lw_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lwWord, memory := memory, irq := 0 } =
      (lwNext state memory 2 0 0x100,
        lwRetirement state
          { fetched := .word lwWord, memory := memory, irq := 0 }
          2 0 0x100) := by
  exact rvMachineWith_lw cv32e40pProfile state memory lwWord 2 0 0x100
    lwWord_decode

theorem picorv32_sw_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word swWord) 0 =
      (swNext state, storeVal memory .word
        (state.readReg 0 + 0x100) (state.readReg 1)) := by
  exact isaStepMemWith_sw cv32e40pProfile state memory swWord 0 1 0x100
    swWord_decode

theorem picorv32_sw_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word swWord, memory := memory, irq := 0 } =
      (swNext state,
        swRetirement state
          { fetched := .word swWord, memory := memory, irq := 0 }
          0 1 0x100) := by
  exact rvMachineWith_sw cv32e40pProfile state memory swWord 0 1 0x100
    swWord_decode

/-! The raw word-memory fields determine the exact threaded ISA step.  The
    store bridge retains the resulting memory update, while the load bridge
    retains the supplied memory as unchanged architectural state. -/

theorem picorv32_sw_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (rs1 rs2 : Reg) (imm : Word)
    (hfields : observation.swFields state input word rs1 rs2 imm) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (swNext state,
        storeVal input.memory .word (state.readReg rs1 + imm)
          (state.readReg rs2)) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.mem .store .word rs2 rs1 imm) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_sw profile state memory word rs1 rs2 imm hdecode

theorem picorv32_lw_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (rd rs1 : Reg) (imm : Word)
    (hfields : observation.lwFields state input word rd rs1 imm) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (lwNext state input.memory rd rs1 imm, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.mem (.load true) .word rd rs1 imm) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_lw profile state memory word rd rs1 imm hdecode

#print axioms picorv32_sw_fields_isa_step
#print axioms picorv32_lw_fields_isa_step

/-! These wrappers connect the measured memory-row predicates to the loaded
    canonical adapter.  The exact source step and decoder result remain
    premises, so the wrappers preserve the boundary evidence instead of
    manufacturing a memory response. -/

theorem picorv32_lw_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.lwBoundary rvfi_lw_boundary.loadState
      rvfi_lw_boundary.loadInput lwWord 2 0 0x100) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation') ∧
      Rv32iBoundary rvfi_lw_boundary.loadState
        rvfi_lw_boundary.loadInput observation'
        { arch := lwNext rvfi_lw_boundary.loadState
            rvfi_lw_boundary.loadInput.memory 2 0 0x100,
          memory := rvfi_lw_boundary.loadInput.memory }
        (lwRetirement rvfi_lw_boundary.loadState
          rvfi_lw_boundary.loadInput 2 0 0x100) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by
    rw [d.fastStepCanonical_eq_step]
    exact hstep
  exact (rvfi_core_adapter.CoreLoadBoundary.to_rv32i_boundary
    (⟨next, observation,
      rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode,
      hboundary⟩ : rvfi_core_adapter.CoreLoadBoundary d st entry
        rvfi_lw_boundary.loadState rvfi_lw_boundary.loadInput
        lwWord 2 0 0x100))

theorem picorv32_sw_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.swBoundary rvfi_sw_boundary.storeState
      rvfi_sw_boundary.storeInput swWord 0 1 0x100) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation') ∧
      Rv32iBoundary rvfi_sw_boundary.storeState
        rvfi_sw_boundary.storeInput observation'
        { arch := swNext rvfi_sw_boundary.storeState,
          memory := LeanModels.Rv.storeVal
            rvfi_sw_boundary.storeInput.memory .word
            (rvfi_sw_boundary.storeState.readReg 0 + 0x100)
            (rvfi_sw_boundary.storeState.readReg 1) }
        (swRetirement rvfi_sw_boundary.storeState
          rvfi_sw_boundary.storeInput 0 1 0x100) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by
    rw [d.fastStepCanonical_eq_step]
    exact hstep
  exact (rvfi_core_adapter.CoreStoreBoundary.to_rv32i_boundary
    (⟨next, observation,
      rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode,
      hboundary⟩ : rvfi_core_adapter.CoreStoreBoundary d st entry
        rvfi_sw_boundary.storeState rvfi_sw_boundary.storeInput
        swWord 0 1 0x100))

#print axioms picorv32_lw_loaded_rv32i_boundary_of_step
#print axioms picorv32_sw_loaded_rv32i_boundary_of_step

#print axioms picorv32_lw_class_step
#print axioms picorv32_lw_class_commit
#print axioms picorv32_sw_class_step
#print axioms picorv32_sw_class_commit

end Examples.«system-verilog».cores.picorv32.r1_mem
