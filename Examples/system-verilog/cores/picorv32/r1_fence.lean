import LeanModels.Refine.RvfiFence
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
open LeanModels.Refine

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

#print axioms picorv32_fence_loaded_rv32i_boundary_of_step
#print axioms picorv32_fenceI_loaded_rv32i_boundary_of_step

#print axioms picorv32_fence_class_step
#print axioms picorv32_fence_class_commit
#print axioms picorv32_fenceI_class_step
#print axioms picorv32_fenceI_class_commit

end Examples.«system-verilog».cores.picorv32.r1_fence
