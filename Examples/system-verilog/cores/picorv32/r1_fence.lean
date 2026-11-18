import LeanModels.Refine.RvfiFence

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

#print axioms picorv32_fence_class_step
#print axioms picorv32_fence_class_commit
#print axioms picorv32_fenceI_class_step
#print axioms picorv32_fenceI_class_commit

end Examples.«system-verilog».cores.picorv32.r1_fence
