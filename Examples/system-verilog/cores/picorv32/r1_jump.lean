import LeanModels.Refine.RvfiJump

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

#print axioms picorv32_jal_class_step
#print axioms picorv32_jal_class_commit
#print axioms picorv32_jalr_class_step
#print axioms picorv32_jalr_class_commit

end Examples.«system-verilog».cores.picorv32.r1_jump
