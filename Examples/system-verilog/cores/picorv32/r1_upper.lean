import LeanModels.Refine.RvfiUpper

/-!
# PicoRV32 R1 upper-immediate class

The two RV32I upper-immediate instructions share the decoded ALU boundary but
select different first operands.  The fixed words below are checked by the
exact decoder, then threaded through the memory-preserving step and retirement
boundary for arbitrary architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_upper

open LeanModels.Rv
open LeanModels.Refine

def luiWord : Word := 0x123451b7
def auipcWord : Word := 0x12345197

theorem upper_decodes :
    Fetched.decode (.word luiWord) =
      some (.alu .add 3 (.reg 0) (.imm 0x12345000)) ∧
    Fetched.decode (.word auipcWord) =
      some (.alu .add 3 .pc (.imm 0x12345000)) := by
  decide

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

#print axioms picorv32_lui_class_step
#print axioms picorv32_lui_class_commit
#print axioms picorv32_auipc_class_step
#print axioms picorv32_auipc_class_commit

end Examples.«system-verilog».cores.picorv32.r1_upper
