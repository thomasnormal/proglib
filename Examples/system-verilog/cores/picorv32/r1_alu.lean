import LeanModels.Refine.RvfiAlu

/-!
# PicoRV32 R1 register-register ALU class

The pinned PicoRV32 RVFI program uses the standard RV32I register-register
encodings.  This file covers the complete ten-operation ALU family.  Each
word is decoded by the exact ISA parser, then threaded through the
memory-preserving step and retirement boundary for arbitrary architectural
state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_alu

open LeanModels.Rv
open LeanModels.Refine

def addWord : Word := 0x002081b3
def subWord : Word := 0x402081b3
def sllWord : Word := 0x002091b3
def sltWord : Word := 0x0020a1b3
def sltuWord : Word := 0x0020b1b3
def xorWord : Word := 0x0020c1b3
def srlWord : Word := 0x0020d1b3
def sraWord : Word := 0x4020d1b3
def orWord : Word := 0x0020e1b3
def andWord : Word := 0x0020f1b3

theorem alu_decodes :
    Fetched.decode (.word addWord) = some (.alu .add 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word subWord) = some (.alu .sub 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word sllWord) = some (.alu .sll 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word sltWord) = some (.alu .slt 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word sltuWord) = some (.alu .sltu 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word xorWord) = some (.alu .xor 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word srlWord) = some (.alu .srl 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word sraWord) = some (.alu .sra 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word orWord) = some (.alu .or 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word andWord) = some (.alu .and 3 (.reg 1) (.reg 2)) := by
  decide

theorem picorv32_add_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word addWord) 0 =
      (aluNext state .add 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory addWord .add 3
    (.reg 1) (.reg 2) alu_decodes.1

theorem picorv32_add_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word addWord, memory := memory, irq := 0 } =
      (aluNext state .add 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word addWord, memory := memory, irq := 0 }
          .add 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory addWord .add 3
    (.reg 1) (.reg 2) alu_decodes.1

theorem picorv32_sub_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word subWord) 0 =
      (aluNext state .sub 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory subWord .sub 3
    (.reg 1) (.reg 2) alu_decodes.2.1

theorem picorv32_sub_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word subWord, memory := memory, irq := 0 } =
      (aluNext state .sub 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word subWord, memory := memory, irq := 0 }
          .sub 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory subWord .sub 3
    (.reg 1) (.reg 2) alu_decodes.2.1

theorem picorv32_sll_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sllWord) 0 =
      (aluNext state .sll 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sllWord .sll 3
    (.reg 1) (.reg 2) alu_decodes.2.2.1

theorem picorv32_sll_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sllWord, memory := memory, irq := 0 } =
      (aluNext state .sll 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word sllWord, memory := memory, irq := 0 }
          .sll 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sllWord .sll 3
    (.reg 1) (.reg 2) alu_decodes.2.2.1

theorem picorv32_slt_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sltWord) 0 =
      (aluNext state .slt 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sltWord .slt 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.1

theorem picorv32_slt_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sltWord, memory := memory, irq := 0 } =
      (aluNext state .slt 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word sltWord, memory := memory, irq := 0 }
          .slt 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sltWord .slt 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.1

theorem picorv32_sltu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sltuWord) 0 =
      (aluNext state .sltu 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sltuWord .sltu 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.1

theorem picorv32_sltu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sltuWord, memory := memory, irq := 0 } =
      (aluNext state .sltu 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word sltuWord, memory := memory, irq := 0 }
          .sltu 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sltuWord .sltu 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.1

theorem picorv32_xor_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word xorWord) 0 =
      (aluNext state .xor 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory xorWord .xor 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.1

theorem picorv32_xor_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word xorWord, memory := memory, irq := 0 } =
      (aluNext state .xor 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word xorWord, memory := memory, irq := 0 }
          .xor 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory xorWord .xor 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.1

theorem picorv32_srl_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word srlWord) 0 =
      (aluNext state .srl 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory srlWord .srl 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.1

theorem picorv32_srl_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word srlWord, memory := memory, irq := 0 } =
      (aluNext state .srl 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word srlWord, memory := memory, irq := 0 }
          .srl 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory srlWord .srl 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.1

theorem picorv32_sra_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sraWord) 0 =
      (aluNext state .sra 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sraWord .sra 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.1

theorem picorv32_sra_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sraWord, memory := memory, irq := 0 } =
      (aluNext state .sra 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word sraWord, memory := memory, irq := 0 }
          .sra 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sraWord .sra 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.1

theorem picorv32_or_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word orWord) 0 =
      (aluNext state .or 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory orWord .or 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.2.1

theorem picorv32_or_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word orWord, memory := memory, irq := 0 } =
      (aluNext state .or 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word orWord, memory := memory, irq := 0 }
          .or 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory orWord .or 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.2.1

theorem picorv32_and_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word andWord) 0 =
      (aluNext state .and 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory andWord .and 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.2.2

theorem picorv32_and_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word andWord, memory := memory, irq := 0 } =
      (aluNext state .and 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word andWord, memory := memory, irq := 0 }
          .and 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory andWord .and 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.2.2

#print axioms picorv32_add_class_step
#print axioms picorv32_add_class_commit
#print axioms picorv32_sub_class_step
#print axioms picorv32_sub_class_commit
#print axioms picorv32_sll_class_step
#print axioms picorv32_sll_class_commit
#print axioms picorv32_slt_class_step
#print axioms picorv32_slt_class_commit
#print axioms picorv32_sltu_class_step
#print axioms picorv32_sltu_class_commit
#print axioms picorv32_xor_class_step
#print axioms picorv32_xor_class_commit
#print axioms picorv32_srl_class_step
#print axioms picorv32_srl_class_commit
#print axioms picorv32_sra_class_step
#print axioms picorv32_sra_class_commit
#print axioms picorv32_or_class_step
#print axioms picorv32_or_class_commit
#print axioms picorv32_and_class_step
#print axioms picorv32_and_class_commit

end Examples.«system-verilog».cores.picorv32.r1_alu
