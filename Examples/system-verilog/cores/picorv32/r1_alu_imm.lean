import LeanModels.Refine.RvfiAlu

/-!
# PicoRV32 R1 remaining immediate ALU class

The ADDI row is already recorded in `r1_addi`.  This file closes the other
nine RV32I OP-IMM forms.  Each fixed word is decoded by the exact ISA parser,
then threaded through the memory-preserving step and retirement boundary for
arbitrary architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_alu_imm

open LeanModels.Rv
open LeanModels.Refine

def sltiWord : Word := 0x06422193
def sltiuWord : Word := 0x06433293
def xoriWord : Word := 0x7ff44393
def oriWord : Word := 0x80056493
def andiWord : Word := 0x0ff67593
def slliWord : Word := 0x01f71693
def srliWord : Word := 0x00185793
def sraiWord : Word := 0x40795893
def addiNegWord : Word := 0xffb10093

theorem alu_imm_decodes :
    Fetched.decode (.word sltiWord) =
      some (.alu .slt 3 (.reg 4) (.imm 100)) ∧
    Fetched.decode (.word sltiuWord) =
      some (.alu .sltu 5 (.reg 6) (.imm 100)) ∧
    Fetched.decode (.word xoriWord) =
      some (.alu .xor 7 (.reg 8) (.imm 2047)) ∧
    Fetched.decode (.word oriWord) =
      some (.alu .or 9 (.reg 10) (.imm 0xFFFFF800)) ∧
    Fetched.decode (.word andiWord) =
      some (.alu .and 11 (.reg 12) (.imm 255)) ∧
    Fetched.decode (.word slliWord) =
      some (.alu .sll 13 (.reg 14) (.imm 31)) ∧
    Fetched.decode (.word srliWord) =
      some (.alu .srl 15 (.reg 16) (.imm 1)) ∧
    Fetched.decode (.word sraiWord) =
      some (.alu .sra 17 (.reg 18) (.imm 7)) ∧
    Fetched.decode (.word addiNegWord) =
      some (.alu .add 1 (.reg 2) (.imm 0xFFFFFFFB)) := by
  decide

theorem picorv32_slti_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sltiWord) 0 =
      (aluNext state .slt 3 (.reg 4) (.imm 100), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sltiWord .slt 3
    (.reg 4) (.imm 100) alu_imm_decodes.1

theorem picorv32_slti_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sltiWord, memory := memory, irq := 0 } =
      (aluNext state .slt 3 (.reg 4) (.imm 100),
        aluRetirement state
          { fetched := .word sltiWord, memory := memory, irq := 0 }
          .slt 3 (.reg 4) (.imm 100)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sltiWord .slt 3
    (.reg 4) (.imm 100) alu_imm_decodes.1

theorem picorv32_sltiu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sltiuWord) 0 =
      (aluNext state .sltu 5 (.reg 6) (.imm 100), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sltiuWord .sltu 5
    (.reg 6) (.imm 100) alu_imm_decodes.2.1

theorem picorv32_sltiu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sltiuWord, memory := memory, irq := 0 } =
      (aluNext state .sltu 5 (.reg 6) (.imm 100),
        aluRetirement state
          { fetched := .word sltiuWord, memory := memory, irq := 0 }
          .sltu 5 (.reg 6) (.imm 100)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sltiuWord .sltu 5
    (.reg 6) (.imm 100) alu_imm_decodes.2.1

theorem picorv32_xori_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word xoriWord) 0 =
      (aluNext state .xor 7 (.reg 8) (.imm 2047), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory xoriWord .xor 7
    (.reg 8) (.imm 2047) alu_imm_decodes.2.2.1

theorem picorv32_xori_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word xoriWord, memory := memory, irq := 0 } =
      (aluNext state .xor 7 (.reg 8) (.imm 2047),
        aluRetirement state
          { fetched := .word xoriWord, memory := memory, irq := 0 }
          .xor 7 (.reg 8) (.imm 2047)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory xoriWord .xor 7
    (.reg 8) (.imm 2047) alu_imm_decodes.2.2.1

theorem picorv32_ori_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word oriWord) 0 =
      (aluNext state .or 9 (.reg 10) (.imm 0xFFFFF800), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory oriWord .or 9
    (.reg 10) (.imm 0xFFFFF800) alu_imm_decodes.2.2.2.1

theorem picorv32_ori_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word oriWord, memory := memory, irq := 0 } =
      (aluNext state .or 9 (.reg 10) (.imm 0xFFFFF800),
        aluRetirement state
          { fetched := .word oriWord, memory := memory, irq := 0 }
          .or 9 (.reg 10) (.imm 0xFFFFF800)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory oriWord .or 9
    (.reg 10) (.imm 0xFFFFF800) alu_imm_decodes.2.2.2.1

theorem picorv32_andi_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word andiWord) 0 =
      (aluNext state .and 11 (.reg 12) (.imm 255), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory andiWord .and 11
    (.reg 12) (.imm 255) alu_imm_decodes.2.2.2.2.1

theorem picorv32_andi_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word andiWord, memory := memory, irq := 0 } =
      (aluNext state .and 11 (.reg 12) (.imm 255),
        aluRetirement state
          { fetched := .word andiWord, memory := memory, irq := 0 }
          .and 11 (.reg 12) (.imm 255)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory andiWord .and 11
    (.reg 12) (.imm 255) alu_imm_decodes.2.2.2.2.1

theorem picorv32_slli_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word slliWord) 0 =
      (aluNext state .sll 13 (.reg 14) (.imm 31), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory slliWord .sll 13
    (.reg 14) (.imm 31) alu_imm_decodes.2.2.2.2.2.1

theorem picorv32_slli_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word slliWord, memory := memory, irq := 0 } =
      (aluNext state .sll 13 (.reg 14) (.imm 31),
        aluRetirement state
          { fetched := .word slliWord, memory := memory, irq := 0 }
          .sll 13 (.reg 14) (.imm 31)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory slliWord .sll 13
    (.reg 14) (.imm 31) alu_imm_decodes.2.2.2.2.2.1

theorem picorv32_srli_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word srliWord) 0 =
      (aluNext state .srl 15 (.reg 16) (.imm 1), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory srliWord .srl 15
    (.reg 16) (.imm 1) alu_imm_decodes.2.2.2.2.2.2.1

theorem picorv32_srli_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word srliWord, memory := memory, irq := 0 } =
      (aluNext state .srl 15 (.reg 16) (.imm 1),
        aluRetirement state
          { fetched := .word srliWord, memory := memory, irq := 0 }
          .srl 15 (.reg 16) (.imm 1)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory srliWord .srl 15
    (.reg 16) (.imm 1) alu_imm_decodes.2.2.2.2.2.2.1

theorem picorv32_srai_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sraiWord) 0 =
      (aluNext state .sra 17 (.reg 18) (.imm 7), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sraiWord .sra 17
    (.reg 18) (.imm 7) alu_imm_decodes.2.2.2.2.2.2.2.1

theorem picorv32_srai_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sraiWord, memory := memory, irq := 0 } =
      (aluNext state .sra 17 (.reg 18) (.imm 7),
        aluRetirement state
          { fetched := .word sraiWord, memory := memory, irq := 0 }
          .sra 17 (.reg 18) (.imm 7)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sraiWord .sra 17
    (.reg 18) (.imm 7) alu_imm_decodes.2.2.2.2.2.2.2.1

theorem picorv32_addi_neg_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word addiNegWord) 0 =
      (aluNext state .add 1 (.reg 2) (.imm 0xFFFFFFFB), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory addiNegWord .add 1
    (.reg 2) (.imm 0xFFFFFFFB) alu_imm_decodes.2.2.2.2.2.2.2.2

theorem picorv32_addi_neg_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word addiNegWord, memory := memory, irq := 0 } =
      (aluNext state .add 1 (.reg 2) (.imm 0xFFFFFFFB),
        aluRetirement state
          { fetched := .word addiNegWord, memory := memory, irq := 0 }
          .add 1 (.reg 2) (.imm 0xFFFFFFFB)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory addiNegWord .add 1
    (.reg 2) (.imm 0xFFFFFFFB) alu_imm_decodes.2.2.2.2.2.2.2.2

#print axioms picorv32_slti_class_step
#print axioms picorv32_slti_class_commit
#print axioms picorv32_sltiu_class_step
#print axioms picorv32_sltiu_class_commit
#print axioms picorv32_xori_class_step
#print axioms picorv32_xori_class_commit
#print axioms picorv32_ori_class_step
#print axioms picorv32_ori_class_commit
#print axioms picorv32_andi_class_step
#print axioms picorv32_andi_class_commit
#print axioms picorv32_slli_class_step
#print axioms picorv32_slli_class_commit
#print axioms picorv32_srli_class_step
#print axioms picorv32_srli_class_commit
#print axioms picorv32_srai_class_step
#print axioms picorv32_srai_class_commit
#print axioms picorv32_addi_neg_class_step
#print axioms picorv32_addi_neg_class_commit

end Examples.«system-verilog».cores.picorv32.r1_alu_imm
