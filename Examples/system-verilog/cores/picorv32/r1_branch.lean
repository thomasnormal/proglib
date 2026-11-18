import LeanModels.Refine.RvfiBranch

/-!
# PicoRV32 R1 conditional-branch class

The six RV32I conditional-branch encodings use the pinned core's 32-bit
instruction width and a common offset.  Each theorem quantifies over the
architectural state and byte memory, so the loaded-core proof only needs to
establish the corresponding raw RVFI boundary.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_branch

open LeanModels.Rv
open LeanModels.Refine

def beqWord : Word := 0x00000463
def bneWord : Word := 0x00001463
def bltWord : Word := 0x00004463
def bgeWord : Word := 0x00005463
def bltuWord : Word := 0x00006463
def bgeuWord : Word := 0x00007463

theorem branch_decodes :
    Fetched.decode (.word beqWord) = some (.branch .eq 0 0 8) ∧
    Fetched.decode (.word bneWord) = some (.branch .ne 0 0 8) ∧
    Fetched.decode (.word bltWord) = some (.branch .lt 0 0 8) ∧
    Fetched.decode (.word bgeWord) = some (.branch .ge 0 0 8) ∧
    Fetched.decode (.word bltuWord) = some (.branch .ltu 0 0 8) ∧
    Fetched.decode (.word bgeuWord) = some (.branch .geu 0 0 8) := by
  decide

theorem picorv32_beq_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word beqWord) 0 =
      (branchNext state .eq 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory beqWord .eq 0 0 8
    branch_decodes.1

theorem picorv32_bne_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bneWord) 0 =
      (branchNext state .ne 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bneWord .ne 0 0 8
    branch_decodes.2.1

theorem picorv32_blt_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bltWord) 0 =
      (branchNext state .lt 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bltWord .lt 0 0 8
    branch_decodes.2.2.1

theorem picorv32_bge_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bgeWord) 0 =
      (branchNext state .ge 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bgeWord .ge 0 0 8
    branch_decodes.2.2.2.1

theorem picorv32_bltu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bltuWord) 0 =
      (branchNext state .ltu 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bltuWord .ltu 0 0 8
    branch_decodes.2.2.2.2.1

theorem picorv32_bgeu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bgeuWord) 0 =
      (branchNext state .geu 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bgeuWord .geu 0 0 8
    branch_decodes.2.2.2.2.2

theorem picorv32_beq_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word beqWord, memory := memory, irq := 0 } =
      (branchNext state .eq 0 0 8,
        branchRetirement state
          { fetched := .word beqWord, memory := memory, irq := 0 } .eq 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory beqWord .eq 0 0 8
    branch_decodes.1

theorem picorv32_bne_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bneWord, memory := memory, irq := 0 } =
      (branchNext state .ne 0 0 8,
        branchRetirement state
          { fetched := .word bneWord, memory := memory, irq := 0 } .ne 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bneWord .ne 0 0 8
    branch_decodes.2.1

theorem picorv32_blt_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bltWord, memory := memory, irq := 0 } =
      (branchNext state .lt 0 0 8,
        branchRetirement state
          { fetched := .word bltWord, memory := memory, irq := 0 } .lt 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bltWord .lt 0 0 8
    branch_decodes.2.2.1

theorem picorv32_bge_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bgeWord, memory := memory, irq := 0 } =
      (branchNext state .ge 0 0 8,
        branchRetirement state
          { fetched := .word bgeWord, memory := memory, irq := 0 } .ge 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bgeWord .ge 0 0 8
    branch_decodes.2.2.2.1

theorem picorv32_bltu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bltuWord, memory := memory, irq := 0 } =
      (branchNext state .ltu 0 0 8,
        branchRetirement state
          { fetched := .word bltuWord, memory := memory, irq := 0 } .ltu 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bltuWord .ltu 0 0 8
    branch_decodes.2.2.2.2.1

theorem picorv32_bgeu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bgeuWord, memory := memory, irq := 0 } =
      (branchNext state .geu 0 0 8,
        branchRetirement state
          { fetched := .word bgeuWord, memory := memory, irq := 0 } .geu 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bgeuWord .geu 0 0 8
    branch_decodes.2.2.2.2.2

#print axioms picorv32_beq_class_step
#print axioms picorv32_bne_class_step
#print axioms picorv32_blt_class_step
#print axioms picorv32_bge_class_step
#print axioms picorv32_bltu_class_step
#print axioms picorv32_bgeu_class_step
#print axioms picorv32_beq_class_commit
#print axioms picorv32_bne_class_commit
#print axioms picorv32_blt_class_commit
#print axioms picorv32_bge_class_commit
#print axioms picorv32_bltu_class_commit
#print axioms picorv32_bgeu_class_commit

end Examples.«system-verilog».cores.picorv32.r1_branch
