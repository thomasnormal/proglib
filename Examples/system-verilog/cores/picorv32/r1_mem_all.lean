import LeanModels.Refine.RvfiMemAll

/-!
# PicoRV32 R1 complete memory class

The RV32I memory family has five loads and three stores across byte, halfword,
and word widths.  These fixed words are checked by the exact decoder, then
threaded through the generic byte-memory step and retirement boundary for
arbitrary architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_mem_all

open LeanModels.Rv
open LeanModels.Refine

def lbWord : Word := 0x10008183
def lhWord : Word := 0x10009183
def lwWord : Word := 0x1000a183
def lbuWord : Word := 0x1000c183
def lhuWord : Word := 0x1000d183
def sbWord : Word := 0x10308023
def shWord : Word := 0x10309023
def swWord : Word := 0x1030a023

theorem lbWord_decode :
    Fetched.decode (.word lbWord) =
      some (.mem (.load true) .byte 3 1 0x100) := by
  decide

theorem lhWord_decode :
    Fetched.decode (.word lhWord) =
      some (.mem (.load true) .half 3 1 0x100) := by
  decide

theorem lwWord_decode :
    Fetched.decode (.word lwWord) =
      some (.mem (.load true) .word 3 1 0x100) := by
  decide

theorem lbuWord_decode :
    Fetched.decode (.word lbuWord) =
      some (.mem (.load false) .byte 3 1 0x100) := by
  decide

theorem lhuWord_decode :
    Fetched.decode (.word lhuWord) =
      some (.mem (.load false) .half 3 1 0x100) := by
  decide

theorem sbWord_decode :
    Fetched.decode (.word sbWord) =
      some (.mem .store .byte 3 1 0x100) := by
  decide

theorem shWord_decode :
    Fetched.decode (.word shWord) =
      some (.mem .store .half 3 1 0x100) := by
  decide

theorem swWord_decode :
    Fetched.decode (.word swWord) =
      some (.mem .store .word 3 1 0x100) := by
  decide

theorem picorv32_lb_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lbWord) 0 =
      (memNext state memory (.load true .byte) 3 1 0x100,
        memAfter memory state (.load true .byte) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lbWord
    (.load true .byte) 3 1 0x100 lbWord_decode

theorem picorv32_lb_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lbWord, memory := memory, irq := 0 } =
      (memNext state memory (.load true .byte) 3 1 0x100,
        memRetirement state
          { fetched := .word lbWord, memory := memory, irq := 0 }
          (.load true .byte) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lbWord
    (.load true .byte) 3 1 0x100 lbWord_decode

theorem picorv32_lh_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lhWord) 0 =
      (memNext state memory (.load true .half) 3 1 0x100,
        memAfter memory state (.load true .half) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lhWord
    (.load true .half) 3 1 0x100 lhWord_decode

theorem picorv32_lh_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lhWord, memory := memory, irq := 0 } =
      (memNext state memory (.load true .half) 3 1 0x100,
        memRetirement state
          { fetched := .word lhWord, memory := memory, irq := 0 }
          (.load true .half) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lhWord
    (.load true .half) 3 1 0x100 lhWord_decode

theorem picorv32_lw_all_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lwWord) 0 =
      (memNext state memory (.load true .word) 3 1 0x100,
        memAfter memory state (.load true .word) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lwWord
    (.load true .word) 3 1 0x100 lwWord_decode

theorem picorv32_lw_all_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lwWord, memory := memory, irq := 0 } =
      (memNext state memory (.load true .word) 3 1 0x100,
        memRetirement state
          { fetched := .word lwWord, memory := memory, irq := 0 }
          (.load true .word) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lwWord
    (.load true .word) 3 1 0x100 lwWord_decode

theorem picorv32_lbu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lbuWord) 0 =
      (memNext state memory (.load false .byte) 3 1 0x100,
        memAfter memory state (.load false .byte) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lbuWord
    (.load false .byte) 3 1 0x100 lbuWord_decode

theorem picorv32_lbu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lbuWord, memory := memory, irq := 0 } =
      (memNext state memory (.load false .byte) 3 1 0x100,
        memRetirement state
          { fetched := .word lbuWord, memory := memory, irq := 0 }
          (.load false .byte) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lbuWord
    (.load false .byte) 3 1 0x100 lbuWord_decode

theorem picorv32_lhu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lhuWord) 0 =
      (memNext state memory (.load false .half) 3 1 0x100,
        memAfter memory state (.load false .half) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lhuWord
    (.load false .half) 3 1 0x100 lhuWord_decode

theorem picorv32_lhu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lhuWord, memory := memory, irq := 0 } =
      (memNext state memory (.load false .half) 3 1 0x100,
        memRetirement state
          { fetched := .word lhuWord, memory := memory, irq := 0 }
          (.load false .half) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lhuWord
    (.load false .half) 3 1 0x100 lhuWord_decode

theorem picorv32_sb_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sbWord) 0 =
      (memNext state memory (.store .byte) 3 1 0x100,
        memAfter memory state (.store .byte) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory sbWord
    (.store .byte) 3 1 0x100 sbWord_decode

theorem picorv32_sb_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sbWord, memory := memory, irq := 0 } =
      (memNext state memory (.store .byte) 3 1 0x100,
        memRetirement state
          { fetched := .word sbWord, memory := memory, irq := 0 }
          (.store .byte) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory sbWord
    (.store .byte) 3 1 0x100 sbWord_decode

theorem picorv32_sh_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word shWord) 0 =
      (memNext state memory (.store .half) 3 1 0x100,
        memAfter memory state (.store .half) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory shWord
    (.store .half) 3 1 0x100 shWord_decode

theorem picorv32_sh_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word shWord, memory := memory, irq := 0 } =
      (memNext state memory (.store .half) 3 1 0x100,
        memRetirement state
          { fetched := .word shWord, memory := memory, irq := 0 }
          (.store .half) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory shWord
    (.store .half) 3 1 0x100 shWord_decode

theorem picorv32_sw_all_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word swWord) 0 =
      (memNext state memory (.store .word) 3 1 0x100,
        memAfter memory state (.store .word) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory swWord
    (.store .word) 3 1 0x100 swWord_decode

theorem picorv32_sw_all_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word swWord, memory := memory, irq := 0 } =
      (memNext state memory (.store .word) 3 1 0x100,
        memRetirement state
          { fetched := .word swWord, memory := memory, irq := 0 }
          (.store .word) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory swWord
    (.store .word) 3 1 0x100 swWord_decode

#print axioms picorv32_lb_class_step
#print axioms picorv32_lb_class_commit
#print axioms picorv32_lh_class_step
#print axioms picorv32_lh_class_commit
#print axioms picorv32_lw_all_class_step
#print axioms picorv32_lw_all_class_commit
#print axioms picorv32_lbu_class_step
#print axioms picorv32_lbu_class_commit
#print axioms picorv32_lhu_class_step
#print axioms picorv32_lhu_class_commit
#print axioms picorv32_sb_class_step
#print axioms picorv32_sb_class_commit
#print axioms picorv32_sh_class_step
#print axioms picorv32_sh_class_commit
#print axioms picorv32_sw_all_class_step
#print axioms picorv32_sw_all_class_commit

end Examples.«system-verilog».cores.picorv32.r1_mem_all
