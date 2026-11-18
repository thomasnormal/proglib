import LeanModels.Refine.RvfiMem
import Examples.«system-verilog».cores.picorv32.rvfi_lw_boundary
import Examples.«system-verilog».cores.picorv32.rvfi_sw_boundary

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

#print axioms picorv32_lw_class_step
#print axioms picorv32_lw_class_commit
#print axioms picorv32_sw_class_step
#print axioms picorv32_sw_class_commit

end Examples.«system-verilog».cores.picorv32.r1_mem
