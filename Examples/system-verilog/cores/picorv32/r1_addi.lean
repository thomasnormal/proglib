import LeanModels.Refine.RvfiAddiProgress
import Examples.«system-verilog».cores.picorv32.addi_boundary

/-!
# PicoRV32 R1 ADDI class

This is the first instruction-class theorem used by the R2 statement.  The
word is the pinned PicoRV32 `addi x1, x0, 5` encoding, while the architectural
state is arbitrary.  The theorem is the exact RV32I step and retirement
contract that a loaded-core E invariant must discharge for every valid ADDI
row.  It is stated over the existing ISA and RVFI boundary, without a second
decoder or a captured-cycle model.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_addi

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.addi_boundary

theorem picorv32_addi_class_step (state : ArchState) :
    isaStepMemWith cv32e40pProfile state zeroMem
        (.word addi5Word) 0 =
      (addiNext state 1 0 5, zeroMem) := by
  exact addi5_isa_boundary state

theorem picorv32_addi_class_commit (state : ArchState) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word addi5Word, memory := zeroMem, irq := 0 } =
      (addiNext state 1 0 5,
        addiRetirement state
          { fetched := .word addi5Word, memory := zeroMem, irq := 0 }
          1 0 5) := by
  exact addi5_commit_boundary state

#print axioms picorv32_addi_class_step
#print axioms picorv32_addi_class_commit

end Examples.«system-verilog».cores.picorv32.r1_addi
