import LeanModels.Refine.RvfiAddiProgress
import Examples.«system-verilog».cores.picorv32.addi_boundary
import Examples.«system-verilog».cores.picorv32.R2

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
open LeanModels.Sv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.addi_boundary
open Examples.«system-verilog».cores.picorv32

/-! The loaded envelope contributes a concrete configuration fact to this R1
class.  It keeps the ADDI theorem tied to the RISCV_FORMAL design pin while
the canonical-E run is still stopped before its first symbolic cycle. -/

theorem picorv32_loaded_addi_shape :
    picorv32_r2.pdesign.params.length = 26 ∧
    picorv32_r2.pdesign.params.map PParam.name =
      ["ENABLE_COUNTERS", "ENABLE_COUNTERS64", "ENABLE_REGS_16_31",
       "ENABLE_REGS_DUALPORT", "LATCHED_MEM_RDATA", "TWO_STAGE_SHIFT",
       "BARREL_SHIFTER", "TWO_CYCLE_COMPARE", "TWO_CYCLE_ALU",
       "COMPRESSED_ISA", "CATCH_MISALIGN", "CATCH_ILLINSN", "ENABLE_PCPI",
       "ENABLE_MUL", "ENABLE_FAST_MUL", "ENABLE_DIV", "ENABLE_IRQ",
       "ENABLE_IRQ_QREGS", "ENABLE_IRQ_TIMER", "ENABLE_TRACE", "REGS_INIT_ZERO",
       "MASKED_IRQ", "LATCHED_IRQ", "PROGADDR_RESET", "PROGADDR_IRQ", "STACKADDR"] ∧
    picorv32RISCVFormalParameters.COMPRESSED_ISA = 0 ∧
    picorv32RISCVFormalParameters.ENABLE_REGS_16_31 = 1 := by
  exact ⟨by decide,
    Examples.«system-verilog».cores.picorv32.picorv32_riscv_formal_param_names_pinned,
    by decide, by decide⟩

#print axioms picorv32_loaded_addi_shape

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
