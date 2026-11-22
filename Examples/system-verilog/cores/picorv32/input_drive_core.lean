import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemFast

/-! The unmodified RISCV_FORMAL envelope at the twenty-six upstream defaults. -/

namespace Examples.«system-verilog».cores.picorv32

open LeanModels.Sv LeanModels.Sv.Kernel

set_option autoImplicit false

set_option maxRecDepth 100000 in
load_design_sv2 picorv32_r2
  from "Examples/system-verilog/cores/picorv32/picorv32_r2.sv.json"

/-! ## The named RISCV_FORMAL design -/

/-- Every PicoRV32 parameter is named here, even when its pinned value is
zero.  The order is the declaration order in the loaded envelope. -/
structure PicoRV32Parameters where
  ENABLE_COUNTERS : Nat
  ENABLE_COUNTERS64 : Nat
  ENABLE_REGS_16_31 : Nat
  ENABLE_REGS_DUALPORT : Nat
  LATCHED_MEM_RDATA : Nat
  TWO_STAGE_SHIFT : Nat
  BARREL_SHIFTER : Nat
  TWO_CYCLE_COMPARE : Nat
  TWO_CYCLE_ALU : Nat
  COMPRESSED_ISA : Nat
  CATCH_MISALIGN : Nat
  CATCH_ILLINSN : Nat
  ENABLE_PCPI : Nat
  ENABLE_MUL : Nat
  ENABLE_FAST_MUL : Nat
  ENABLE_DIV : Nat
  ENABLE_IRQ : Nat
  ENABLE_IRQ_QREGS : Nat
  ENABLE_IRQ_TIMER : Nat
  ENABLE_TRACE : Nat
  REGS_INIT_ZERO : Nat
  MASKED_IRQ : Nat
  LATCHED_IRQ : Nat
  PROGADDR_RESET : Nat
  PROGADDR_IRQ : Nat
  STACKADDR : Nat
  deriving Repr, DecidableEq

def picorv32RISCVFormalParameters : PicoRV32Parameters :=
  { ENABLE_COUNTERS := 1
    ENABLE_COUNTERS64 := 1
    ENABLE_REGS_16_31 := 1
    ENABLE_REGS_DUALPORT := 1
    LATCHED_MEM_RDATA := 0
    TWO_STAGE_SHIFT := 1
    BARREL_SHIFTER := 0
    TWO_CYCLE_COMPARE := 0
    TWO_CYCLE_ALU := 0
    COMPRESSED_ISA := 0
    CATCH_MISALIGN := 1
    CATCH_ILLINSN := 1
    ENABLE_PCPI := 0
    ENABLE_MUL := 0
    ENABLE_FAST_MUL := 0
    ENABLE_DIV := 0
    ENABLE_IRQ := 0
    ENABLE_IRQ_QREGS := 1
    ENABLE_IRQ_TIMER := 1
    ENABLE_TRACE := 0
    REGS_INIT_ZERO := 0
    MASKED_IRQ := 0
    LATCHED_IRQ := 0xffffffff
    PROGADDR_RESET := 0
    PROGADDR_IRQ := 16
    STACKADDR := 0xffffffff }

def PicoRV32Parameters.toArgs (p : PicoRV32Parameters) : List Int :=
  [p.ENABLE_COUNTERS, p.ENABLE_COUNTERS64, p.ENABLE_REGS_16_31,
   p.ENABLE_REGS_DUALPORT, p.LATCHED_MEM_RDATA, p.TWO_STAGE_SHIFT,
   p.BARREL_SHIFTER, p.TWO_CYCLE_COMPARE, p.TWO_CYCLE_ALU, p.COMPRESSED_ISA,
   p.CATCH_MISALIGN, p.CATCH_ILLINSN, p.ENABLE_PCPI, p.ENABLE_MUL,
   p.ENABLE_FAST_MUL, p.ENABLE_DIV, p.ENABLE_IRQ, p.ENABLE_IRQ_QREGS,
   p.ENABLE_IRQ_TIMER, p.ENABLE_TRACE, p.REGS_INIT_ZERO, p.MASKED_IRQ,
   p.LATCHED_IRQ, p.PROGADDR_RESET, p.PROGADDR_IRQ, p.STACKADDR]

#guard picorv32RISCVFormalParameters.toArgs ==
  [1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
   4294967295, 0, 16, 4294967295]

theorem picorv32_riscv_formal_args_pinned :
    picorv32RISCVFormalParameters.toArgs =
      [1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
       4294967295, 0, 16, 4294967295] := by
  decide

#print axioms picorv32_riscv_formal_args_pinned

theorem picorv32_riscv_formal_param_names_pinned :
    picorv32_r2.pdesign.params.map PParam.name =
      ["ENABLE_COUNTERS", "ENABLE_COUNTERS64", "ENABLE_REGS_16_31",
       "ENABLE_REGS_DUALPORT", "LATCHED_MEM_RDATA", "TWO_STAGE_SHIFT",
       "BARREL_SHIFTER", "TWO_CYCLE_COMPARE", "TWO_CYCLE_ALU",
       "COMPRESSED_ISA", "CATCH_MISALIGN", "CATCH_ILLINSN", "ENABLE_PCPI",
       "ENABLE_MUL", "ENABLE_FAST_MUL", "ENABLE_DIV", "ENABLE_IRQ",
       "ENABLE_IRQ_QREGS", "ENABLE_IRQ_TIMER", "ENABLE_TRACE", "REGS_INIT_ZERO",
       "MASKED_IRQ", "LATCHED_IRQ", "PROGADDR_RESET", "PROGADDR_IRQ", "STACKADDR"] := by
  decide

#print axioms picorv32_riscv_formal_param_names_pinned

/-! The loaded source contains one one-rank unpacked declaration, the
register file at `cpuregs`.  This is the concrete declaration shape consumed
by the canonical one-rank memory relation. -/

theorem picorv32_loaded_cpuregs_one_rank_unpacked :
    picorv32_r2.pdesign.decls.filterMap
      (fun d => if d.name == "cpuregs" then some d.unpackedDims.length else none) =
      [1] := by
  decide

#print axioms picorv32_loaded_cpuregs_one_rank_unpacked

theorem picorv32_loaded_cpuregs_cell_shape :
    picorv32_r2.pdesign.decls.filterMap
      (fun d => if d.name == "cpuregs" then
        some ((match d.type with | .packed _ r => r | _ => none),
          d.unpackedDims.length) else none) =
      [(some 32, 1)] := by
  decide

#print axioms picorv32_loaded_cpuregs_cell_shape

theorem picorv32_loaded_regfile_size :
    picorv32_r2.pdesign.localParams.filterMap
      (fun p => if p.name == "regfile_size" then p.resolved? else none) =
      [32] := by
  decide

#print axioms picorv32_loaded_regfile_size

theorem picorv32_loaded_inactive_generate_params :
    picorv32RISCVFormalParameters.ENABLE_FAST_MUL = 0 ∧
    picorv32RISCVFormalParameters.ENABLE_MUL = 0 ∧
    picorv32RISCVFormalParameters.ENABLE_DIV = 0 ∧
    picorv32RISCVFormalParameters.TWO_CYCLE_ALU = 0 := by
  decide

#print axioms picorv32_loaded_inactive_generate_params

theorem picorv32_rv32m_disabled :
    picorv32RISCVFormalParameters.ENABLE_MUL = 0 ∧
      picorv32RISCVFormalParameters.ENABLE_DIV = 0 := by
  decide

#print axioms picorv32_rv32m_disabled

/- The loaded design is compiled once so the input-driven receipt can execute
the source-shaped E route without re-elaborating the multi-megabyte envelope
for every temporary probe. -/
def picorv32_core_mem : Res CoreMemDesign :=
  picorv32_r2.e 1 1 1 1 0 1 0 0 0 0 1 1 0 0 0 0 0 1 1 0 0 0 4294967295 0 16 4294967295

theorem picorv32_core_mem_unfolds :
    picorv32_core_mem =
      picorv32_r2.e 1 1 1 1 0 1 0 0 0 0 1 1 0 0 0 0 0 1 1 0 0 0 4294967295 0 16 4294967295 := rfl

#print axioms picorv32_core_mem_unfolds

end Examples.«system-verilog».cores.picorv32
