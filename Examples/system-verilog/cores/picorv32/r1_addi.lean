import LeanModels.Refine.RvfiAddiProgress
import Examples.«system-verilog».cores.picorv32.addi_boundary
import Examples.«system-verilog».cores.picorv32.R2
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

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

/-! The envelope's defaults-elaborated parameter metadata is the concrete
configuration consumed by the named RISCV_FORMAL instantiation.  Keeping the
resolved values in declaration order makes the link between the loaded design
and `PicoRV32Parameters.toArgs` explicit. -/

theorem picorv32_loaded_resolved_params :
    picorv32_r2.pdesign.params.map PParam.resolved? =
      [some 1, some 1, some 1, some 1, some 0, some 1, some 0, some 0,
       some 0, some 0, some 1, some 1, some 0, some 0, some 0, some 0,
       some 0, some 1, some 1, some 0, some 0, some 0, some 4294967295,
       some 0, some 16, some 4294967295] := by
  decide

#print axioms picorv32_loaded_resolved_params

theorem picorv32_loaded_resolved_params_eq_formal_args :
    picorv32_r2.pdesign.params.map PParam.resolved? =
      picorv32RISCVFormalParameters.toArgs.map some := by
  rw [picorv32_loaded_resolved_params]
  decide

#print axioms picorv32_loaded_resolved_params_eq_formal_args

theorem picorv32_loaded_rvfi_prefix :
    (picorv32_r2.pdesign.decls.take 31).map PDecl.name =
      ["clk", "resetn", "trap", "mem_valid", "mem_instr", "mem_ready",
       "mem_addr", "mem_wdata", "mem_wstrb", "mem_rdata", "mem_la_read",
       "mem_la_write", "mem_la_addr", "mem_la_wdata", "mem_la_wstrb",
       "pcpi_valid", "pcpi_insn", "pcpi_rs1", "pcpi_rs2", "pcpi_wr",
       "pcpi_rd", "pcpi_wait", "pcpi_ready", "irq", "eoi", "rvfi_valid",
       "rvfi_order", "rvfi_insn", "rvfi_trap", "rvfi_halt", "rvfi_intr"] := by
  decide

#print axioms picorv32_loaded_rvfi_prefix

theorem picorv32_loaded_rvfi_fields_present :
    ∀ name ∈ ["rvfi_valid", "rvfi_order", "rvfi_insn", "rvfi_trap",
      "rvfi_halt", "rvfi_intr", "rvfi_mode", "rvfi_ixl", "rvfi_rs1_addr",
      "rvfi_rs2_addr", "rvfi_rs1_rdata", "rvfi_rs2_rdata", "rvfi_rd_addr",
      "rvfi_rd_wdata", "rvfi_pc_rdata", "rvfi_pc_wdata", "rvfi_mem_addr",
      "rvfi_mem_rmask", "rvfi_mem_wmask", "rvfi_mem_rdata", "rvfi_mem_wdata"],
      name ∈ picorv32_r2.pdesign.decls.map PDecl.name := by
  decide

#print axioms picorv32_loaded_rvfi_fields_present

private def loadedPackedWidth? (decl : PDecl) : Option Nat :=
  match decl.type with
  | .packed _ width => width
  | _ => none

theorem picorv32_loaded_rvfi_widths :
    (picorv32_r2.pdesign.decls.drop 25 |>.take 21).map
        (fun decl => (decl.name, loadedPackedWidth? decl)) =
      [("rvfi_valid", some 1), ("rvfi_order", some 64),
       ("rvfi_insn", some 32), ("rvfi_trap", some 1), ("rvfi_halt", some 1),
       ("rvfi_intr", some 1), ("rvfi_mode", some 2), ("rvfi_ixl", some 2),
       ("rvfi_rs1_addr", some 5), ("rvfi_rs2_addr", some 5),
       ("rvfi_rs1_rdata", some 32), ("rvfi_rs2_rdata", some 32),
       ("rvfi_rd_addr", some 5), ("rvfi_rd_wdata", some 32),
       ("rvfi_pc_rdata", some 32), ("rvfi_pc_wdata", some 32),
       ("rvfi_mem_addr", some 32), ("rvfi_mem_rmask", some 4),
       ("rvfi_mem_wmask", some 4), ("rvfi_mem_rdata", some 32),
       ("rvfi_mem_wdata", some 32)] := by
  decide

#print axioms picorv32_loaded_rvfi_widths

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

/-! The exact-cycle ADDI consumer.  The source-step/decode obligation remains
    explicit, so this theorem can only be used after the loaded E machine has
    supplied a canonical post-state and RVFI observation for every admitted
    input. -/

theorem picorv32_addi_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hstep : ∀ (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfi_core_adapter.rvfiStep d state (machine.encode state input) =
            .ok (next, observation) ∧
          (if observation.valid then
            ∃ w rd rs1 imm,
              input.memory = memoryState.memory ∧
              observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
              rel next
                { arch := addiNext memoryState.arch rd rs1 imm,
                  memory := memoryState.memory }
          else rel next memoryState))
    (horder : ∀ (start : Nat) (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input)
      (next : LeanModels.Sv.Kernel.CoreMemState)
      (observation : RvfiObservation),
      rel state memoryState → admit input →
      rvfi_core_adapter.rvfiStep d state (machine.encode state input) =
        .ok (next, observation) →
      if observation.valid then observation.order = start else True) :
    Rv32iCycleStepRefines machine.toRvfiCycleMachine rel admit := by
  exact (machine.to_addi_invariant hstep horder).toMixedStep

#print axioms picorv32_addi_exact_cycle_step_refines


/-! The measured first ADDI row can be consumed by the same indexed RV32I
    dispatcher as a universal invariant.  The source transition and exact
    port sample remain premises, so this theorem records a loaded-core
    boundary without turning the finite receipt into a universal claim. -/

theorem picorv32_addi1_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState}
    (hstep : d.step st entry = .ok next)
    (hsample : rvfi_core_adapter.rvfiPortSample d next =
      rvfi_addi_boundary.addi1PortSample) :
    ∃ next' observation, rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation) ∧
      Rv32iBoundary (ArchState.init 0)
        rvfi_addi_boundary.addiInput observation
        { arch := addiNext (ArchState.init 0) 1 0 5,
          memory := rvfi_addi_boundary.addiInput.memory }
        (addiRetirement (ArchState.init 0)
          rvfi_addi_boundary.addiInput 1 0 5) := by
  obtain ⟨next', observation, hrun, hboundary⟩ :=
    rvfi_core_adapter.pinned_addi1_core_boundary_of_step hstep hsample
  have hcore : rvfi_core_adapter.CoreAddiBoundary d st entry
      (ArchState.init 0) rvfi_addi_boundary.addiInput
      0x00500093 1 0 5 :=
    ⟨next', observation, hrun, hboundary⟩
  exact hcore.to_rv32i_boundary

#print axioms picorv32_addi1_loaded_rv32i_boundary_of_step

theorem picorv32_addi2_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState}
    (hstep : d.step st entry = .ok next)
    (hsample : rvfi_core_adapter.rvfiPortSample d next =
      rvfi_addi_boundary.addi2PortSample) :
    ∃ next' observation, rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation) ∧
      Rv32iBoundary rvfi_addi_boundary.addi2State
        rvfi_addi_boundary.addi2Input observation
        { arch := addiNext rvfi_addi_boundary.addi2State 3 2 1,
          memory := rvfi_addi_boundary.addi2Input.memory }
        (addiRetirement rvfi_addi_boundary.addi2State
          rvfi_addi_boundary.addi2Input 3 2 1) := by
  obtain ⟨next', observation, hrun, hboundary⟩ :=
    rvfi_core_adapter.pinned_addi2_core_boundary_of_step hstep hsample
  have hcore : rvfi_core_adapter.CoreAddiBoundary d st entry
      rvfi_addi_boundary.addi2State rvfi_addi_boundary.addi2Input
      0x00110193 3 2 1 :=
    ⟨next', observation, hrun, hboundary⟩
  exact hcore.to_rv32i_boundary

#print axioms picorv32_addi2_loaded_rv32i_boundary_of_step

end Examples.«system-verilog».cores.picorv32.r1_addi
