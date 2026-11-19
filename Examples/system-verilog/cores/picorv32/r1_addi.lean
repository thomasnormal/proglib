import LeanModels.Refine.RvfiAddiProgress
import Examples.«system-verilog».cores.picorv32.addi_boundary
import Examples.«system-verilog».cores.picorv32.R2
import Examples.«system-verilog».cores.picorv32.input_drive_core
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

/-! The same obligation at the actual loaded canonical-E entry point.  The
    result carries the loader certificate together with the mixed-cycle
    refinement, so a later PicoRV32 proof cannot silently substitute a
    different design for the one used by the E-RUN. -/

theorem picorv32_loaded_addi_exact_cycle_step_refines
    (core : PicoRV32LoadedCanonicalE)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hstep : ∀ (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfi_core_adapter.rvfiStep (PicoRV32LoadedCanonicalE.design core) state
              ((rvfi_core_adapter.CoreRvfiMachine.encode
                (PicoRV32LoadedCanonicalE.machine core)) state input) =
              .ok (next, observation) ∧
          (if observation.valid then
            ∃ w rd rs1 imm,
              input.memory = memoryState.memory ∧
              observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
              rel next
                { arch := addiNext memoryState.arch rd rs1 imm,
                  memory := memoryState.memory }
          else rel next memoryState))
    (horder : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input)
      (next : LeanModels.Sv.Kernel.CoreMemState)
      (observation : RvfiObservation),
      rel state memoryState → admit input →
      rvfi_core_adapter.rvfiStep (PicoRV32LoadedCanonicalE.design core) state
          ((rvfi_core_adapter.CoreRvfiMachine.encode
            (PicoRV32LoadedCanonicalE.machine core)) state input) =
        .ok (next, observation) →
      if observation.valid then observation.order = start else True) :
    picorv32_core_mem = .ok (PicoRV32LoadedCanonicalE.design core) ∧
      Rv32iCycleStepRefines
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)) rel admit := by
  refine ⟨PicoRV32LoadedCanonicalE.loaded core, ?_⟩
  exact picorv32_addi_exact_cycle_step_refines
    (PicoRV32LoadedCanonicalE.machine core) hstep horder

#print axioms picorv32_loaded_addi_exact_cycle_step_refines

/-! This is the packaged first R1 invariant at the loaded design boundary.
    Its exact source-step, decoder, architectural post-state, relation, and
    order premises remain explicit. -/

theorem picorv32_loaded_addi_invariant
    (core : PicoRV32LoadedCanonicalE)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hstep : ∀ (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfi_core_adapter.rvfiStep
              (PicoRV32LoadedCanonicalE.design core) state
              ((rvfi_core_adapter.CoreRvfiMachine.encode
                (PicoRV32LoadedCanonicalE.machine core)) state input) =
            .ok (next, observation) ∧
          (if observation.valid then
            ∃ w rd rs1 imm,
              input.memory = memoryState.memory ∧
              observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
              rel next
                { arch := addiNext memoryState.arch rd rs1 imm,
                  memory := memoryState.memory }
          else rel next memoryState))
    (horder : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input)
      (next : LeanModels.Sv.Kernel.CoreMemState)
      (observation : RvfiObservation),
      rel state memoryState → admit input →
      rvfi_core_adapter.rvfiStep
          (PicoRV32LoadedCanonicalE.design core) state
          ((rvfi_core_adapter.CoreRvfiMachine.encode
            (PicoRV32LoadedCanonicalE.machine core)) state input) =
        .ok (next, observation) →
      if observation.valid then observation.order = start else True) :
    picorv32_core_mem = .ok (PicoRV32LoadedCanonicalE.design core) ∧
      Rv32iAddiInvariant
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)) rel admit := by
  refine ⟨PicoRV32LoadedCanonicalE.loaded core, ?_⟩
  exact (PicoRV32LoadedCanonicalE.machine core).to_addi_invariant hstep horder

#print axioms picorv32_loaded_addi_invariant

/-! The first ADDI invariant can now consume the concrete loaded reset
    relation.  The program image is retained in the all-prefix contract, and
    retirement progress remains an independent premise. -/

theorem picorv32_loaded_addi_program_refinement_from_initial_relation
    (core : PicoRV32LoadedCanonicalE)
    (profile : PlatformProfile)
    (program : Memory)
    (initialArch : ArchState)
    (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (invariant : Rv32iAddiInvariant
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)) rel admit)
    (hrel : ∀ (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState),
      PicoRV32ResetRelation
        (PicoRV32LoadedCanonicalE.design core) program
        state memoryState → rel state memoryState)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core))
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)).init schedule target) :
    picorv32_core_mem = .ok (PicoRV32LoadedCanonicalE.design core) ∧
      Rv32iAllPrefixRefinement profile
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)) rel 0
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)).init
        { arch := initialArch, memory := program } schedule target := by
  have hinitial : rel
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)).init
      { arch := initialArch, memory := program } :=
    hrel _ _ (picoRV32_reset_relation_initial
      (PicoRV32LoadedCanonicalE.design core) program initialArch hpc hwf)
  refine ⟨PicoRV32LoadedCanonicalE.loaded core, ?_⟩
  exact rv32i_progress_refinement profile
    (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
      (PicoRV32LoadedCanonicalE.machine core)) rel admit
    invariant.toMixedStep 0 _ _ hinitial hschedule progress

#print axioms picorv32_loaded_addi_program_refinement_from_initial_relation

/-! The typed ADDI prefix consumer retains the instruction-class fact that is
    erased by the generic RV32I prefix package.  Its cycle certificate and
    input fold are both tied to the loaded reset relation and the caller's
    explicit progress witness. -/

theorem picorv32_loaded_addi_typed_program_prefix_from_initial_relation
    (core : PicoRV32LoadedCanonicalE)
    (profile : PlatformProfile)
    (program : Memory)
    (initialArch : ArchState)
    (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (invariant : Rv32iAddiInvariant
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)) rel admit)
    (hrel : ∀ (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState),
      PicoRV32ResetRelation
        (PicoRV32LoadedCanonicalE.design core) program
        state memoryState → rel state memoryState)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core))
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (PicoRV32LoadedCanonicalE.machine core)).init schedule target) :
    ∀ k : Nat, ∃ boundary : Nat, ∃ instructions : List AddiInstruction,
      AddiRvfiCycleTrace
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)) program 0
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
          (PicoRV32LoadedCanonicalE.machine core)).init initialArch
        (schedulePrefix schedule boundary) instructions ∧
      addiProgramInputs program instructions = schedulePrefix target k ∧
      normalizeRvfiTrace? 0
          (rvfiObservations
            (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
              (PicoRV32LoadedCanonicalE.machine core))
            (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
              (PicoRV32LoadedCanonicalE.machine core)).init
            (schedulePrefix schedule boundary)) =
        some (trace (rvMemoryMachineWith profile)
          { arch := initialArch, memory := program }
          (schedulePrefix target k)) ∧
      rel
        (rvfiStateAfter
          (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
            (PicoRV32LoadedCanonicalE.machine core))
          (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
            (PicoRV32LoadedCanonicalE.machine core)).init
          (schedulePrefix schedule boundary))
        (rvMemoryStateAfter profile
          { arch := initialArch, memory := program }
          (schedulePrefix target k)) := by
  let machine := rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
    (PicoRV32LoadedCanonicalE.machine core)
  have hinitial : rel machine.init { arch := initialArch, memory := program } :=
    hrel _ _ (picoRV32_reset_relation_initial
      (PicoRV32LoadedCanonicalE.design core) program initialArch hpc hwf)
  intro k
  obtain ⟨boundary, htarget⟩ := progress k
  have hall : ∀ input ∈ schedulePrefix schedule boundary, admit input := by
    intro input hmem
    exact schedulePrefix_admit schedule admit hschedule boundary input hmem
  obtain ⟨instructions, certificate, hfinal⟩ :=
    addiRvfiCycleTrace_of_step machine rel admit invariant.step invariant.order
      (start := 0) (schedulePrefix schedule boundary) hinitial hall
  have hinputs : addiProgramInputs program instructions =
      schedulePrefix target k := by
    calc
      addiProgramInputs program instructions =
          retireInputs machine.toCycleMachine machine.init
            (schedulePrefix schedule boundary) :=
        (certificate.retireInputs_eq (start := 0)).symm
      _ = schedulePrefix target k := htarget
  have htrace : normalizeRvfiTrace? 0
      (rvfiObservations machine machine.init
        (schedulePrefix schedule boundary)) =
      some (trace (rvMemoryMachineWith profile)
        { arch := initialArch, memory := program }
        (schedulePrefix target k)) := by
    calc
      normalizeRvfiTrace? 0
          (rvfiObservations machine machine.init
            (schedulePrefix schedule boundary)) =
          some (trace (rvMemoryMachineWith profile)
            { arch := initialArch, memory := program }
            (retireInputs machine.toCycleMachine machine.init
              (schedulePrefix schedule boundary))) :=
        certificate.trace_refines profile
      _ = some (trace (rvMemoryMachineWith profile)
          { arch := initialArch, memory := program }
          (schedulePrefix target k)) := by rw [htarget]
  have hstate :
      { arch := addiProgramState initialArch instructions,
        memory := program } =
      rvMemoryStateAfter profile
        { arch := initialArch, memory := program }
        (schedulePrefix target k) := by
    have hmachine := rvMemoryMachineWith_addi_program_state profile
      initialArch program instructions
    simpa [rvMemoryStateAfter, hinputs] using hmachine.symm
  refine ⟨boundary, instructions, certificate, hinputs, htrace, ?_⟩
  exact hstate ▸ hfinal

#print axioms picorv32_loaded_addi_typed_program_prefix_from_initial_relation

/-! The explicit program-image reset relation also supplies the WF premise
    for an ADDI-only architectural prefix. -/

theorem picorv32_loaded_addi_program_state_preserves_WF
    (core : PicoRV32LoadedCanonicalE)
    (program : Memory)
    (initialArch : ArchState)
    (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF)
    (instructions : List AddiInstruction) :
    (addiProgramState initialArch instructions).WF := by
  have hreset := picoRV32_reset_relation_initial
    (PicoRV32LoadedCanonicalE.design core) program initialArch hpc hwf
  exact addiProgramState_preserves_WF initialArch instructions hreset.arch_wf

#print axioms picorv32_loaded_addi_program_state_preserves_WF

/-! The measured first row is consumed only after the reset relation exposes
    the exact architectural state used by that row.  The relation's WF field
    is retained in the result rather than silently discarded. -/

theorem picorv32_addi1_boundary_of_reset_relation
    {design : LeanModels.Sv.Kernel.CoreMemDesign} {program : Memory}
    {state : LeanModels.Sv.Kernel.CoreMemState}
    {memoryState : RvMemoryState}
    (hreset : PicoRV32ResetRelation design program state memoryState)
    (harch : memoryState.arch = ArchState.init 0) :
    memoryState.arch.WF ∧
      RvfiObservation.addiBoundary memoryState.arch
        rvfi_addi_boundary.addiInput rvfi_proof.addi1
        0x00500093 1 0 5 := by
  refine ⟨hreset.arch_wf, ?_⟩
  rw [harch]
  exact rvfi_addi_boundary.pinned_addi_boundary

#print axioms picorv32_addi1_boundary_of_reset_relation

/-! The same measured row is valid for every architectural state whose PC is
    reset and whose x0 slot is well formed.  Nonzero reset registers remain
    unresolved, while this ADDI reads only x0. -/

theorem picorv32_addi1_fields_of_wf_state
    (state : ArchState) (hpc : state.pc = 0) (hwf : state.WF) :
    state.WF ∧
      RvfiObservation.addiFields state
        rvfi_addi_boundary.addiInput rvfi_proof.addi1
        0x00500093 1 0 5 := by
  refine ⟨hwf, ?_⟩
  unfold RvfiObservation.addiFields
  have hx0 : state.regs 0 = 0 := hwf
  simp [rvfi_addi_boundary.addiInput, rvfi_proof.addi1,
    ArchState.readReg, hpc, hx0]
  constructor
  · exact addi_boundary.addi5_decode
  · change rvfi_proof.addi1.wellFormedB = true
    decide

#print axioms picorv32_addi1_fields_of_wf_state

/-! The row fields alone determine the exact architectural ADDI step.  This
    bridge intentionally does not require retirement equality, whose changed-
    register list depends on the prior destination value. -/

theorem picorv32_addi_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (rd rs1 : Reg) (imm : Word)
    (hfields : observation.addiFields state input word rd rs1 imm) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (addiNext state rd rs1 imm, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.alu .add rd (.reg rs1) (.imm imm)) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_addi profile state memory word rd rs1 imm hdecode

#print axioms picorv32_addi_fields_isa_step

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

/-! The loaded first-row consumer can retain the reset relation's architectural
    well-formedness while exposing the same indexed RV32I boundary. -/

theorem picorv32_addi1_loaded_rv32i_boundary_of_reset_relation
    {design : LeanModels.Sv.Kernel.CoreMemDesign} {program : Memory}
    {state : LeanModels.Sv.Kernel.CoreMemState} {memoryState : RvMemoryState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    (hreset : PicoRV32ResetRelation design program state memoryState)
    (harch : memoryState.arch = ArchState.init 0)
    (hstep : design.step state entry = .ok next)
    (hsample : rvfi_core_adapter.rvfiPortSample design next =
      rvfi_addi_boundary.addi1PortSample) :
    memoryState.arch.WF ∧
      ∃ next' observation, rvfi_core_adapter.rvfiStep design state entry =
        .ok (next', observation) ∧
        Rv32iBoundary memoryState.arch
          rvfi_addi_boundary.addiInput observation
          { arch := addiNext memoryState.arch 1 0 5,
            memory := rvfi_addi_boundary.addiInput.memory }
          (addiRetirement memoryState.arch
            rvfi_addi_boundary.addiInput 1 0 5) := by
  refine ⟨hreset.arch_wf, ?_⟩
  obtain ⟨next', observation, hrun, hboundary⟩ :=
    picorv32_addi1_loaded_rv32i_boundary_of_step hstep hsample
  refine ⟨next', observation, hrun, ?_⟩
  simpa [harch] using hboundary

#print axioms picorv32_addi1_loaded_rv32i_boundary_of_reset_relation

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

/-! The pinned ADDI class keeps the architectural x0 invariant required by
    the loaded reset relation.  The other reset register values remain
    arbitrary. -/

theorem picorv32_addi_class_preserves_reset_wf
    (state : ArchState) (hWF : state.WF) :
    (addiNext state 1 0 5).WF := by
  exact addiNext_preserves_WF state 1 0 5 hWF

#print axioms picorv32_addi_class_preserves_reset_wf

end Examples.«system-verilog».cores.picorv32.r1_addi
