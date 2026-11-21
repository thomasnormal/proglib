import LeanModels.Sv.Ingest2
import LeanModels.Refine.RvfiE
import LeanModels.Refine.RvfiPorts
import LeanModels.Refine.RvfiProgress
import LeanModels.Refine.RvfiRv32iProgram
import LeanModels.Refine.RvfiAddiProgress
import LeanModels.Refine.RvfiUpperProgress

/-!
# PicoRV32 R2 statement

This is the first core-specific statement for R2.  The backend `E` remains an
explicit parameter: the mixed E implementation will be supplied by the
general lane.  The loaded design below is the unmodified YosysHQ
`RISCV_FORMAL` build, admitted by canonical E at the pinned parameter point.
The file states the universal obligations separately from the finite E-RUN
receipt, so no RTL theorem is claimed until its invariant premises are proved.

The environment is deliberately fixed.  Program memory is always ready,
reset is held for a named number of cycles, interrupts and `pcpi_ready` are
low, and every other input is represented by a one-bit `BitVec`, hence is a
real 0/1 value.  The encoder into `E.Env` is a backend parameter until mixed
E exists.  `admit_inhabited` is the explicit non-vacuity witness for that
encoder; it does not assert that E has completed a run.

The safety conclusion uses the exact RVFI decoder from `RvfiPorts`, ties every
valid fetched word to the byte-addressed program memory, and keeps the
stateful ISA trace from `RvfiE.TraceRefines`.  Progress is a separate
bounded-next-retirement contract below.
-/

namespace Examples.«system-verilog».cores.picorv32

open LeanModels.Rv
open LeanModels.Sv
open LeanModels.Sv.Observe
open LeanModels.Refine
open LeanModels.Refine.RvfiPorts

set_option autoImplicit false

/-! ## R2 consumption map

The loaded-core proof consumes one concrete obligation at each boundary.  The
`PicoRV32Invariant.init` field supplies reset and initial-memory relation data.
Its `PicoRV32Invariant.step` field supplies `RvfiE.StepRefines`, whose valid
row cases consume the exact `Rv32iBoundary` family and whose invalid cases
must carry the relation across a bubble.  `PicoRV32FetchTie` supplies the
program-image word equality used by `PicoRV32R2Statement.safety`.  The
separate `BoundedNextRetirement` premise supplies liveness to
`picoRV32_progress`; it is not inferred from safety.  The R1 files listed
below are the currently available boundary families consumed by that step
obligation:

* `r1_addi.lean`, `r1_alu_imm.lean`, and `r1_alu.lean` for immediate and
  register ALU rows;
* `r1_upper.lean`, `r1_branch.lean`, and `r1_jump.lean` for upper-immediate,
  conditional-branch, and jump rows;
* `r1_mem.lean` and `r1_mem_all.lean` for every load/store width and sign;
* trap, CSR, fence, and RV32M classes are deliberately absent.  PicoRV32's
  RVFI decoder rejects trap and halt rows, the core has no M-mode CSR/MRET/WFI
  behavior, and the pinned parameters disable RV32M.  These ISA-only files
  were removed because they cannot be consumed by a theorem about this core;
* `LeanModels.Refine.RvfiAddiProgress` for the packaged ADDI-only invariant
  bridge `Rv32iAddiInvariant.toMixedStep` and its reset-stream refinement;
* `r1_addi.lean` for the loaded-envelope ADDI configuration, resolved
  parameter vector, declaration prefix, field-presence, and exact RVFI-width
  facts that feed that decoder;
* `picorv32_loaded_cpuregs_one_rank_unpacked`,
  `picorv32_loaded_cpuregs_cell_shape`, and `picorv32_loaded_regfile_size` for
  the concrete register-file geometry consumed by the canonical one-rank
  memory relation;
* `picorv32_loaded_inactive_generate_params` for the four default-disabled
  generate branches reported by the census;
* `rvfi_ports.lean` for the exact-width RVFI decoder and `rvfi_proof.lean`
  for the measured observation witness;
* `rvfi_addi_boundary.lean` for the measured raw ADDI row and its
  `addiBoundary`-to-ISA step and memory-machine commit bridges.
* `rvfi_core_adapter.lean` for the refusal-preserving canonical RVFI adapter,
  the `CoreAddiBoundary` state relation, and its exact canonical-step
  constructors for the measured first and second ADDI rows.  Its
  `r1_addi.picorv32_addi1_loaded_rv32i_boundary_of_step` and
  `picorv32_addi2_loaded_rv32i_boundary_of_step` wrappers carry the measured
  first two rows into the same indexed dispatcher used by the universal
  invariant, while retaining the source-step and exact-port-sample premises.
  `r1_addi.picorv32_addi1_loaded_rv32i_boundary_of_reset_relation` additionally
  carries the reset relation's architectural well-formedness into that first
  loaded-row boundary.
  `r1_mem.picorv32_lw_loaded_rv32i_boundary_of_step` and
  `picorv32_sw_loaded_rv32i_boundary_of_step` provide the corresponding
  memory-row consumers with explicit load and store post-memory states.
  `r1_upper.picorv32_lui_loaded_rv32i_boundary_of_step` and
  `picorv32_auipc_loaded_rv32i_boundary_of_step` provide the corresponding
  LUI and AUIPC consumers through the decoded upper-immediate witness.
  `r1_jump.picorv32_jal_loaded_rv32i_boundary_of_step` and
  `picorv32_jalr_loaded_rv32i_boundary_of_step` provide the corresponding
  JAL and JALR consumers through the decoded jump witness.
  `r1_branch` provides the six conditional-branch consumers through one
  condition-indexed decoded witness.  Its
  `r1_branch.picorv32_branch_exact_cycle_step_refines` theorem consumes the
  common exact branch boundary directly in the mixed cycle dispatcher,
  retaining the source instruction and architectural continuation.
  `r1_branch.picorv32_loaded_branch_program_refinement_of_total` packages one
  condition-indexed branch instruction into the loaded all-prefix contract
  from total canonical execution.
  `r1_alu` provides the ten register-register ALU consumers, and its generic
  operation-indexed witness also covers the immediate ALU forms from
  `r1_alu_imm`.  Its
  `r1_alu.picorv32_alu_exact_cycle_step_refines` theorem consumes the generic
  exact ALU boundary in the mixed cycle dispatcher while retaining the
  operation and source operands.
  `r1_alu_imm` provides the nine remaining immediate ALU raw boundaries that
  instantiate that generic consumer.
  `r1_alu.picorv32_loaded_alu_program_refinement_of_total` packages one
  operation-indexed ALU instruction into the loaded reset-specialized
  all-prefix contract from total canonical execution.
  `r1_mem_all` provides the five load and three store consumers through the
  memory-threaded MemInstruction witness.  Its
  `r1_mem_all.picorv32_mem_exact_cycle_step_refines` theorem consumes the
  generic exact memory boundary in the mixed cycle dispatcher while retaining
  width, signedness, and the post-memory state.
  `rv32iProgramState_preserves_WF` and
  `picorv32_reset_relation_program_state_preserves_WF` preserve the
  architectural x0 invariant from the explicit reset relation through every
  mixed program prefix.
  `rvfi_core_adapter.CoreRv32iBoundary` is the family-tagged composition
  boundary for that premise.  Its
  `CoreRv32iBoundary.to_rv32i_boundary` projection converts each retained
  ALU, branch, jump, memory, fence, system, CSR, or trap witness to the
  corresponding mixed boundary while preserving the exact canonical step.
  `CoreRvfiMachine.to_rv32i_step_refines_of_family_boundary` is the invariant
  adapter that consumes this projection while retaining the order and
  relation-continuation obligations.
  `CoreRvfiMachine.ofTotal` packages a proved total canonical step and RVFI
  decode witness into the machine consumed by these R1 bridges, while
  `CoreRvfiMachine.ofTotal_exact` preserves the witness equality.
  `rvfiObservation_memAddr_of_valid` theorem ties a valid decoded row's
  memory address back to the exact known-width port sample without a
  four-state default.
  Its `rvfiObservation_memAddr_of_valid_view` specialization exposes the
  same fact directly from the canonical `CoreMemState.view`.
  Its
  `CoreRvfiMachine.to_addi_invariant` theorem is the bridge from an explicit
  all-admitted-step premise and order premise to `Rv32iAddiInvariant`, and
  `CoreRvfiMachine.to_reset_addi_refinement` composes that invariant with the
  all-prefix reset contract once initial relation and progress are supplied.
  `r1_addi.picorv32_loaded_addi_typed_program_prefix_from_initial_relation`
  retains an `AddiInstruction` list, its exact input fold, and the final
  relation for each target prefix.
  `r1_addi.picorv32_loaded_addi_program_state_preserves_WF` carries the
  reset relation's x0 invariant through an ADDI-only architectural prefix.
  `r1_addi.picorv32_addi1_boundary_of_reset_relation` consumes an explicit
  reset relation while keeping the measured first-row state equality visible.
  `r1_addi.picorv32_addi1_fields_of_wf_state` proves the same row's wire
  fields for every reset-PC state with a well-formed x0, leaving nonzero reset
  registers unresolved.
  `r1_addi.picorv32_addi_fields_isa_step` bridges any such exact ADDI row
  fields to the ISA memory step without requiring a changed-write list.
  `r1_branch.picorv32_branch_fields_isa_step` provides the corresponding
  exact architectural step bridge for every conditional-branch row.
  `r1_jump.picorv32_jal_fields_isa_step` and
  `r1_jump.picorv32_jalr_fields_isa_step` provide the corresponding exact
  JAL and JALR step bridges while retaining their distinct decoder shapes.
  `r1_jump.picorv32_jump_exact_cycle_step_refines` consumes the common exact
  jump boundary in the mixed cycle dispatcher while preserving the distinct
  JAL and JALR target semantics carried by `JumpInstruction`.
  `r1_jump.picorv32_loaded_jump_program_refinement_of_total` packages one
  retained JAL or JALR instruction into the loaded all-prefix contract from
  total canonical execution.
  `r1_upper.picorv32_lui_fields_isa_step` and
  `r1_upper.picorv32_auipc_fields_isa_step` provide the corresponding exact
  LUI and AUIPC step bridges while retaining their distinct source operands.
  `r1_upper.picorv32_upper_exact_cycle_step_refines` consumes the shared
  upper-immediate boundary in the mixed cycle dispatcher and embeds its
  retained LUI/AUIPC witness into the exact RV32I instruction union.
  `r1_upper.picorv32_loaded_upper_program_refinement_of_total` packages one
  retained LUI or AUIPC instruction into the loaded all-prefix contract from
  total canonical execution.
  `r1_mem.picorv32_sw_fields_isa_step` and
  `r1_mem.picorv32_lw_fields_isa_step` provide the corresponding exact word
  store and load step bridges with their memory effects explicit.
  `r1_mem_all.picorv32_mem_fields_isa_step` provides the shared exact bridge
  for byte, halfword, and word loads and stores, retaining signedness.
  `r1_mem_all.picorv32_loaded_mem_program_refinement_of_total` packages one
  retained load/store instruction into the loaded all-prefix contract from
  total canonical execution.
  `r1_alu.picorv32_alu_fields_isa_step` provides the shared exact bridge for
  register, immediate, and pc-based ALU source forms.
  `r1_addi.picorv32_addi_class_preserves_reset_wf` carries the reset
  `ArchState.WF` fact through the pinned `addi x1, x0, 5` transition.
  `CoreAddiBoundary.to_rv32i_boundary` lifts each exact ADDI witness into the
  indexed RV32I dispatcher while retaining its architectural post-state and
  retirement.  The machine's encoder is state-dependent because the concrete
  E-RUN memory response is selected from the core's sampled address.
  A conversion from
  four-state `mem_addr` to an architectural word remains an explicit loaded-
  core premise, not an inferred default.
  The pinned design leaves nonzero `cpuregs` unresolved at reset because
  `REGS_INIT_ZERO = 0`.  The R2 statement therefore does not introduce a
  second ISA-side read-before-write language.  `decodePost` and `rvfiStep`
  admit only known-width RVFI samples, so the loaded invariant must prove the
  corresponding sample is known or preserve the exact decoder refusal.

These are boundary consumers for a future loaded-core invariant.  They do not
assert that the current PicoRV32 envelope executes in canonical E. -/

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

/-! The census's four remaining rows are inactive default generate branches.
Their controlling parameters are all zero in the pinned RISCV_FORMAL point. -/

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

/-! The first loaded-core consumer is the packaged ADDI bridge.  Keeping this
typed wrapper beside the core statement makes the obligation visible to the
eventual E-specific invariant without introducing a second ADDI theorem. -/
theorem picorv32_addi_step_bridge
    {State : Type} {machine : RvfiCycleMachine State}
    {rel : State → RvMemoryState → Prop} {admit : Input → Prop}
    (invariant : Rv32iAddiInvariant machine rel admit) :
    Rv32iLegacyCycleStepRefines machine rel admit := by
  exact invariant.toMixedStep

#print axioms picorv32_addi_step_bridge

theorem picorv32_upper_step_bridge
    {State : Type} {machine : RvfiCycleMachine State}
    {rel : State → RvMemoryState → Prop} {admit : Input → Prop}
    (invariant : Rv32iUpperInvariant machine rel admit) :
    Rv32iLegacyCycleStepRefines machine rel admit := by
  exact invariant.toMixedStep

#print axioms picorv32_upper_step_bridge

/-- The literal parametric envelope and its explicit pinned instantiation.
`Design2` may contain the loader's loud refusal while the corresponding E
backend is being completed; retaining that value is provenance, not a claim
that the core already runs. -/
def picorv32RISCVFormalPDesign : PDesign := picorv32_r2.pdesign

def picorv32RISCVFormalDesign : Design2 :=
  picorv32RISCVFormalPDesign.instantiateD2 picorv32RISCVFormalParameters.toArgs

/-! ## Fixed environment -/

/-- The fixed R2 environment.  `otherInputs` has a one-bit type, so the
environment cannot contain an x/z value at those ports.  The `programRegion`
predicate and its `programReadOnly` field are the memory-model hypothesis. -/
structure PicoRV32Environment where
  program : Memory
  programRegion : Word → Bool
  resetCycles : Nat
  reset : Nat → Bool
  memoryReady : Word → Bool
  interrupts : Word
  pcpiReady : Bool
  otherInputs : String → BitVec 1
  programReadOnly : ∀ address width value,
    programRegion address = true → storeVal program width address value = program
  resetHeld : ∀ cycle, cycle < resetCycles → reset cycle = true
  resetReleased : reset resetCycles = false
  alwaysReady : ∀ address, memoryReady address = true
  noInterrupts : interrupts = 0
  noPcpiReady : pcpiReady = false

/-- A concrete fixed timing used by examples: reset is high for two cycles and
low thereafter. -/
def fixedEnvironment (program : Memory) (programRegion : Word → Bool)
    (hreadonly : ∀ address width value,
      programRegion address = true → storeVal program width address value = program) :
    PicoRV32Environment :=
  { program := program
    programRegion := programRegion
    resetCycles := 2
    reset := fun cycle => if cycle < 2 then true else false
    memoryReady := fun _ => true
    interrupts := 0
    pcpiReady := false
    otherInputs := fun _ => 0
    programReadOnly := hreadonly
    resetHeld := by intro cycle h; simp [h]
    resetReleased := by simp
    alwaysReady := by intro; rfl
    noInterrupts := rfl
    noPcpiReady := rfl }

/-! ## Backend parameter and safety claim -/

/-- The E-specific part of the loaded-core setup.  `design` and `realize`
remain named parameters until mixed E exists; `loaded` is nevertheless fixed
to the explicit RISCV_FORMAL envelope above. -/
structure PicoRV32Backend (E : ESig) where
  design : E.Elab
  loaded : Design2
  loadedIsPinned : loaded = picorv32RISCVFormalDesign
  /-- The E elaboration selected for a loaded `Design2` design.  Keeping this
  map explicit prevents the backend's `design` field from floating free of
  the source envelope. -/
  toE : Design2 → E.Elab
  designIsLoaded : design = toE loaded
  environment : PicoRV32Environment
  realize : PicoRV32Environment → E.Env
  clocking : Clocking

def PicoRV32Backend.admit {E : ESig} (b : PicoRV32Backend E) (env : E.Env) : Prop :=
  env = b.realize b.environment

/-- The fixed environment admission is inhabited by the backend's explicit
encoder. -/
theorem PicoRV32Backend.admit_inhabited {E : ESig} (b : PicoRV32Backend E) :
    ∃ env, b.admit env := by
  exact ⟨b.realize b.environment, rfl⟩

#print axioms PicoRV32Backend.admit_inhabited

theorem PicoRV32Backend.design_is_pinned {E : ESig}
    (b : PicoRV32Backend E) :
    b.design = b.toE picorv32RISCVFormalDesign := by
  rw [b.designIsLoaded, b.loadedIsPinned]

#print axioms PicoRV32Backend.design_is_pinned

/-- Reset starts the ISA at the pinned `PROGADDR_RESET = 0` and keeps the
loaded program as the initial byte memory. -/
def picoRV32Initial {E : ESig} (b : PicoRV32Backend E)
    (initialArch : ArchState) : RvMemoryState :=
  { arch := initialArch, memory := b.environment.program }

/-- A valid RVFI row fetches the word held by program memory at its reported
PC.  Invalid rows carry no instruction meaning. -/
def fetchProgramTie (program : Memory) (row : RvfiObservation) : Prop :=
  row.valid = false ∨ row.insn = loadVal program .word false row.pcRdata

/-! The generic `TraceRefines` relation deliberately leaves its witnessed
instruction list existential.  The core statement keeps that list, while
also recording the independently checked fetch-to-memory fact for every
decoded row. -/

def PicoRV32TraceRefines (profile : PlatformProfile) (initial : RvMemoryState)
    (program : Memory) (initialPc : Word) (programReadOnly : Prop)
    (environmentInhabited : Prop) (designPinned : Prop)
    (decode : CycleObs PortSample → Option RvfiObservation)
    (samples : List (CycleObs PortSample)) : Prop :=
  initial.memory = program ∧ initial.arch.pc = initialPc ∧ programReadOnly ∧
    environmentInhabited ∧ designPinned ∧
    ∃ rows instructions,
      RvfiE.decodeSamples decode samples = some rows ∧
        (∀ row, row ∈ rows → fetchProgramTie program row) ∧
        normalizeRvfiTrace? 0 rows =
          some (trace (rvMemoryMachineWith profile) initial
            (rv32iProgramInputs initial instructions))

/-- The fetch tie is required on every decoded E cycle. -/
def PicoRV32FetchTie {E : ESig} (b : PicoRV32Backend E) : Prop :=
  ∀ ch env trace,
    b.admit env → E.Disciplined b.clocking env → E.Behaves b.design env ch trace →
    ∀ cycle, cycle < E.cycles env →
      ∀ row,
        decodePost "rvfi_" (RvfiE.sample E b.design env trace cycle) = some row →
          fetchProgramTie b.environment.program row

private theorem decodeSamples_cons
    {decode : CycleObs PortSample → Option RvfiObservation}
    {sample : CycleObs PortSample} {samples : List (CycleObs PortSample)}
    {rows : List RvfiObservation}
    (h : RvfiE.decodeSamples decode (sample :: samples) = some rows) :
    ∃ row tail,
      decode sample = some row ∧
      RvfiE.decodeSamples decode samples = some tail ∧
      rows = row :: tail := by
  unfold RvfiE.decodeSamples at h
  cases hd : decode sample with
  | none => simp [hd] at h
  | some row =>
      cases ht : RvfiE.decodeSamples decode samples with
      | none => simp [hd, ht] at h
      | some tail =>
          rw [hd, ht] at h
          simp at h
          refine ⟨row, tail, ?_, ?_, ?_⟩
          · rfl
          · rfl
          · exact h.symm

private theorem rows_fetch_program_tie
    {E : ESig} {b : PicoRV32Backend E}
    {env : E.Env} {trace : Nat → E.Config}
    (hfetch : ∀ cycle, cycle < E.cycles env →
      ∀ row, decodePost "rvfi_" (RvfiE.sample E b.design env trace cycle) = some row →
        fetchProgramTie b.environment.program row) :
    ∀ offset count rows,
      offset + count ≤ E.cycles env →
      RvfiE.decodeSamples (decodePost "rvfi_")
          ((List.range' offset count).map (RvfiE.sample E b.design env trace)) = some rows →
      ∀ row, row ∈ rows → fetchProgramTie b.environment.program row := by
  intro offset count
  induction count generalizing offset with
  | zero =>
      intro rows hbound hdecode row hmem
      simp [RvfiE.decodeSamples] at hdecode
      subst rows
      simp at hmem
  | succ count ih =>
      intro rows hbound hdecode row hmem
      have hparts := decodeSamples_cons (decode := decodePost "rvfi_")
        (sample := RvfiE.sample E b.design env trace offset)
        (samples := (List.range' (offset + 1) count).map
          (RvfiE.sample E b.design env trace)) hdecode
      obtain ⟨head, tail, hhead, htail, rfl⟩ := hparts
      have hoff : offset < E.cycles env := by omega
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hrow =>
          subst row
          exact hfetch offset hoff head hhead
      | inr htailmem =>
          exact ih (offset := offset + 1) tail (by omega) htail row htailmem

/-! ## Indexed safety invariant and the R2 statement -/

structure PicoRV32Invariant {E : ESig} (b : PicoRV32Backend E)
    (profile : PlatformProfile) (initial : RvMemoryState)
    (rel : Nat → E.Config → RvMemoryState → Prop) where
  init : ∀ ch env trace, b.admit env → E.Disciplined b.clocking env →
    E.Behaves b.design env ch trace →
    rel 0 (RvfiE.boundary E env trace 0) initial
  step : ∀ ch env trace, b.admit env → E.Disciplined b.clocking env →
    E.Behaves b.design env ch trace →
    RvfiE.StepRefines E b.design (decodePost "rvfi_") rel env trace

theorem PicoRV32Invariant.safe {E : ESig} {b : PicoRV32Backend E}
    {profile : PlatformProfile} {initial : RvMemoryState}
    {rel : Nat → E.Config → RvMemoryState → Prop}
    (h : PicoRV32Invariant b profile initial rel) :
    (Obs_E E).SafeOn b.clocking b.design b.admit
      (fun _ samples => RvfiE.TraceRefines profile initial
        (decodePost "rvfi_") samples) := by
  exact RvfiE.safe_of_invariant E b.design b.clocking b.admit profile initial
    (decodePost "rvfi_") rel h.init h.step

#print axioms PicoRV32Invariant.safe

/-- The core-specific R2 claim.  Its safety conclusion is the stateful ISA
trace for the loaded program's initial memory; `fetchTie` supplies the missing
word-to-memory link that the generic `TraceRefines` theorem intentionally
leaves to each core. -/
structure PicoRV32R2Statement (E : ESig) (b : PicoRV32Backend E)
    (profile : PlatformProfile) (initial : RvMemoryState)
    (rel : Nat → E.Config → RvMemoryState → Prop) where
  initialMemory : initial.memory = b.environment.program
  resetPc : initial.arch.pc = 0
  initialWellFormed : initial.arch.WF
  /-- `REGS_INIT_ZERO = 0` leaves nonzero `cpuregs` unresolved.  Their
      resolution or a refusal for reads before initialization belongs in the
      supplied invariant, rather than in this deterministic statement. -/
  environmentInhabited : ∃ env, b.admit env
  invariant : PicoRV32Invariant b profile initial rel
  fetchTie : PicoRV32FetchTie b

theorem PicoRV32R2Statement.safety {E : ESig} {b : PicoRV32Backend E}
    {profile : PlatformProfile} {initial : RvMemoryState}
    {rel : Nat → E.Config → RvMemoryState → Prop}
    (s : PicoRV32R2Statement E b profile initial rel) :
    (Obs_E E).SafeOn b.clocking b.design b.admit
      (fun _ samples => PicoRV32TraceRefines profile initial
        b.environment.program 0
        (∀ address width value,
          b.environment.programRegion address = true →
            storeVal b.environment.program width address value = b.environment.program)
        (∃ env, b.admit env)
        (b.design = b.toE picorv32RISCVFormalDesign)
        (decodePost "rvfi_") samples) := by
  intro ch env samples hadmit hdisc hbeh
  have hgeneric := s.invariant.safe ch env samples hadmit hdisc hbeh
  obtain ⟨rows, instructions, hdecode, htrace⟩ := hgeneric
  obtain ⟨probes, ⟨trace, hrun, hprobes⟩, hsamples⟩ := hbeh
  refine ⟨s.initialMemory, s.resetPc, b.environment.programReadOnly,
    s.environmentInhabited, b.design_is_pinned,
    rows, instructions, hdecode, ?_, htrace⟩
  subst probes
  subst samples
  intro row hrow
  have hdecode' :
      RvfiE.decodeSamples (decodePost "rvfi_")
          ((List.range' 0 (E.cycles env)).map
            (RvfiE.sample E b.design env trace)) = some rows := by
    change RvfiE.decodeSamples (decodePost "rvfi_")
      (((List.range (E.cycles env)).map fun cycle =>
        CycleObs.mk (E.preponed trace (E.edgeSlot env cycle))
          (trace (E.edgeSlot env cycle))).map
        (CycleObs.map ((Obs_E E).sample b.design))) = some rows at hdecode
    dsimp only [Obs_E] at hdecode
    rw [List.map_map, List.range_eq_range'] at hdecode
    change RvfiE.decodeSamples (decodePost "rvfi_")
      ((List.range' 0 (E.cycles env)).map
        (RvfiE.sample E b.design env trace)) = some rows at hdecode
    exact hdecode
  exact rows_fetch_program_tie
    (b := b) (env := env) (trace := trace)
    (s.fetchTie ch env trace hadmit hdisc hrun)
    0 (E.cycles env) rows (by omega) hdecode' row hrow

#print axioms PicoRV32R2Statement.safety

/-! ## Separate bounded progress theorem -/

/-- The explicit liveness premise: one retirement occurs within `bound`
cycles of reset release, and another target retirement occurs within `bound`
cycles after every target prefix already reached. -/
structure BoundedNextRetirement {State : Type}
    (machine : RvfiCycleMachine State) (initial : State)
    (schedule target : Nat → Input) (resetRelease bound : Nat) : Prop where
  first : ∃ n, n ≤ resetRelease + bound ∧
    retireInputs machine.toCycleMachine initial (schedulePrefix schedule n) =
      schedulePrefix target 1
  next : ∀ k n,
    retireInputs machine.toCycleMachine initial (schedulePrefix schedule n) =
      schedulePrefix target (k + 1) →
    ∃ n', n' ≤ n + 1 + bound ∧
      retireInputs machine.toCycleMachine initial (schedulePrefix schedule n') =
        schedulePrefix target (k + 2)

theorem BoundedNextRetirement.toRetiresTarget {State : Type}
    {machine : RvfiCycleMachine State} {initial : State}
    {schedule target : Nat → Input} {resetRelease bound : Nat}
    (h : BoundedNextRetirement machine initial schedule target resetRelease bound) :
    Rv32iRetiresTarget machine initial schedule target := by
  intro k
  cases k with
  | zero => exact ⟨0, rfl⟩
  | succ k =>
      induction k with
      | zero =>
          obtain ⟨n, _, hn⟩ := h.first
          exact ⟨n, hn⟩
      | succ k ih =>
          obtain ⟨n, hn⟩ := ih
          obtain ⟨n', _, hn'⟩ := h.next k n hn
          exact ⟨n', by simpa [Nat.add_assoc] using hn'⟩

#print axioms BoundedNextRetirement.toRetiresTarget

end Examples.«system-verilog».cores.picorv32
