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

The real proof still has two obligations. `PicoRV32Invariant.init` supplies
the reset and initial-memory relation, while `PicoRV32Invariant.step` supplies
the order-indexed `RvfiE.StepRefines` fact. `PicoRV32FetchTie` supplies the
program-image word equality used by the safety theorem, and
`BoundedNextRetirement` is the separate progress premise.

The former `r1_*` files were deleted because they only repackaged those
obligations or proved ISA facts for fixed words. They did not establish a fact
about the loaded PicoRV32 design. The remaining useful infrastructure is
`rvfi_ports.lean` for the exact RVFI decoder, `rvfi_core_adapter.lean` for the
generic family boundary and future invariant bridge, and the RVFI boundary
files for their explicitly typed observation data. None of these files claims
that the current envelope satisfies the missing step invariant.

The first real target is one ADDI class over `CoreMemDesign.step` for the
loaded envelope. It must establish the source instruction, decoded operands,
retirement order, architectural post-state, and relation continuation. The
canonical clocked route currently stops during normalization of the full
PicoRV32 envelope before it can produce the structure equation.
-/

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
