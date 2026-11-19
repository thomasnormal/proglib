import Examples.«system-verilog».cores.picorv32.R2
import Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary
import LeanModels.Sv.Kernel.CoreMemFast

/-!
# PicoRV32 canonical-E RVFI state adapter

This adapter restricts a canonical `CoreMemState` view to the declared RVFI
ports before applying the exact `RvfiPorts.decode` function.  It has no
defaults and does not reinterpret internal signals.  A future loaded-core
invariant can use this function at the post-edge cut point while retaining
the canonical fast-cycle refinement theorem.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

open LeanModels.Sv
open LeanModels.Sv.Kernel
open LeanModels.Sv.Observe
open LeanModels.Refine
open LeanModels.Refine.RvfiPorts

def rvfiPortNames : List String :=
  ["rvfi_valid", "rvfi_order", "rvfi_insn", "rvfi_trap", "rvfi_halt",
   "rvfi_intr", "rvfi_mode", "rvfi_ixl", "rvfi_rs1_addr", "rvfi_rs2_addr",
   "rvfi_rs1_rdata", "rvfi_rs2_rdata", "rvfi_rd_addr", "rvfi_rd_wdata",
   "rvfi_pc_rdata", "rvfi_pc_wdata", "rvfi_mem_addr", "rvfi_mem_rmask",
   "rvfi_mem_wmask", "rvfi_mem_rdata", "rvfi_mem_wdata"]

def rvfiPortSample (d : CoreMemDesign) (st : CoreMemState) : PortSample :=
  ⟨rvfiPortNames.filterMap fun name =>
    (SvState.lookup (CoreMemState.view d st) name).map fun value => (name, value)⟩

theorem rvfiPortSample_read (d : CoreMemDesign) (st : CoreMemState)
    (name : String) :
    (rvfiPortSample d st).read name =
      if name ∈ rvfiPortNames then
        SvState.lookup (CoreMemState.view d st) name
      else none := by
  exact lookup_filterMap
    (fun n => SvState.lookup (CoreMemState.view d st) n) name rvfiPortNames

def rvfiObservation (d : CoreMemDesign) (st : CoreMemState) :
    Option RvfiObservation :=
  decode "rvfi_" (rvfiPortSample d st)

theorem rvfiObservation_memAddr_of_valid
    {d : CoreMemDesign} {st : CoreMemState} {row : RvfiObservation}
    {addr : Word}
    (hobs : rvfiObservation d st = some row)
    (hvalid : row.valid = true)
    (haddr : (rvfiPortSample d st).read "rvfi_mem_addr" = some (.ofBitVec addr)) :
    row.memAddr = addr := by
  have hv := decode_valid "rvfi_" (rvfiPortSample d st) row (by
    simpa [rvfiObservation] using hobs)
  have hv' : readBits 1 (rvfiPortSample d st) ("rvfi_" ++ "valid") = some 1 := by
    simpa [hvalid] using hv
  have hm : readBits 32 (rvfiPortSample d st) ("rvfi_" ++ "mem_addr") = some addr :=
    readBits_ofBitVec _ _ _ haddr
  change decode "rvfi_" (rvfiPortSample d st) = some row at hobs
  unfold decode at hobs
  rw [hv'] at hobs
  simp at hobs
  cases hp : readPayload "rvfi_" (rvfiPortSample d st) with
  | none => simp [hp] at hobs
  | some payload =>
      rw [hp] at hobs
      have hpayload := readPayload_memAddr_of_some hp hm
      simp at hobs
      exact (Payload.toObservation?_memAddr payload row hobs).trans hpayload

theorem rvfiObservation_memAddr_of_valid_view
    {d : CoreMemDesign} {st : CoreMemState} {row : RvfiObservation}
    {addr : Word}
    (hobs : rvfiObservation d st = some row)
    (hvalid : row.valid = true)
    (haddr : SvState.lookup (CoreMemState.view d st) "rvfi_mem_addr" =
      some (.ofBitVec addr)) :
    row.memAddr = addr := by
  apply rvfiObservation_memAddr_of_valid hobs hvalid
  rw [rvfiPortSample_read]
  simp only [show "rvfi_mem_addr" ∈ rvfiPortNames by decide, if_true]
  exact haddr

theorem rvfiObservation_eq_decode (d : CoreMemDesign) (st : CoreMemState) :
    rvfiObservation d st = decode "rvfi_" (rvfiPortSample d st) := rfl

/-! A failed canonical cycle or a refused RVFI decode remains a `Res` failure.
    The wrapper is intentionally not a total `RvfiCycleMachine`: an invariant
    must first prove that both execution and observation decoding succeed. -/

def rvfiStep (d : CoreMemDesign) (st : CoreMemState) (entry : SvState) :
    Res (CoreMemState × RvfiObservation) := do
  let next ← d.fastStepCanonical st entry
  let row ← match rvfiObservation d next with
    | some row => .ok row
    | none => .unsupported "RVFI decode refused canonical post-state"
  pure (next, row)

/-! A universal invariant may use a total `RvfiCycleMachine` only after its
    environment encoder proves that every admitted cycle succeeds in the exact
    adapter above.  This wrapper carries that success proof explicitly. -/

structure CoreRvfiMachine (d : CoreMemDesign) where
  /-- The cycle entry may depend on the current core state.  This is required
      for memory responses driven from the core's sampled address. -/
  encode : CoreMemState → LeanModels.Refine.Input → SvState
  step : CoreMemState → LeanModels.Refine.Input →
    CoreMemState × RvfiObservation
  exact : ∀ (state : CoreMemState) (input : LeanModels.Refine.Input),
    rvfiStep d state (encode state input) = .ok (step state input)

def CoreRvfiMachine.toRvfiCycleMachine
    {d : CoreMemDesign} (machine : CoreRvfiMachine d) :
    LeanModels.Refine.RvfiCycleMachine CoreMemState where
  init := d.initial
  step := machine.step

theorem CoreRvfiMachine.step_exact
    {d : CoreMemDesign} (machine : CoreRvfiMachine d)
    (state : CoreMemState) (input : LeanModels.Refine.Input) :
    rvfiStep d state (machine.encode state input) =
      .ok ((machine.toRvfiCycleMachine).step state input) := by
  exact machine.exact state input

theorem CoreRvfiMachine.step_eq_of_exact
    {d : CoreMemDesign} (machine : CoreRvfiMachine d)
    {state next : CoreMemState} {input : LeanModels.Refine.Input}
    {observation : RvfiObservation}
    (h : rvfiStep d state (machine.encode state input) =
      .ok (next, observation)) :
    machine.step state input = (next, observation) := by
  have hexact := machine.exact state input
  exact Res.ok.inj (hexact.symm.trans h)

theorem CoreRvfiMachine.to_addi_invariant
    {d : CoreMemDesign} (machine : CoreRvfiMachine d)
    {rel : CoreMemState → LeanModels.Refine.RvMemoryState → Prop}
    {admit : LeanModels.Refine.Input → Prop}
    (hstep : ∀ (state : CoreMemState)
      (memoryState : LeanModels.Refine.RvMemoryState)
      (input : LeanModels.Refine.Input),
      rel state memoryState → admit input →
      ∃ next : CoreMemState, ∃ observation : RvfiObservation,
        rvfiStep d state (machine.encode state input) = .ok (next, observation) ∧
        (if observation.valid then
          ∃ w rd rs1 imm,
            input.memory = memoryState.memory ∧
            observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
            rel next
              { arch := LeanModels.Refine.addiNext memoryState.arch rd rs1 imm,
                memory := memoryState.memory }
        else rel next memoryState))
    (horder : ∀ (start : Nat) (state : CoreMemState)
      (memoryState : LeanModels.Refine.RvMemoryState)
      (input : LeanModels.Refine.Input)
      (next : CoreMemState) (observation : RvfiObservation),
      rel state memoryState → admit input →
      rvfiStep d state (machine.encode state input) = .ok (next, observation) →
      if observation.valid then observation.order = start else True) :
    LeanModels.Refine.Rv32iAddiInvariant
      machine.toRvfiCycleMachine rel admit := by
  refine ⟨?_, ?_⟩
  · intro state memoryState input hrel hadmit
    rcases hstep state memoryState input hrel hadmit with
      ⟨next, observation, hrun, hcase⟩
    have hmachine := machine.step_eq_of_exact hrun
    simpa [CoreRvfiMachine.toRvfiCycleMachine, hmachine] using hcase
  · intro start state memoryState input hrel hadmit
    have hrun := machine.exact state input
    change (if (machine.step state input).2.valid then
      (machine.step state input).2.order = start else True)
    exact horder start state memoryState input
      (machine.step state input).1 (machine.step state input).2
      hrel hadmit hrun

theorem CoreRvfiMachine.to_reset_addi_refinement
    {d : CoreMemDesign} (profile : LeanModels.Rv.PlatformProfile)
    (machine : CoreRvfiMachine d)
    (rel : CoreMemState → LeanModels.Refine.RvMemoryState → Prop)
    (admit : LeanModels.Refine.Input → Prop)
    (invariant : LeanModels.Refine.Rv32iAddiInvariant
      machine.toRvfiCycleMachine rel admit)
    (hinit : rel machine.toRvfiCycleMachine.init
      (LeanModels.Refine.rvMemoryMachineWith profile).init)
    {schedule target : Nat → LeanModels.Refine.Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : LeanModels.Refine.Rv32iRetiresTarget
      machine.toRvfiCycleMachine machine.toRvfiCycleMachine.init schedule target) :
    LeanModels.Refine.Rv32iResetRefinement profile
      machine.toRvfiCycleMachine rel schedule target := by
  exact LeanModels.Refine.rv32i_reset_addi_refines_of_invariant profile
    machine.toRvfiCycleMachine rel admit invariant hinit hschedule progress

theorem rvfiStep_ok_of_fast_and_decode
    {d : CoreMemDesign} {st next : CoreMemState} {entry : SvState}
    {row : RvfiObservation}
    (hstep : d.fastStepCanonical st entry = .ok next)
    (hdecode : rvfiObservation d next = some row) :
    rvfiStep d st entry = .ok (next, row) := by
  simp [rvfiStep, hstep, hdecode]

theorem rvfiStep_ok_iff_fast_and_decode
    {d : CoreMemDesign} {st next : CoreMemState} {entry : SvState}
    {row : RvfiObservation} :
    rvfiStep d st entry = .ok (next, row) ↔
      d.fastStepCanonical st entry = .ok next ∧
        rvfiObservation d next = some row := by
  constructor
  · intro h
    unfold rvfiStep at h
    cases hs : d.fastStepCanonical st entry with
    | timeout => simp [hs] at h
    | unsupported msg => simp [hs] at h
    | ok a =>
        simp only [hs, Res.ok_bind] at h
        cases hd : rvfiObservation d a with
        | none => simp [hd] at h
        | some b =>
            simp only [hd, pure] at h
            cases h
            exact ⟨rfl, hd⟩
  · rintro ⟨hstep, hdecode⟩
    exact rvfiStep_ok_of_fast_and_decode hstep hdecode

theorem rvfiStep_ok_iff_step_and_decode
    {d : CoreMemDesign} {st next : CoreMemState} {entry : SvState}
    {row : RvfiObservation} :
    rvfiStep d st entry = .ok (next, row) ↔
      d.step st entry = .ok next ∧
        rvfiObservation d next = some row := by
  rw [rvfiStep_ok_iff_fast_and_decode]
  rw [d.fastStepCanonical_eq_step]

/-! This is the input-aware ADDI obligation for a loaded-core invariant.  The
    canonical post-state and decoded observation remain witnesses, so a proof
    cannot establish the architectural boundary by manufacturing a row. -/

def CoreAddiBoundary
    (d : LeanModels.Sv.Kernel.CoreMemDesign)
    (st : LeanModels.Sv.Kernel.CoreMemState) (entry : LeanModels.Sv.SvState)
    (arch : LeanModels.Rv.ArchState) (input : LeanModels.Refine.Input)
    (word : LeanModels.Refine.Word) (rd rs1 : LeanModels.Rv.Reg)
    (imm : LeanModels.Refine.Word) : Prop :=
  ∃ next : CoreMemState, ∃ observation : RvfiObservation,
    rvfiStep d st entry = .ok (next, observation) ∧
      observation.addiBoundary arch input word rd rs1 imm

theorem CoreAddiBoundary.of_step_decode_boundary
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {arch : LeanModels.Rv.ArchState} {input : LeanModels.Refine.Input}
    {word : LeanModels.Refine.Word} {rd rs1 : LeanModels.Rv.Reg}
    {imm : LeanModels.Refine.Word}
    {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation}
    (hstep : d.fastStepCanonical st entry = .ok next)
    (hdecode : rvfiObservation d next = some observation)
    (hboundary : observation.addiBoundary arch input word rd rs1 imm) :
    CoreAddiBoundary d st entry arch input word rd rs1 imm := by
  exact ⟨next, observation,
    rvfiStep_ok_of_fast_and_decode hstep hdecode, hboundary⟩

theorem CoreAddiBoundary.of_canonical_step_decode_boundary
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {arch : LeanModels.Rv.ArchState} {input : LeanModels.Refine.Input}
    {word : LeanModels.Refine.Word} {rd rs1 : LeanModels.Rv.Reg}
    {imm : LeanModels.Refine.Word}
    {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfiObservation d next = some observation)
    (hboundary : observation.addiBoundary arch input word rd rs1 imm) :
    CoreAddiBoundary d st entry arch input word rd rs1 imm := by
  apply CoreAddiBoundary.of_step_decode_boundary (hdecode := hdecode)
    (hboundary := hboundary)
  rw [d.fastStepCanonical_eq_step]
  exact hstep

theorem pinned_addi1_core_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState}
    (hstep : d.step st entry = .ok next)
    (hsample : rvfiPortSample d next =
      Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary.addi1PortSample) :
    CoreAddiBoundary d st entry
      (LeanModels.Rv.ArchState.init 0)
      Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary.addiInput
      0x00500093 1 0 5 := by
  apply CoreAddiBoundary.of_canonical_step_decode_boundary (hstep := hstep)
  · rw [rvfiObservation_eq_decode, hsample]
    exact Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary.pinned_addi1_port_decode
  · exact Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary.pinned_addi_boundary

theorem pinned_addi2_core_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState}
    (hstep : d.step st entry = .ok next)
    (hsample : rvfiPortSample d next =
      Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary.addi2PortSample) :
    CoreAddiBoundary d st entry
      Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary.addi2State
      Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary.addi2Input
      0x00110193 3 2 1 := by
  apply CoreAddiBoundary.of_canonical_step_decode_boundary (hstep := hstep)
  · rw [rvfiObservation_eq_decode, hsample]
    exact Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary.pinned_addi2_port_decode
  · exact Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary.pinned_addi2_boundary

theorem CoreAddiBoundary.isaStepMemWith
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {arch : LeanModels.Rv.ArchState} {input : LeanModels.Refine.Input}
    {word : LeanModels.Refine.Word} {rd rs1 : LeanModels.Rv.Reg}
    {imm : LeanModels.Refine.Word}
    (h : CoreAddiBoundary d st entry arch input word rd rs1 imm) :
    LeanModels.Rv.isaStepMemWith LeanModels.Rv.cv32e40pProfile arch
      input.memory input.fetched input.irq =
      (LeanModels.Refine.addiNext arch rd rs1 imm, input.memory) := by
  rcases h with ⟨next, observation, hrun, hboundary⟩
  exact RvfiObservation.addiBoundary_isaStepMemWith
    LeanModels.Rv.cv32e40pProfile observation arch input word rd rs1 imm hboundary

theorem CoreAddiBoundary.memoryMachineStep
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {arch : LeanModels.Rv.ArchState} {input : LeanModels.Refine.Input}
    {word : LeanModels.Refine.Word} {rd rs1 : LeanModels.Rv.Reg}
    {imm : LeanModels.Refine.Word}
    (h : CoreAddiBoundary d st entry arch input word rd rs1 imm) :
    (LeanModels.Refine.rvMemoryMachineWith LeanModels.Rv.cv32e40pProfile).step
        { arch := arch, memory := input.memory } input =
      ({ arch := LeanModels.Refine.addiNext arch rd rs1 imm, memory := input.memory },
        LeanModels.Refine.addiRetirement arch input rd rs1 imm) := by
  rcases h with ⟨next, observation, hrun, hboundary⟩
  exact RvfiObservation.addiBoundary_rvMemoryMachineWith
    LeanModels.Rv.cv32e40pProfile observation arch input word rd rs1 imm hboundary

/-! The ADDI-specific boundary can also feed the indexed RV32I dispatcher.
    Keeping the post-state and retirement in the conclusion prevents this
    adapter from erasing the architectural result while changing boundary
    representations. -/

theorem CoreAddiBoundary.to_rv32i_boundary
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {arch : LeanModels.Rv.ArchState} {input : LeanModels.Refine.Input}
    {word : LeanModels.Refine.Word} {rd rs1 : LeanModels.Rv.Reg}
    {imm : LeanModels.Refine.Word}
    (h : CoreAddiBoundary d st entry arch input word rd rs1 imm) :
    ∃ next : CoreMemState, ∃ observation : RvfiObservation,
      rvfiStep d st entry = .ok (next, observation) ∧
      Rv32iBoundary arch input observation
        { arch := LeanModels.Refine.addiNext arch rd rs1 imm,
          memory := input.memory }
        (LeanModels.Refine.addiRetirement arch input rd rs1 imm) := by
  rcases h with ⟨next, observation, hrun, hboundary⟩
  refine ⟨next, observation, hrun, ?_⟩
  simpa [LeanModels.Refine.addiNext, LeanModels.Refine.addiRetirement,
    LeanModels.Refine.aluNext, LeanModels.Refine.aluRetirement,
    LeanModels.Refine.addiEffects, LeanModels.Refine.aluEffects,
    LeanModels.Rv.aluSem, LeanModels.Rv.src1Val, LeanModels.Rv.src2Val] using
    RvfiObservation.addiBoundary_rv32i word rd rs1 imm hboundary

#print axioms CoreAddiBoundary.to_rv32i_boundary

theorem CoreAddiBoundary.exists_semantic_post
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {arch : LeanModels.Rv.ArchState} {input : LeanModels.Refine.Input}
    {word : LeanModels.Refine.Word} {rd rs1 : LeanModels.Rv.Reg}
    {imm : LeanModels.Refine.Word}
    (h : CoreAddiBoundary d st entry arch input word rd rs1 imm) :
    ∃ next : CoreMemState, ∃ observation : RvfiObservation,
      rvfiStep d st entry = .ok (next, observation) ∧
      observation.addiBoundary arch input word rd rs1 imm ∧
      LeanModels.Rv.isaStepMemWith LeanModels.Rv.cv32e40pProfile arch
        input.memory input.fetched input.irq =
        (LeanModels.Refine.addiNext arch rd rs1 imm, input.memory) := by
  rcases h with ⟨next, observation, hrun, hboundary⟩
  exact ⟨next, observation, hrun, hboundary,
    RvfiObservation.addiBoundary_isaStepMemWith
      LeanModels.Rv.cv32e40pProfile observation arch input word rd rs1 imm hboundary⟩

theorem CoreAddiBoundary.to_addi_invariant_valid_branch
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {arch : LeanModels.Rv.ArchState} {input : LeanModels.Refine.Input}
    {word : LeanModels.Refine.Word} {rd rs1 : LeanModels.Rv.Reg}
    {imm : LeanModels.Refine.Word}
    {rel : CoreMemState → LeanModels.Refine.RvMemoryState → Prop}
    (h : CoreAddiBoundary d st entry arch input word rd rs1 imm)
    (hpost : ∀ (next : CoreMemState) (observation : RvfiObservation),
      rvfiStep d st entry = .ok (next, observation) →
      rel next
        { arch := LeanModels.Refine.addiNext arch rd rs1 imm,
          memory := input.memory }) :
    ∃ next : CoreMemState, ∃ observation : RvfiObservation,
      rvfiStep d st entry = .ok (next, observation) ∧
      observation.addiBoundary arch input word rd rs1 imm ∧
      rel next
        { arch := LeanModels.Refine.addiNext arch rd rs1 imm,
          memory := input.memory } := by
  rcases h with ⟨next, observation, hrun, hboundary⟩
  exact ⟨next, observation, hrun, hboundary, hpost next observation hrun⟩

#print axioms rvfiPortSample_read
#print axioms rvfiObservation_memAddr_of_valid
#print axioms rvfiObservation_eq_decode
#print axioms rvfiStep_ok_of_fast_and_decode
#print axioms rvfiStep_ok_iff_fast_and_decode
#print axioms rvfiStep_ok_iff_step_and_decode
#print axioms CoreAddiBoundary.isaStepMemWith
#print axioms CoreAddiBoundary.memoryMachineStep

end Examples.«system-verilog».cores.picorv32.rvfi_core_adapter
