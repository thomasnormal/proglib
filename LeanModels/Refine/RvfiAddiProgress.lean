import LeanModels.Refine.RvfiAddiMixed
import LeanModels.Refine.RvfiProgress

/-!
# From-reset stream refinement for an ADDI-only invariant

The ADDI invariant bridge and the generic progress theorem are useful on
their own, but a first core proof should be able to state the complete
from-reset contract in one place.  This theorem composes those two pieces:
the per-cycle ADDI boundary plus explicit order premise supplies the mixed
step obligation, and the independent progress witness supplies every finite
target prefix.

No target schedule is synthesized here.  As in the generic theorem, the
caller provides the admitted schedule and its progress witness.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The local obligations for an ADDI-only loaded-core invariant.

The step field describes the memory-threaded ADDI boundary and post-state;
the order field supplies the RVFI order tag separately.  Keeping them in one
named proposition lets a core proof carry its invariant without repeating the
dependent cycle-step predicates at every reset theorem call.
-/
structure Rv32iAddiInvariant {State : Type}
    (machine : RvfiCycleMachine State)
    (rel : Nat → State → RvMemoryState → Prop) (admit : Input → Prop) : Prop where
  step : ∀ (start : Nat) (state : State) (memoryState : RvMemoryState) (input : Input),
    rel start state memoryState → admit input →
    let (state', observation) := machine.step state input
    if observation.valid then
      ∃ w rd rs1 imm,
        input.memory = memoryState.memory ∧
        observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
            rel (start + 1) state'
          { arch := addiNext memoryState.arch rd rs1 imm,
            memory := memoryState.memory }
      else rel start state' memoryState
  order : ∀ (start : Nat) (state : State)
    (memoryState : RvMemoryState) (input : Input),
    rel start state memoryState → admit input →
    let (_, observation) := machine.step state input
    if observation.valid then observation.order = start else True

/-- The packaged ADDI invariant discharges the unified mixed per-cycle
obligation. -/
theorem Rv32iAddiInvariant.toMixedStep
    {State : Type} {machine : RvfiCycleMachine State}
    {rel : Nat → State → RvMemoryState → Prop} {admit : Input → Prop}
    (invariant : Rv32iAddiInvariant machine rel admit) :
    Rv32iCycleStepRefines machine rel admit := by
  exact rv32iCycleStepRefines_of_addi_memory machine rel admit
    invariant.step invariant.order

/-! ## Typed finite prefixes

The mixed bridge above intentionally forgets that every retiring row came
from an ADDI.  The constructor below keeps that information for a finite
cycle prefix.  It consumes the same memory-threaded step premise directly,
so a loaded-core theorem can expose an `AddiInstruction` program rather than
an arbitrary `Rv32iInstruction` list.
-/

theorem addiRvfiCycleTrace_of_step
    {State : Type} (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd rs1 imm,
          input.memory = memoryState.memory ∧
          observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
          rel state'
            { arch := addiNext memoryState.arch rd rs1 imm,
              memory := memoryState.memory }
      else rel state' memoryState)
    (horder : ∀ (start : Nat) (state : State)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (_, observation) := machine.step state input
      if observation.valid then observation.order = start else True)
    {start : Nat} {coreState : State} {memoryState : RvMemoryState}
    (cycles : List Input) (hrel : rel coreState memoryState)
    (hall : ∀ input ∈ cycles, admit input) :
    ∃ program : List AddiInstruction,
      AddiRvfiCycleTrace machine memoryState.memory start coreState
        memoryState.arch cycles program ∧
      rel (rvfiStateAfter machine coreState cycles)
        { arch := addiProgramState memoryState.arch program,
          memory := memoryState.memory } := by
  induction cycles generalizing start coreState memoryState with
  | nil =>
      refine ⟨[], .nil start coreState memoryState.arch, ?_⟩
      simpa [rvfiStateAfter, addiProgramState] using hrel
  | cons input cycles ih =>
      have hadmit : admit input := hall input (by simp)
      have htail : ∀ input' ∈ cycles, admit input' := by
        intro input' hmem
        exact hall input' (by simp [hmem])
      have hcase := hstep coreState memoryState input hrel hadmit
      have horderCase := horder start coreState memoryState input hrel hadmit
      cases hmachine : machine.step coreState input with
      | mk coreState' observation =>
          simp only [hmachine] at hcase horderCase
          by_cases hv : observation.valid = true
          · have hcase' : ∃ w rd rs1 imm,
                input.memory = memoryState.memory ∧
                observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
                rel coreState'
                  { arch := addiNext memoryState.arch rd rs1 imm,
                    memory := memoryState.memory } := by
              simpa [hv] using hcase
            rcases hcase' with
              ⟨w, rd, rs1, imm, hmem, hboundary, hrel'⟩
            have horder' : observation.order = start := by
              simpa [hv] using horderCase
            have hdecode : Fetched.decode (.word w) =
                some (.alu .add rd (.reg rs1) (.imm imm)) :=
              hboundary.1.2.2.1
            let instruction : AddiInstruction :=
              { word := w, rd := rd, rs1 := rs1, imm := imm,
                decode := hdecode }
            have hinput : input =
                addiProgramInput memoryState.memory instruction := by
              cases input with
              | mk fetched memory irq =>
                  have hfetched : fetched = .word w := by
                    simpa using hboundary.1.2.1
                  have hirq : irq = 0 := by
                    simpa using hboundary.1.1
                  cases hfetched
                  cases hmem
                  cases hirq
                  rfl
            have hboundary' :
                Rv32iBoundary memoryState.arch
                  (addiProgramInput memoryState.memory instruction)
                  observation
                  { arch := addiNext memoryState.arch rd rs1 imm,
                    memory := memoryState.memory }
                  (addiRetirement memoryState.arch
                    (addiProgramInput memoryState.memory instruction)
                    rd rs1 imm) := by
              have hboundaryAlu :=
                RvfiObservation.addiBoundary_rv32i w rd rs1 imm hboundary
              rw [← hinput]
              simpa [instruction, AddiInstruction.toAlu, addiNext,
                aluNext, addiRetirement, aluRetirement, addiEffects,
                aluEffects, src1Val, src2Val, aluSem, hmem] using
                hboundaryAlu
            obtain ⟨program, htrace, hfinal⟩ :=
              ih (start := start + 1) (coreState := coreState')
                (memoryState :=
                  { arch := addiNext memoryState.arch rd rs1 imm,
                    memory := memoryState.memory }) hrel' htail
            refine ⟨instruction :: program, ?_, ?_⟩
            · exact .retire hmachine hinput horder' hboundary' htrace
            · simpa [rvfiStateAfter, addiProgramState, hmachine]
                using hfinal
          · have hv' : observation.valid = false := by
              cases hvalue : observation.valid with
              | false => exact rfl
              | true => exact False.elim (hv hvalue)
            have hrel' : rel coreState' memoryState := by
              simpa [hv, hv'] using hcase
            obtain ⟨program, htrace, hfinal⟩ :=
              ih (start := start) (coreState := coreState')
                (memoryState := memoryState) hrel' htail
            refine ⟨program, ?_, ?_⟩
            · exact .bubble hmachine hv' htrace
            · simpa [rvfiStateAfter, hmachine] using hfinal

#print axioms LeanModels.Refine.addiRvfiCycleTrace_of_step

end LeanModels.Refine
