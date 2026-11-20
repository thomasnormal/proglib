import LeanModels.Refine.Progress
import LeanModels.Refine.RvfiRv32iProgram

/-!
# All-prefix progress for mixed RVFI refinement

`Rv32iRvfiCycleTrace_of_step_refines` gives the end-to-end result for one
finite cycle window.  A real core runs on an unbounded cycle schedule, so its
refinement statement also needs an explicit progress witness: every finite
prefix of the target retirement-input stream is reached at some finite cycle
boundary.  This file states that witness for the packed RVFI boundary and
combines it with the mixed RV32I certificate.

The target is an input schedule rather than a guessed decoder stream.  The
per-cycle invariant remains responsible for identifying each valid row as an
admitted `Rv32iInstruction`; the progress witness only says where a target
prefix appears.  Thus no scheduler, retirement order, or instruction choice
is hidden in this layer.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Explicit progress at the RVFI cycle boundary -/

/-- Every finite target input prefix is retained by `retireInputs` at some
    finite boundary of the packed cycle schedule. -/
def Rv32iRetiresTarget {State : Type}
    (machine : RvfiCycleMachine State) (initial : State)
    (schedule target : Nat → Input) : Prop :=
  ∀ k : Nat, ∃ n : Nat,
    retireInputs machine.toCycleMachine initial (schedulePrefix schedule n) =
      schedulePrefix target k

theorem schedulePrefix_admit {α : Type} (schedule : Nat → α)
    (admit : α → Prop) (hschedule : ∀ n, admit (schedule n)) :
    ∀ n input, input ∈ schedulePrefix schedule n → admit input := by
  intro n
  induction n with
  | zero =>
      intro input hmem
      simp [schedulePrefix] at hmem
  | succ n ih =>
      intro input hmem
      simp only [schedulePrefix_succ, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hschedule n
      · exact ih input hmem

/-! ## Mixed RV32I all-prefix theorem -/

/-! The result below is the public stream-level shape of the R2 claim.  A
loaded-core proof still supplies the indexed per-cycle invariant and the
progress witness; this structure keeps the resulting certificate, normalized
trace, and target-state relation together at each finite target prefix. -/

/-- A single target-prefix witness for an all-prefix RV32I refinement. -/
structure Rv32iPrefixRefinement {State : Type}
    (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop)
    (start : Nat) (coreState : State) (memoryState : RvMemoryState)
    (schedule target : Nat → Input) (k : Nat) where
  boundary : Nat
  program : List Rv32iInstruction
  certificate :
    Rv32iRvfiCycleTrace machine start coreState memoryState
      (schedulePrefix schedule boundary) program
  program_inputs_eq :
    rv32iProgramInputs memoryState program = schedulePrefix target k
  program_state_eq :
    rv32iProgramState memoryState program =
      rvMemoryStateAfter profile memoryState (schedulePrefix target k)
  trace_eq :
    normalizeRvfiTrace? start
        (rvfiObservations machine coreState (schedulePrefix schedule boundary)) =
      some (trace (rvMemoryMachineWith profile) memoryState
        (schedulePrefix target k))
  cycle_trace_eq :
    cycleTrace machine.toCycleMachine coreState
        (schedulePrefix schedule boundary) =
      trace (rvMemoryMachineWith profile) memoryState
        (schedulePrefix target k)
  state_rel :
    rel (rvfiStateAfter machine coreState (schedulePrefix schedule boundary))
      (rvMemoryStateAfter profile memoryState (schedulePrefix target k))

/-- The all-prefix stream refinement exposed to a loaded-core theorem. -/
def Rv32iAllPrefixRefinement {State : Type}
    (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop)
    (start : Nat) (coreState : State) (memoryState : RvMemoryState)
    (schedule target : Nat → Input) : Prop :=
  ∀ k : Nat,
    Nonempty (Rv32iPrefixRefinement profile machine rel start coreState
      memoryState schedule target k)

def Rv32iResetRefinement {State : Type}
    (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop)
    (schedule target : Nat → Input) : Prop :=
  Rv32iAllPrefixRefinement profile machine rel 0 machine.init
    (rvMemoryMachineWith profile).init schedule target

end LeanModels.Refine
