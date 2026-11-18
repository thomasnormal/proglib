import LeanModels.Rust.Ast

namespace LeanModels.Rust

/-! A first executable MIR family.  The relation is primary: `Step` describes
one structured MIR statement, and `Steps` composes those relation clauses.
`run` is the kernel-reducible fold used by checks and is proved to be in the
relation below.  Unsupported places, rvalues, terminators and control-flow
shapes remain explicit refusals. -/

inductive Slot where
  | uninit
  | value (n : Int)
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

structure State where
  locals : List (Nat × Slot) := []
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

inductive Event where
  | storageLive (localId : Nat)
  | storageDead (localId : Nat)
  | assign (localId : Nat) (value : Int)
  | placeMention (localId : Nat)
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

structure Trace where
  state : State
  events : List Event
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

inductive Refusal where
  | unsupported (what : String)
  | malformed (what : String)
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

def setSlot (s : State) (localId : Nat) (slot : Slot) : State :=
  { locals := (localId, slot) :: s.locals.filter (fun item => item.1 != localId) }

def littleEndian (bytes : List Nat) (shift : Nat := 0) : Nat :=
  match bytes with
  | [] => 0
  | byte :: rest => byte * 256 ^ shift + littleEndian rest (shift + 1)

def bytesValue (bytes : List Nat) : Option Int :=
  if bytes.length ≤ 8 ∧ bytes.all (· ≤ 255) then
    some (Int.ofNat (littleEndian bytes))
  else none

def operandValue : Operand → Option Int
  | .constant _ bytes => bytesValue bytes
  | .copy _ | .move _ | .unsupported _ => none

def statementStep (s : State) (statement : Statement) : Option (State × Event) :=
  match statement with
  | .storageLive localId => some (setSlot s localId .uninit, .storageLive localId)
  | .storageDead localId => some (setSlot s localId .uninit, .storageDead localId)
  | .placeMention place =>
      if place.projection.isEmpty then some (s, .placeMention place.localId) else none
  | .assign place (.use operand) =>
      if place.projection.isEmpty then
        match operandValue operand with
        | some value => some (setSlot s place.localId (.value value), .assign place.localId value)
        | none => none
      else none
  | .assign _ (.unsupported _) | .unsupported _ => none

def Step (s : State) (statement : Statement) (s' : State) (event : Event) : Prop :=
  statementStep s statement = some (s', event)

def statementsRun : List Statement → State → Option Trace
  | [], state => some { state, events := [] }
  | statement :: rest, state => do
      let (state', event) ← statementStep state statement
      let trace ← statementsRun rest state'
      pure { trace with events := event :: trace.events }

def bodyRun (body : Body) : Option Trace :=
  match body.blocks with
  | [{ statements, terminator := .ret }] => statementsRun statements {}
  | _ => none

def BodyInSteps (body : Body) (trace : Trace) : Prop :=
  ∃ statements, body.blocks = [{ statements, terminator := .ret }] ∧
    statementsRun statements {} = some trace

theorem bodyRun_in_steps {body : Body} {trace : Trace}
    (h : bodyRun body = some trace) : BodyInSteps body trace := by
  unfold bodyRun at h
  cases hblocks : body.blocks with
  | nil => simp [hblocks] at h
  | cons block rest =>
      cases rest with
      | nil =>
          cases block with
          | mk statements terminator =>
              cases terminator with
              | ret =>
                  simp [hblocks] at h
                  exact ⟨statements, by simp [hblocks], h⟩
              | unsupported kind => simp [hblocks] at h
      | cons block2 rest2 => simp [hblocks] at h

def run (program : Envelope) : Option Trace :=
  match program.bodies.find? (·.instanceId == program.entry) with
  | some body => bodyRun body
  | none => none

def ProgramInSteps (program : Envelope) (trace : Trace) : Prop :=
  ∃ body, program.bodies.find? (·.instanceId == program.entry) = some body ∧ BodyInSteps body trace

theorem run_in_steps {program : Envelope} {trace : Trace}
    (h : run program = some trace) : ProgramInSteps program trace := by
  unfold run at h
  cases hfind : program.bodies.find? (·.instanceId == program.entry) with
  | none => simp [hfind] at h
  | some body =>
      simp [hfind] at h
      exact ⟨body, hfind, bodyRun_in_steps h⟩

def InSteps : List Statement → State → State → List Event → Prop
  | [], initial, final, events => final = initial ∧ events = []
  | statement :: rest, initial, final, events =>
      ∃ middle event tail,
        Step initial statement middle event ∧ InSteps rest middle final tail ∧ events = event :: tail

theorem statementStep_in_step {s s' : State} {statement : Statement} {event : Event}
    (h : statementStep s statement = some (s', event)) : Step s statement s' event := by
  exact h

theorem statementsRun_in_steps {statements : List Statement} {initial final : State}
    {events : List Event} (h : statementsRun statements initial = some { state := final, events }) :
    InSteps statements initial final events := by
  induction statements generalizing initial final events with
  | nil => simp [statementsRun] at h; exact ⟨h.1.symm, h.2⟩
  | cons statement rest ih =>
      simp only [statementsRun] at h
      generalize hs : statementStep initial statement = result at h
      cases result with
      | none => simp_all
      | some pair =>
          cases pair with
          | mk middle event =>
              generalize hr : statementsRun rest middle = tail at h
              cases tail with
              | none => simp_all
              | some trace =>
                  simp [Option.bind] at h
                  rw [hr] at h
                  simp at h
                  rcases h with ⟨hstate, hevents⟩
                  subst final
                  subst events
                  exact ⟨middle, event, trace.events, hs, ih hr, rfl⟩

end LeanModels.Rust
