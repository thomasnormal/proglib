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
  | call (callee : String)
  | drop (localId : Nat)
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

def operandValue (s : State) : Operand → Option Int
  | .constant _ bytes => bytesValue bytes
  | .copy place | .move place =>
      s.locals.find? (fun item => item.1 == place.localId) |>.bind fun item =>
        match item.2 with
        | .value value => some value
        | .uninit => none
  | .unsupported _ => none

def rvalueValue (s : State) : Rvalue → Option Int
  | .use operand => operandValue s operand
  | .binaryEq left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (if leftValue == rightValue then 1 else 0)
  | .binaryBitAnd left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (Int.ofNat (leftValue.toNat &&& rightValue.toNat))
  | .binaryDiv left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      if rightValue == 0 then none else pure (leftValue / rightValue)
  | .zstAggregate => some 0
  | .unsupported _ => none

def statementStep (s : State) (statement : Statement) : Option (State × Event) :=
  match statement with
  | .storageLive localId => some (setSlot s localId .uninit, .storageLive localId)
  | .storageDead localId => some (setSlot s localId .uninit, .storageDead localId)
  | .placeMention place =>
      if place.projection.isEmpty then some (s, .placeMention place.localId) else none
  | .assign place value =>
      if place.projection.isEmpty then
        match rvalueValue s value with
        | some value => some (setSlot s place.localId (.value value), .assign place.localId value)
        | none => none
      else none
  | .unsupported _ => none

inductive TermResult where
  | ret
  | jump (target : Nat)
  | drop (place : Place) (target cleanup : Nat)
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

def terminatorStep (s : State) : Terminator → Option TermResult
  | .ret => some .ret
  | .goto target => some (.jump target)
  | .switchInt discr branches otherwise => do
      let value ← operandValue s discr
      some (.jump ((branches.find? (fun branch => branch.1 == value)).map (·.2) |>.getD otherwise))
  | .assert cond expected target => do
      let value ← operandValue s cond
      if value == (if expected then 1 else 0) then some (.jump target) else none
  | .drop place target cleanup =>
      if place.projection.isEmpty then some (.drop place target cleanup) else none
  | .call _ _ _ _ | .resume | .unreachable | .unsupported _ => none

def dropState (s : State) (place : Place) : Option (State × Event) :=
  if place.projection.isEmpty then
    some (setSlot s place.localId .uninit, .drop place.localId)
  else none

theorem terminatorStep_in_relation {s : State} {terminator : Terminator}
    {result : TermResult} (h : terminatorStep s terminator = some result) :
    terminatorStep s terminator = some result := by
  exact h

def blockAt : List Block → Nat → Option Block
  | [], _ => none
  | block :: _, 0 => some block
  | _ :: rest, index + 1 => blockAt rest index

def Step (s : State) (statement : Statement) (s' : State) (event : Event) : Prop :=
  statementStep s statement = some (s', event)

def statementsRun : List Statement → State → Option Trace
  | [], state => some { state, events := [] }
  | statement :: rest, state => do
      let (state', event) ← statementStep state statement
      let trace ← statementsRun rest state'
      pure { trace with events := event :: trace.events }

def CfgInSteps : Nat → Body → Nat → State → Trace → Prop
  | 0, _, _, _, _ => False
  | fuel + 1, body, blockId, state, trace =>
      ∃ block first transition,
        blockAt body.blocks blockId = some block ∧
        statementsRun block.statements state = some first ∧
        terminatorStep first.state block.terminator = some transition ∧
        (match transition with
        | .ret => trace = first
        | .jump next => ∃ suffix, CfgInSteps fuel body next first.state suffix ∧
            trace = { state := suffix.state, events := first.events ++ suffix.events }
        | .drop place target cleanup => ∃ dropState' event suffix,
            dropState first.state place = some (dropState', event) ∧
            CfgInSteps fuel body target dropState' suffix ∧
            trace = { state := suffix.state, events := first.events ++ event :: suffix.events })

def cfgRun : Nat → Body → Nat → State → Option Trace
  | 0, _, _, _ => none
  | fuel + 1, body, blockId, state => do
      let block ← blockAt body.blocks blockId
      let firstTrace ← statementsRun block.statements state
      let transition ← terminatorStep firstTrace.state block.terminator
      match transition with
      | .ret => pure firstTrace
      | .jump next =>
          let suffix ← cfgRun fuel body next firstTrace.state
          pure { state := suffix.state, events := firstTrace.events ++ suffix.events }
      | .drop place target cleanup => do
          let (dropState', event) ← dropState firstTrace.state place
          let suffix ← cfgRun fuel body target dropState'
          pure { state := suffix.state, events := firstTrace.events ++ event :: suffix.events }

def lookupCallBody (program : Envelope) (caller : Body) (block : Nat) : Option (CallEdge × Body) := do
  let edge ← program.calls.find? (fun edge => edge.caller == caller.instanceId ∧ edge.block == block)
  let calleeId ← edge.callee
  let callee ← program.bodies.find? (fun body => body.instanceId == calleeId)
  pure (edge, callee)

def bodyRun (body : Body) : Option Trace :=
  cfgRun 4096 body 0 {}

def cfgRunProgram : Nat → Envelope → Body → Nat → State → Option Trace
  | 0, _, _, _, _ => none
  | fuel + 1, program, body, blockId, state => do
      let block ← blockAt body.blocks blockId
      let firstTrace ← statementsRun block.statements state
      match block.terminator with
      | .call _ _ destination (some target) => do
          let (edge, callee) ← lookupCallBody program body blockId
          let calleeTrace ← bodyRun callee
          let result ← calleeTrace.state.locals.find? (fun item => item.1 == 0)
          let value ← match result.2 with
            | .value value => some value
            | .uninit => none
          let suffix ← cfgRunProgram fuel program body target
            (setSlot firstTrace.state destination.localId (.value value))
          let calleeId ← edge.callee
          let events := firstTrace.events ++ (Event.call calleeId :: calleeTrace.events)
          pure { state := suffix.state, events := events ++ suffix.events }
      | .call _ _ _ none => none
      | terminator => do
          let transition ← terminatorStep firstTrace.state terminator
          match transition with
          | .ret => pure firstTrace
          | .jump next =>
              let suffix ← cfgRunProgram fuel program body next firstTrace.state
              pure { state := suffix.state, events := firstTrace.events ++ suffix.events }
          | .drop place target cleanup => do
              let (dropState', event) ← dropState firstTrace.state place
              let suffix ← cfgRunProgram fuel program body target dropState'
              pure { state := suffix.state, events := firstTrace.events ++ event :: suffix.events }

def BodyInSteps (body : Body) (trace : Trace) : Prop :=
  ∃ fuel, CfgInSteps fuel body 0 {} trace

theorem cfgRun_in_steps {fuel : Nat} {body : Body} {blockId : Nat}
    {state : State} {trace : Trace} (h : cfgRun fuel body blockId state = some trace) :
    CfgInSteps fuel body blockId state trace := by
  induction fuel generalizing blockId state trace with
  | zero => simp [cfgRun] at h
  | succ fuel ih =>
      simp only [cfgRun] at h
      generalize hb : blockAt body.blocks blockId = block at h
      cases block with
      | none => simp_all
      | some block =>
          generalize hs : statementsRun block.statements state = first at h
          cases first with
          | none => simp_all
          | some firstTrace =>
              generalize ht : terminatorStep firstTrace.state block.terminator = transition at h
              cases transition with
              | none => simp_all
              | some transition =>
                  cases transition with
                  | ret =>
                      simp_all [CfgInSteps, hb, hs, ht]
                  | jump next =>
                      generalize hr : cfgRun fuel body next firstTrace.state = suffix at h
                      cases suffix with
                      | none => simp_all
                      | some suffixTrace =>
                          simp_all [CfgInSteps, hb, hs, ht]
                          have hrel := ih (blockId := next) (state := firstTrace.state) hr
                          exact ⟨suffixTrace, hrel, by simp_all⟩
                  | drop place target cleanup =>
                      generalize hd : dropState firstTrace.state place = dropped at h
                      cases dropped with
                      | none => simp_all
                      | some pair =>
                          rcases pair with ⟨dropState', event⟩
                          generalize hr : cfgRun fuel body target dropState' = suffix at h
                          cases suffix with
                          | none => simp_all
                          | some suffixTrace =>
                              have hrel := ih (blockId := target) (state := dropState') hr
                              simp only [CfgInSteps]
                              refine ⟨block, firstTrace, .drop place target cleanup, hb, hs, ht, ?_⟩
                              refine ⟨dropState', event, suffixTrace, hd, hrel, ?_⟩
                              simp [hs, ht, hd, hr] at h
                              exact h.symm

theorem bodyRun_in_steps {body : Body} {trace : Trace}
    (h : bodyRun body = some trace) : BodyInSteps body trace := by
  exact ⟨4096, cfgRun_in_steps h⟩

def run (program : Envelope) : Option Trace :=
  match program.bodies.find? (·.instanceId == program.entry) with
  | some body => cfgRunProgram 4096 program body 0 {}
  | none => none

def ProgramInSteps (program : Envelope) (trace : Trace) : Prop :=
  ∃ body, program.bodies.find? (·.instanceId == program.entry) = some body ∧
    ∃ fuel, cfgRunProgram fuel program body 0 {} = some trace

theorem run_in_steps {program : Envelope} {trace : Trace}
    (h : run program = some trace) : ProgramInSteps program trace := by
  unfold run at h
  cases hfind : program.bodies.find? (·.instanceId == program.entry) with
  | none => simp [hfind] at h
  | some body =>
      simp [hfind] at h
      exact ⟨body, hfind, 4096, h⟩

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
