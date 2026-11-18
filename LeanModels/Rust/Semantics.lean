import LeanModels.Rust.Ast

namespace LeanModels.Rust

/-! A first executable MIR family.  The relation is primary: `Step` describes
one structured MIR statement, and `Steps` composes those relation clauses.
`run` is the kernel-reducible fold used by checks and is proved to be in the
relation below.  Unsupported places, rvalues, terminators and control-flow
shapes remain explicit refusals. -/

structure Pointer where
  provenance : Nat
  address : Nat
deriving Repr, Inhabited, BEq, DecidableEq

inductive FieldValue where
  | int (n : Int)
  | pointer (p : Pointer)
deriving Repr, Inhabited, BEq, DecidableEq

inductive Cell where
  | int (n : Int)
  | pointer (p : Pointer)
  | aggregate (fields : List FieldValue)
  | unit
deriving Repr, Inhabited, BEq, DecidableEq

inductive Slot where
  | uninit
  | value (n : Int)
  | cell (value : Cell)
deriving Repr, Inhabited, BEq, DecidableEq

structure State where
  locals : List (Nat × Slot) := []
  placements : List (Nat × Nat) := []
  types : List TypeLayout := []
deriving Repr, Inhabited, BEq, DecidableEq

inductive Event where
  | storageLive (localId : Nat)
  | storageDead (localId : Nat)
  | assign (localId : Nat) (value : Int)
  | assignOpaque (localId : Nat)
  | placeMention (localId : Nat)
  | call (callee : String)
  | drop (localId : Nat)
deriving Repr, Inhabited, BEq, DecidableEq

structure Trace where
  state : State
  events : List Event
deriving Repr, Inhabited, BEq, DecidableEq

inductive Refusal where
  | unsupported (what : String)
  | malformed (what : String)
deriving Repr, Inhabited, BEq, DecidableEq

inductive Outcome where
  | returned (trace : Trace)
  | panicked
  | ub (kind : String)
  | refused (reason : Refusal)
  | outOfFuel
deriving Repr, Inhabited, BEq, DecidableEq

inductive CheckedOutcome where
  | value (n : Int)
  | overflow
  | divideByZero
deriving Repr, Inhabited, BEq, DecidableEq

def Outcome.isReturned : Outcome → Bool
  | .returned _ => true
  | _ => false

def setSlot (s : State) (localId : Nat) (slot : Slot) : State :=
  { s with locals := (localId, slot) :: s.locals.filter (fun item => item.1 != localId) }

def littleEndian (bytes : List Nat) (shift : Nat := 0) : Nat :=
  match bytes with
  | [] => 0
  | byte :: rest => byte * 256 ^ shift + littleEndian rest (shift + 1)

def bytesValue (bytes : List Nat) : Option Int :=
  if bytes.length ≤ 8 ∧ bytes.all (· ≤ 255) then
    some (Int.ofNat (littleEndian bytes))
  else none

def checkedSub32 (left right : Int) : CheckedOutcome :=
  let result := left - right
  if result < -(2 ^ 31) ∨ result > 2 ^ 31 - 1 then .overflow else .value result

def checkedAdd32 (left right : Int) : CheckedOutcome :=
  let result := left + right
  if result < -(2 ^ 31) ∨ result > 2 ^ 31 - 1 then .overflow else .value result

def checkedBinaryOutcome (op : String) (left right : Int) : CheckedOutcome :=
  match op with
  | "Sub" => checkedSub32 left right
  | "Add" => checkedAdd32 left right
  | "Div" => if right == 0 then .divideByZero else .value (left / right)
  | _ => .overflow

def placementOf (s : State) (localId : Nat) : Nat :=
  (s.placements.find? (fun item => item.1 == localId)).map (·.2) |>.getD localId

def allocationPlacementsFrom (placement : Nat → Nat) (index : Nat) :
    List Allocation → List (Nat × Nat)
  | [] => []
  | _ :: rest => (index, placement index) :: allocationPlacementsFrom placement (index + 1) rest

def allocationPlacements (placement : Nat → Nat) (allocations : List Allocation) :
    List (Nat × Nat) :=
  allocationPlacementsFrom placement 0 allocations

def sameProvenance (left right : Pointer) : Prop :=
  left.provenance = right.provenance

theorem pointer_address_independent (provenance address₁ address₂ : Nat) :
    sameProvenance
      { provenance, address := address₁ }
      { provenance, address := address₂ } := by
  rfl

def slotCell : Slot → Option Cell
  | .uninit => none
  | .value value => some (.int value)
  | .cell value => some value

def cellInt : Cell → Option Int
  | .int value => some value
  | _ => none

def cellField : Cell → Option FieldValue
  | .int value => some (.int value)
  | .pointer pointer => some (.pointer pointer)
  | _ => none

def fieldCell : FieldValue → Cell
  | .int value => .int value
  | .pointer pointer => .pointer pointer

def cellSlot : Cell → Slot
  | .int value => .value value
  | value => .cell value

def localSlot (s : State) (localId : Nat) : Option Slot :=
  s.locals.find? (fun item => item.1 == localId) |>.map (·.2)

def projectCell (s : State) (cell : Cell) : List Projection → Option Cell
  | [] => some cell
  | .deref :: rest =>
      match cell with
      | .pointer pointer => localSlot s pointer.provenance |>.bind slotCell |>.bind (projectCell s · rest)
      | _ => none
  | .field index _ :: rest =>
      match cell with
      | .aggregate fields =>
          fields.drop index |>.head? |>.map fieldCell |>.bind (projectCell s · rest)
      | _ => none
  | .downcast _ :: _ | .unsupported _ :: _ => none

def readCell (s : State) (place : Place) : Option Cell :=
  localSlot s place.localId |>.bind slotCell |>.bind (projectCell s · place.projection)

def writeCell (s : State) (place : Place) (value : Cell) : Option State :=
  match place.projection with
  | [] => some (setSlot s place.localId (cellSlot value))
  | .deref :: rest =>
      localSlot s place.localId |>.bind slotCell |>.bind fun cell =>
        match cell with
        | .pointer pointer =>
            if rest.isEmpty then some (setSlot s pointer.provenance (cellSlot value)) else none
        | _ => none
  | .field index _ :: rest =>
      if rest.isEmpty then
        localSlot s place.localId |>.bind slotCell |>.bind fun cell =>
          match cell with
          | .aggregate fields =>
              fields.drop index |>.head? |>.bind fun _old =>
                some (setSlot s place.localId
                  (match value with
                  | .int n => .cell (.aggregate (fields.set index (.int n)))
                  | _ => .cell (.aggregate fields)))
          | _ => none
      else none
  | .downcast _ :: _ | .unsupported _ :: _ => none

def typedBytesValue (s : State) (ty : Nat) (bytes : List Nat) : Option Int :=
  let layout := s.types.find? (fun item => item.id == toString ty)
  match layout with
  | none => bytesValue bytes
  | some info =>
    match info.sizeBits with
    | some 0 => some 0
    | some sizeBits =>
      if bytes.length ≤ 8 ∧ bytes.all (· ≤ 255) then
        let raw := Int.ofNat (littleEndian bytes)
        match info.signed with
        | some true =>
            if sizeBits ≤ 64 ∧ raw ≥ 2 ^ (sizeBits - 1) then
              some (raw - 2 ^ sizeBits)
            else some raw
        | some false => some raw
        | none => none
      else none
    | none => none

def operandCell (s : State) : Operand → Option Cell
  | .constant _ bytes ty provenance =>
      match s.types.find? (fun item => item.id == toString ty), provenance with
      | some info, some target =>
          if info.kind.startsWith "RigidTy(RawPtr" || info.kind.startsWith "RigidTy(Ref" then
            some (.pointer { provenance := target, address := placementOf s target })
          else typedBytesValue s ty bytes |>.map Cell.int
      | _, _ => typedBytesValue s ty bytes |>.map Cell.int
  | .copy place | .move place =>
      readCell s place
  | .unsupported _ => none

def operandValue (s : State) (operand : Operand) : Option Int :=
  operandCell s operand |>.bind cellInt

def rvalueValue (s : State) : Rvalue → Option Int
  | .use operand => operandValue s operand
  | .binaryEq left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (if leftValue == rightValue then 1 else 0)
  | .binaryNe left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (if leftValue != rightValue then 1 else 0)
  | .binaryBitAnd left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (Int.ofNat (leftValue.toNat &&& rightValue.toNat))
  | .binaryDiv left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      if rightValue == 0 then none else pure (leftValue / rightValue)
  | .checkedBinary op left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      match checkedBinaryOutcome op leftValue rightValue with
      | .value value => pure value
      | .overflow | .divideByZero => none
  | .ref _ | .aggregate _ _ => none
  | .zstAggregate => some 0
  | .unsupported _ => none

def rvalueCell (s : State) : Rvalue → Option Cell
  | .use operand => operandCell s operand
  | .binaryEq left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (.int (if leftValue == rightValue then 1 else 0))
  | .binaryNe left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (.int (if leftValue != rightValue then 1 else 0))
  | .binaryBitAnd left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (.int (Int.ofNat (leftValue.toNat &&& rightValue.toNat)))
  | .binaryDiv left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      if rightValue == 0 then none else pure (.int (leftValue / rightValue))
  | .checkedBinary op left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      match checkedBinaryOutcome op leftValue rightValue with
      | .value value => pure (.aggregate [.int value, .int 0])
      | .overflow => pure (.aggregate [.int 0, .int 1])
      | .divideByZero => none
  | .ref place => some (.pointer { provenance := place.localId, address := placementOf s place.localId })
  | .aggregate _ fields => do
      let values ← fields.mapM (operandCell s) >>= (·.mapM cellField)
      pure (.aggregate values)
  | .zstAggregate => some (.int 0)
  | .unsupported _ => none

def eventForCell (localId : Nat) : Cell → Event
  | .int value => .assign localId value
  | _ => .assignOpaque localId

def statementStep (s : State) (statement : Statement) : Option (State × Event) :=
  match statement with
  | .storageLive localId => some (setSlot s localId .uninit, .storageLive localId)
  | .storageDead localId => some (setSlot s localId .uninit, .storageDead localId)
  | .placeMention place =>
      if readCell s place |>.isSome then some (s, .placeMention place.localId) else none
  | .assign place value =>
      match rvalueCell s value with
      | some cell => writeCell s place cell |>.map fun state => (state, eventForCell place.localId cell)
      | none => none
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

inductive CfgSteps (body : Body) : Nat → State → Trace → Prop
  | ret {blockId : Nat} {state : State} {block : Block} {first : Trace}
      (hb : blockAt body.blocks blockId = some block)
      (hs : statementsRun block.statements state = some first)
      (ht : terminatorStep first.state block.terminator = some .ret) :
      CfgSteps body blockId state first
  | jump {blockId next : Nat} {state : State} {block : Block} {first suffix : Trace}
      (hb : blockAt body.blocks blockId = some block)
      (hs : statementsRun block.statements state = some first)
      (ht : terminatorStep first.state block.terminator = some (.jump next))
      (rest : CfgSteps body next first.state suffix) :
      CfgSteps body blockId state { state := suffix.state, events := first.events ++ suffix.events }
  | drop {blockId target cleanup : Nat} {state : State} {block : Block} {first suffix : Trace}
      {place : Place} {dropState' : State} {event : Event}
      (hb : blockAt body.blocks blockId = some block)
      (hs : statementsRun block.statements state = some first)
      (ht : terminatorStep first.state block.terminator = some (.drop place target cleanup))
      (hd : dropState first.state place = some (dropState', event))
      (rest : CfgSteps body target dropState' suffix) :
      CfgSteps body blockId state { state := suffix.state, events := first.events ++ event :: suffix.events }

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

def bindCallArgs : State → List Operand → Nat → Option State
  | state, [], _ => some state
  | state, operand :: rest, localId => do
      let value ← operandValue state operand
      bindCallArgs (setSlot state localId (.value value)) rest (localId + 1)

def returnValue (trace : Trace) : Option Int :=
  (trace.state.locals.find? (fun item => item.1 == 0)).bind fun item =>
    match item.2 with
    | .value value => some value
    | .cell (.int value) => some value
    | .cell _ => none
    | .uninit => none

def cfgRunProgram : Nat → Envelope → Body → Nat → State → Option Trace
  | 0, _, _, _, _ => none
  | fuel + 1, program, body, blockId, state => do
      let block ← blockAt body.blocks blockId
      let firstTrace ← statementsRun block.statements state
      match block.terminator with
      | .call _ args destination (some target) => do
          let (edge, callee) ← lookupCallBody program body blockId
          let calleeState ← bindCallArgs
            { placements := firstTrace.state.placements, types := firstTrace.state.types } args 1
          let calleeTrace ← cfgRun fuel callee 0 calleeState
          let value ← returnValue calleeTrace
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

inductive ProgramSteps (program : Envelope) : Body → Nat → State → Trace → Prop
  | ret {body : Body} {blockId : Nat} {state : State} {block : Block} {first : Trace}
      (hb : blockAt body.blocks blockId = some block)
      (hs : statementsRun block.statements state = some first)
      (ht : terminatorStep first.state block.terminator = some .ret) :
      ProgramSteps program body blockId state first
  | jump {body : Body} {blockId next : Nat} {state : State} {block : Block} {first suffix : Trace}
      (hb : blockAt body.blocks blockId = some block)
      (hs : statementsRun block.statements state = some first)
      (ht : terminatorStep first.state block.terminator = some (.jump next))
      (rest : ProgramSteps program body next first.state suffix) :
      ProgramSteps program body blockId state
        { state := suffix.state, events := first.events ++ suffix.events }
  | drop {body : Body} {blockId target cleanup : Nat} {state : State}
      {block : Block} {first suffix : Trace} {place : Place} {dropState' : State} {event : Event}
      (hb : blockAt body.blocks blockId = some block)
      (hs : statementsRun block.statements state = some first)
      (ht : terminatorStep first.state block.terminator = some (.drop place target cleanup))
      (hd : dropState first.state place = some (dropState', event))
      (rest : ProgramSteps program body target dropState' suffix) :
      ProgramSteps program body blockId state
        { state := suffix.state, events := first.events ++ event :: suffix.events }
  | call {body : Body} {blockId target : Nat} {state : State}
      {block : Block} {first calleeTrace suffix : Trace} {calleeState : State}
      {func : Operand} {args : List Operand} {destination : Place}
      {edge : CallEdge} {calleeId : String} {callee : Body} {value : Int}
      (hb : blockAt body.blocks blockId = some block)
      (hs : statementsRun block.statements state = some first)
      (ht : block.terminator = .call func args destination (some target))
      (hl : lookupCallBody program body blockId = some (edge, callee))
      (he : edge.callee = some calleeId)
      (ha : bindCallArgs
        { placements := first.state.placements, types := first.state.types } args 1 = some calleeState)
      (hc : CfgSteps callee 0 calleeState calleeTrace)
      (hv : returnValue calleeTrace = some value)
      (rest : ProgramSteps program body target
        (setSlot first.state destination.localId (.value value)) suffix) :
      ProgramSteps program body blockId state
        { state := suffix.state,
          events := first.events ++ (Event.call calleeId :: (calleeTrace.events ++ suffix.events)) }

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

theorem cfgInSteps_to_cfgSteps {fuel : Nat} {body : Body} {blockId : Nat}
    {state : State} {trace : Trace} (h : CfgInSteps fuel body blockId state trace) :
    CfgSteps body blockId state trace := by
  induction fuel generalizing blockId state trace with
  | zero => exact False.elim h
  | succ fuel ih =>
      rcases h with ⟨block, first, transition, hb, hs, ht, hrest⟩
      cases transition with
      | ret =>
          simpa [hrest] using CfgSteps.ret hb hs ht
      | jump next =>
          rcases hrest with ⟨suffix, hrel, htrace⟩
          simpa [htrace] using CfgSteps.jump hb hs ht (ih hrel)
      | drop place target cleanup =>
          rcases hrest with ⟨dropState', event, suffix, hd, hrel, htrace⟩
          simpa [htrace] using CfgSteps.drop hb hs ht hd (ih hrel)

theorem bodyRun_in_steps {body : Body} {trace : Trace}
    (h : bodyRun body = some trace) : BodyInSteps body trace := by
  exact ⟨4096, cfgRun_in_steps h⟩

def run (program : Envelope) : Option Trace :=
  match program.bodies.find? (·.instanceId == program.entry) with
  | some body => cfgRunProgram 4096 program body 0 {}
  | none => none

def initialState (placement : Nat → Nat) (types : List TypeLayout)
    (allocations : List Allocation := []) : State :=
  { locals := [], placements := allocationPlacements placement allocations, types := types }

def runWithPlacement (placement : Nat → Nat) (program : Envelope) : Option Trace :=
  match program.bodies.find? (·.instanceId == program.entry) with
  | some body => cfgRunProgram 4096 program body 0
      (initialState placement program.types program.allocations)
  | none => none

def runOutcome (program : Envelope) : Outcome :=
  match runWithPlacement (fun n => n) program with
  | some trace => .returned trace
  | none => .refused (.unsupported "execution")

def ProgramInSteps (program : Envelope) (trace : Trace) : Prop :=
  ∃ body, program.bodies.find? (·.instanceId == program.entry) = some body ∧
    ProgramSteps program body 0 {} trace

theorem cfgRunProgram_in_steps {fuel : Nat} {program : Envelope} {body : Body}
    {blockId : Nat} {state : State} {trace : Trace}
    (h : cfgRunProgram fuel program body blockId state = some trace) :
    ProgramSteps program body blockId state trace := by
  induction fuel generalizing blockId state trace with
  | zero => simp [cfgRunProgram] at h
  | succ fuel ih =>
      simp only [cfgRunProgram] at h
      generalize hb : blockAt body.blocks blockId = block at h
      cases block with
      | none => simp_all
      | some block =>
          simp [hb] at h
          generalize hs : statementsRun block.statements state = first at h
          cases first with
          | none => simp_all
          | some firstTrace =>
              cases hterm : block.terminator with
              | call func args destination target =>
                  simp [hterm] at h
                  cases target with
                  | none => simp_all
                  | some target =>
                      generalize hl : lookupCallBody program body blockId = lookup at h
                      cases lookup with
                      | none => simp_all
                      | some pair =>
                          rcases pair with ⟨edge, callee⟩
                          cases hec : edge.callee with
                          | none => simp_all
                          | some calleeId =>
                              generalize ha : bindCallArgs
                                { placements := firstTrace.state.placements,
                                  types := firstTrace.state.types } args 1 = calleeState at h
                              cases calleeState with
                              | none => simp_all
                              | some calleeState =>
                                  generalize hc : cfgRun fuel callee 0 calleeState = calleeTrace at h
                                  cases calleeTrace with
                                  | none => simp_all
                                  | some calleeTrace =>
                                      generalize hv : returnValue calleeTrace = value at h
                                      cases value with
                                      | none => simp_all
                                      | some value =>
                                          generalize hr : cfgRunProgram fuel program body target
                                              (setSlot firstTrace.state destination.localId (.value value)) = suffix at h
                                          cases suffix with
                                          | none => simp_all
                                          | some suffixTrace =>
                                              have hcallee := cfgRun_in_steps hc
                                              have hcalleeSteps := cfgInSteps_to_cfgSteps hcallee
                                              have hrest := ih (blockId := target)
                                                (state := setSlot firstTrace.state destination.localId (.value value)) hr
                                              have htrace :
                                                  { state := suffixTrace.state,
                                                    events := firstTrace.events ++
                                                      (Event.call calleeId ::
                                                        (calleeTrace.events ++ suffixTrace.events)) } = trace := by
                                                simpa [hterm, hl, hec, ha, hc, hv, hr] using h
                                              rw [← htrace]
                                              exact ProgramSteps.call hb hs hterm hl hec ha hcalleeSteps hv hrest
              | ret =>
                  have htrace : firstTrace = trace := by
                    simpa [hterm, terminatorStep] using h
                  rw [← htrace]
                  exact ProgramSteps.ret hb hs (by simp [hterm, terminatorStep])
              | goto target =>
                  simp [hterm, terminatorStep] at h
                  have ht : terminatorStep firstTrace.state block.terminator = some (.jump target) := by
                    simp [hterm, terminatorStep]
                  generalize hr : cfgRunProgram fuel program body target firstTrace.state = suffix at h
                  cases suffix with
                  | none => simp_all
                  | some suffixTrace =>
                      have hrest := ih (blockId := target) (state := firstTrace.state) hr
                      have htrace :
                          { state := suffixTrace.state,
                            events := firstTrace.events ++ suffixTrace.events } = trace := by
                        simpa [hr] using h
                      rw [← htrace]
                      exact ProgramSteps.jump hb hs ht hrest
              | switchInt discr branches otherwise =>
                  simp [hterm] at h
                  generalize ht0 : terminatorStep firstTrace.state
                      (Terminator.switchInt discr branches otherwise) = transition at h
                  cases transition with
                  | none => simp_all
                  | some transition =>
                      cases transition with
                      | ret =>
                          cases hv : operandValue firstTrace.state discr with
                          | none => simp [terminatorStep, hv] at ht0
                          | some value => simp [terminatorStep, hv] at ht0
                      | jump target =>
                          generalize hr : cfgRunProgram fuel program body target firstTrace.state = suffix at h
                          cases suffix with
                          | none => simp_all
                          | some suffixTrace =>
                              have hrest := ih (blockId := target) (state := firstTrace.state) hr
                              have ht : terminatorStep firstTrace.state block.terminator = some (.jump target) := by
                                simpa [hterm] using ht0
                              have htrace :
                                  { state := suffixTrace.state,
                                    events := firstTrace.events ++ suffixTrace.events } = trace := by
                                simpa [ht, hr] using h
                              rw [← htrace]
                              exact ProgramSteps.jump hb hs ht hrest
                      | drop _ _ _ =>
                          cases hv : operandValue firstTrace.state discr with
                          | none => simp [terminatorStep, hv] at ht0
                          | some value => simp [terminatorStep, hv] at ht0
              | assert cond expected target =>
                  simp [hterm] at h
                  generalize ht0 : terminatorStep firstTrace.state
                      (Terminator.assert cond expected target) = transition at h
                  cases transition with
                  | none => simp_all
                  | some transition =>
                      cases transition with
                      | ret =>
                          cases hv : operandValue firstTrace.state cond with
                          | none => simp [terminatorStep, hv] at ht0
                          | some value => simp [terminatorStep, hv] at ht0
                      | jump target =>
                          generalize hr : cfgRunProgram fuel program body target firstTrace.state = suffix at h
                          cases suffix with
                          | none => simp_all
                          | some suffixTrace =>
                              have hrest := ih (blockId := target) (state := firstTrace.state) hr
                              have ht : terminatorStep firstTrace.state block.terminator = some (.jump target) := by
                                simpa [hterm] using ht0
                              have htrace :
                                  { state := suffixTrace.state,
                                    events := firstTrace.events ++ suffixTrace.events } = trace := by
                                simpa [ht, hr] using h
                              rw [← htrace]
                              exact ProgramSteps.jump hb hs ht hrest
                      | drop _ _ _ =>
                          cases hv : operandValue firstTrace.state cond with
                          | none => simp [terminatorStep, hv] at ht0
                          | some value => simp [terminatorStep, hv] at ht0
              | drop place target cleanup =>
                  simp [hterm] at h
                  generalize ht0 : terminatorStep firstTrace.state
                      (Terminator.drop place target cleanup) = transition at h
                  cases transition with
                  | none => simp_all
                  | some transition =>
                      cases transition with
                      | ret => simp [terminatorStep] at ht0
                      | jump next => simp [terminatorStep] at ht0
                      | drop place' target' cleanup' =>
                          generalize hd : dropState firstTrace.state place' = dropped at h
                          cases dropped with
                          | none => simp_all
                          | some pair =>
                              rcases pair with ⟨dropState', event⟩
                              generalize hr : cfgRunProgram fuel program body target' dropState' = suffix at h
                              cases suffix with
                              | none => simp [hd, hr] at h
                              | some suffixTrace =>
                                  have hrest := ih (blockId := target') (state := dropState') hr
                                  have ht : terminatorStep firstTrace.state block.terminator =
                                      some (.drop place' target' cleanup') := by
                                    simpa [hterm] using ht0
                                  have htrace :
                                      { state := suffixTrace.state,
                                        events := firstTrace.events ++ event :: suffixTrace.events } = trace := by
                                    simpa [ht, hr, hd] using h
                                  rw [← htrace]
                                  exact ProgramSteps.drop hb hs ht hd hrest
              | resume => simp [hterm, terminatorStep] at h
              | unreachable => simp [hterm, terminatorStep] at h
              | unsupported kind => simp [hterm, terminatorStep] at h

theorem run_in_steps {program : Envelope} {trace : Trace}
    (h : run program = some trace) : ProgramInSteps program trace := by
  unfold run at h
  cases hfind : program.bodies.find? (·.instanceId == program.entry) with
  | none => simp [hfind] at h
  | some body =>
      simp [hfind] at h
      exact ⟨body, hfind, cfgRunProgram_in_steps h⟩

def InSteps : List Statement → State → State → List Event → Prop
  | [], initial, final, events => final = initial ∧ events = []
  | statement :: rest, initial, final, events =>
      ∃ middle event tail,
        Step initial statement middle event ∧ InSteps rest middle final tail ∧ events = event :: tail

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
