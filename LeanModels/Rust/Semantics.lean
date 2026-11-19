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
  pointeeType : Option Nat := none
  isLocal : Bool := true
  targetFrame : Option Nat := none
  projection : List Projection := []
deriving Repr, Inhabited, BEq, DecidableEq

inductive Cell where
  | int (n : Int)
  | pointer (p : Pointer)
  | aggregate (fields : List Cell)
  | enum (variant : Nat) (fields : List Cell)
  | bytes (values : List Nat)
  | unit
deriving Repr, Inhabited, BEq

inductive Slot where
  | uninit
  | value (n : Int)
  | cell (value : Cell)
deriving Repr, Inhabited, BEq

structure State where
  locals : List (Nat × Slot) := []
  sharedLocals : List (Nat × Nat × Slot) := []
  frameId : Nat := 0
  localTypes : List (Nat × Nat) := []
  placements : List (Nat × Nat) := []
  types : List TypeLayout := []
  allocations : List Allocation := []
  provenance : List (Nat × Nat) := []
deriving Repr, Inhabited, BEq

inductive Event where
  | storageLive (localId : Nat)
  | storageDead (localId : Nat)
  | assign (localId : Nat) (value : Int)
  | assignOpaque (localId : Nat)
  | placeMention (localId : Nat)
  | call (callee : String)
  | drop (localId : Nat)
deriving Repr, Inhabited, BEq

structure Trace where
  state : State
  events : List Event
deriving Repr, Inhabited, BEq

inductive Refusal where
  | unsupported (what : String)
  | malformed (what : String)
deriving Repr, Inhabited, BEq

inductive Outcome where
  | returned (trace : Trace)
  | panicked
  | ub (kind : String)
  | refused (reason : Refusal)
  | outOfFuel
deriving Repr, Inhabited, BEq

inductive CheckedOutcome where
  | value (n : Int)
  | overflow
  | divideByZero
deriving Repr, Inhabited, BEq

def Outcome.isReturned : Outcome → Bool
  | .returned _ => true
  | _ => false

def Refusal.label : Refusal → String
  | .unsupported what => "unsupported:" ++ what
  | .malformed what => "malformed:" ++ what

def Outcome.label : Outcome → String
  | .returned _ => "returned"
  | .panicked => "panicked"
  | .ub kind => "ub:" ++ kind
  | .refused reason => "refused:" ++ reason.label
  | .outOfFuel => "out_of_fuel"

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

def checkedMul32 (left right : Int) : CheckedOutcome :=
  let result := left * right
  if result < -(2 ^ 31) ∨ result > 2 ^ 31 - 1 then .overflow else .value result

def checkedBinaryOutcome (op : String) (left right : Int) : CheckedOutcome :=
  match op with
  | "Sub" => checkedSub32 left right
  | "Add" => checkedAdd32 left right
  | "Mul" => checkedMul32 left right
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

def cellSlot : Cell → Slot
  | .int value => .value value
  | value => .cell value

def shareCell (frameId : Nat) : Cell → Cell
  | .pointer pointer =>
      if pointer.isLocal then
        .pointer { pointer with isLocal := false, targetFrame := some frameId }
      else .pointer pointer
  | .aggregate fields => .aggregate (fields.map (shareCell frameId))
  | .enum variant fields => .enum variant (fields.map (shareCell frameId))
  | value => value

def normalizeAbiCell : Cell → Cell
  | .aggregate [.pointer pointer] => .pointer pointer
  | .aggregate fields => .aggregate (fields.map normalizeAbiCell)
  | .enum variant fields => .enum variant (fields.map normalizeAbiCell)
  | value => value

def localSlot (s : State) (localId : Nat) : Option Slot :=
  s.locals.find? (fun item => item.1 == localId) |>.map (·.2)

def localType (s : State) (localId : Nat) : Option Nat :=
  s.localTypes.find? (fun item => item.1 == localId) |>.map (·.2)

def sharedSlot (s : State) (frameId localId : Nat) : Option Slot :=
  s.sharedLocals.find? (fun item => item.1 == frameId && item.2.1 == localId) |>.map (·.2.2)

def sharedSlotsFrom (frameId : Nat) : List (Nat × Slot) → List (Nat × Nat × Slot)
  | [] => []
  | (localId, slot) :: rest => (frameId, localId, slot) :: sharedSlotsFrom frameId rest

def typedBytesValue (s : State) (ty : Nat) (bytes : List Nat) : Option Int :=
  let layout := s.types.find? (fun item => item.id == toString ty)
  match layout with
  | none => if s.types.isEmpty then bytesValue bytes else none
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

def allocationCell (s : State) (provenance : Nat) (pointeeType : Option Nat) : Option Cell :=
  match s.allocations.drop provenance |>.head? with
  | some allocation =>
      if allocation.bytesValid then
        match pointeeType with
        | some ty => typedBytesValue s ty allocation.bytes |>.map Cell.int
        | none => none
      else none
  | none => none

def resolveProvenance (s : State) (raw : Nat) : Nat :=
  (s.provenance.find? (fun item => item.1 == raw)).map (·.2) |>.getD raw

def projectFields (s : State) (cell : Cell) : List Projection → Option Cell
  | [] => some cell
  | .field index _ :: rest =>
      match cell with
      | .aggregate fields =>
          fields.drop index |>.head? |>.bind (projectFields s · rest)
      | .enum _ fields =>
          fields.drop index |>.head? |>.bind (projectFields s · rest)
      | _ => none
  | .downcast variant :: rest =>
      match cell with
      | .enum actual _ => if actual == variant then projectFields s cell rest else none
      | _ => none
  | .deref :: _ | .unsupported _ :: _ => none

def projectCell (s : State) (cell : Cell) : List Projection → Option Cell
  | [] => some cell
  | .deref :: rest =>
      match cell with
      | .aggregate [inner] => projectCell s inner (.deref :: rest)
      | .pointer pointer =>
          let target :=
            if pointer.isLocal then
              ((localSlot s pointer.provenance).orElse (fun _ => sharedSlot s s.frameId pointer.provenance)).bind slotCell |>.bind
                (projectFields s · pointer.projection)
            else
              match pointer.targetFrame with
              | some frameId => match sharedSlot s frameId pointer.provenance with
                | some slot => slotCell slot |>.bind (projectFields s · pointer.projection)
                | none => none
              | none => match pointer.pointeeType with
                | some ty => allocationCell s pointer.provenance (some ty)
                | none => allocationCell s pointer.provenance none
          target.bind (projectCell s · rest)
      | _ => none
  | .field index _ :: rest =>
      match cell with
      | .pointer pointer =>
          let target :=
            if pointer.isLocal then ((localSlot s pointer.provenance).orElse (fun _ => sharedSlot s s.frameId pointer.provenance)).bind slotCell
            else match pointer.targetFrame with
              | some frameId => (sharedSlot s frameId pointer.provenance).bind slotCell
              | none => match pointer.pointeeType with
                | some ty => allocationCell s pointer.provenance (some ty)
                | none => allocationCell s pointer.provenance none
          target.bind (projectFields s · (.field index 0 :: rest))
      | .aggregate fields =>
          fields.drop index |>.head? |>.bind (projectCell s · rest)
      | .enum _ fields =>
          fields.drop index |>.head? |>.bind (projectCell s · rest)
      | _ => none
  | .downcast variant :: rest =>
      match cell with
      | .enum actual _ => if actual == variant then projectCell s cell rest else none
      | _ => none
  | .unsupported _ :: _ => none

def readCell (s : State) (place : Place) : Option Cell :=
  localSlot s place.localId |>.bind slotCell |>.bind (projectCell s · place.projection)

def updateCellProjection : Cell → List Projection → Cell → Option Cell
  | cell, [], value => some value
  | .aggregate fields, .field index _ :: rest, value => do
      let old ← fields.drop index |>.head?
      let updated ← updateCellProjection old rest value
      pure (.aggregate (fields.set index updated))
  | .enum variant fields, .field index _ :: rest, value => do
      let old ← fields.drop index |>.head?
      let updated ← updateCellProjection old rest value
      pure (.enum variant (fields.set index updated))
  | .enum variant fields, .downcast expected :: rest, value =>
      if variant == expected then updateCellProjection (.enum variant fields) rest value else none
  | _, .field _ _ :: _, _ | _, .downcast _ :: _, _ => none
  | _, .deref :: _ , _ | _, .unsupported _ :: _, _ => none

def writeLocalProjection (s : State) (localId : Nat) : List Projection → Cell → Option State
  | [], value => some (setSlot s localId (cellSlot value))
  | projections, value => do
      let cell ← localSlot s localId |>.bind slotCell
      let updated ← updateCellProjection cell projections value
      pure (setSlot s localId (cellSlot updated))

def writeCell (s : State) (place : Place) (value : Cell) : Option State :=
  match place.projection with
  | [] => some (setSlot s place.localId (cellSlot value))
  | .deref :: rest =>
      localSlot s place.localId |>.bind slotCell |>.bind fun cell =>
        match cell with
        | .pointer pointer =>
            if pointer.isLocal then
              if pointer.projection.isEmpty then
                writeLocalProjection s pointer.provenance rest value
              else none
            else do
              let frameId ← pointer.targetFrame
              let slot ← sharedSlot s frameId pointer.provenance
              let cell ← slotCell slot
              let updated ← updateCellProjection cell (pointer.projection ++ rest) value
              pure { s with sharedLocals :=
                (frameId, pointer.provenance, cellSlot updated) ::
                  s.sharedLocals.filter (fun item =>
                    !(item.1 == frameId && item.2.1 == pointer.provenance)) }
        | _ => none
  | .field index _ :: rest => writeLocalProjection s place.localId (.field index 0 :: rest) value
  | .downcast _ :: _ | .unsupported _ :: _ => none

def castInt (s : State) (target : Nat) (value : Int) : Option Int :=
  match s.types.find? (fun item => item.id == toString target) with
  | some info =>
      if !(info.kind.startsWith "RigidTy(Int(") &&
          !(info.kind.startsWith "RigidTy(Uint(") then none else
        match info.sizeBits, info.signed with
        | some width, some signed =>
            if width == 0 then none
            else if width ≤ 64 then
              let modulus := (2 : Int) ^ width
              let raw := value % modulus
              if signed && raw ≥ 2 ^ (width - 1) then
                some (raw - modulus)
              else some raw
            else none
        | _, _ => none
  | none => none

def pointerType (s : State) (target : Nat) : Bool :=
  match s.types.find? (fun item => item.id == toString target) with
  | some info => info.kind.startsWith "RigidTy(RawPtr" || info.kind.startsWith "RigidTy(Ref" ||
      info.kind.startsWith "RigidTy(FnPtr"
  | none => false

def operandCell (s : State) : Operand → Option Cell
  | .constant _ bytes ty provenance zeroSized =>
      if zeroSized then some (.int 0) else
      match s.types.find? (fun item => item.id == toString ty), provenance with
      | some info, some target =>
          if info.kind.startsWith "RigidTy(RawPtr" || info.kind.startsWith "RigidTy(Ref" ||
              info.kind.startsWith "RigidTy(FnPtr" then
            let resolved := resolveProvenance s target
            some (.pointer { provenance := resolved, address := placementOf s resolved, pointeeType := info.pointee, isLocal := false })
          else match typedBytesValue s ty bytes with
            | some value => some (.int value)
            | none => if bytes.all (· ≤ 255) then some (.bytes bytes) else none
      | _, _ => match typedBytesValue s ty bytes with
          | some value => some (.int value)
          | none => if bytes.all (· ≤ 255) then some (.bytes bytes) else none
  | .copy place | .move place =>
      readCell s place
  | .unsupported _ => none

def operandValue (s : State) (operand : Operand) : Option Int :=
  operandCell s operand |>.bind cellInt

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
  | .binaryLe left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (.int (if leftValue ≤ rightValue then 1 else 0))
  | .binaryLt left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (.int (if leftValue < rightValue then 1 else 0))
  | .binaryBitAnd left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (.int (Int.ofNat (leftValue.toNat &&& rightValue.toNat)))
  | .binaryBitXor left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      pure (.int (Int.ofNat (leftValue.toNat ^^^ rightValue.toNat)))
  | .binaryDiv left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      if rightValue == 0 then none else pure (.int (leftValue / rightValue))
  | .binaryRem left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      if rightValue == 0 then none else pure (.int (leftValue % rightValue))
  | .cast .intToInt operand target => do
      let value ← operandValue s operand
      let casted ← castInt s target value
      pure (.int casted)
  | .cast .ptrToPtr operand target => do
      if !pointerType s target then none else
        match ← operandCell s operand with
        | .pointer pointer => pure (.pointer pointer)
        | _ => none
  | .cast .transmute operand _target => operandCell s operand
  | .cast (.pointerCoercion _) operand _target => operandCell s operand
  | .cast .pointerWithExposedProvenance operand _target => operandCell s operand
  | .cast _ _ _ => none
  | .checkedBinary op left right => do
      let leftValue ← operandValue s left
      let rightValue ← operandValue s right
      match checkedBinaryOutcome op leftValue rightValue with
      | .value value => pure (.aggregate [.int value, .int 0])
      | .overflow => pure (.aggregate [.int 0, .int 1])
      | .divideByZero => none
  | .ref place =>
      match place.projection with
      | [] => some (.pointer { provenance := place.localId, address := placementOf s place.localId, pointeeType := localType s place.localId })
      | .deref :: rest =>
          match localSlot s place.localId |>.bind slotCell with
          | some (.pointer pointer) =>
              if pointer.projection.isEmpty then
                some (.pointer { pointer with projection := rest })
              else none
          | _ => none
      | projection =>
          some (.pointer { provenance := place.localId, address := placementOf s place.localId, pointeeType := localType s place.localId, projection := projection })
  | .addressOf _ place =>
      some (.pointer { provenance := place.localId, address := placementOf s place.localId, projection := place.projection })
  | .aggregate _ fields => do
      let values ← fields.mapM (operandCell s)
      pure (.aggregate values)
  | .adtAggregate variant fields => do
      let values ← fields.mapM (operandCell s)
      pure (.enum variant values)
  | .repeat operand count => do
      let value ← operandCell s operand
      pure (.aggregate (List.replicate count value))
  | .zstAggregate => some (.enum 0 [])
  | .discriminant place =>
      match readCell s place with
      | some (.enum variant _) => some (.int variant)
      | _ => none
  | .unsupported _ => none

def rvalueValue (s : State) (value : Rvalue) : Option Int :=
  (rvalueCell s value).bind cellInt

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
  | .assert cond expected target _cleanup => do
      let value ← operandValue s cond
      if value == (if expected then 1 else 0) then some (.jump target) else none
  | .drop place target cleanup =>
      if place.projection.isEmpty then some (.drop place target cleanup) else none
  | .call _ _ _ _ _ | .resume | .unreachable | .unsupported _ => none

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

def statementFailure : State → List Statement → Outcome
  | _, [] => .refused (.unsupported "statement execution")
  | state, statement :: rest =>
      match statementStep state statement with
      | some (state', _) => statementFailure state' rest
      | none =>
          match statement with
          | .assign _ (.binaryDiv _ right) | .assign _ (.binaryRem _ right) =>
              if operandValue state right == some 0 then .panicked
              else .refused (.unsupported "binary arithmetic")
          | .assign _ (.checkedBinary op left right) =>
              match operandValue state left, operandValue state right with
              | some leftValue, some rightValue =>
                  match checkedBinaryOutcome op leftValue rightValue with
                  | .divideByZero => .panicked
                  | .overflow | .value _ => .refused (.unsupported "checked arithmetic")
              | _, _ => .refused (.unsupported "checked arithmetic operands")
          | .assign _ (.ref _ ) => .refused (.unsupported "reference write")
          | .assign _ (.addressOf _ _) => .refused (.unsupported "address-of write")
          | .assign _ (.aggregate _ _) => .refused (.unsupported "aggregate write")
          | .assign _ (.repeat _ _) => .refused (.unsupported "repeat write")
          | .assign _ (.cast _ _ _) => .refused (.unsupported "cast write")
          | .assign place (.use operand) =>
              match rvalueCell state (.use operand) with
              | none => .refused (.unsupported "use operand")
              | some cell =>
                  if (writeCell state place cell).isNone then
                    .refused (.unsupported ("use destination local " ++ toString place.localId))
                  else .refused (.unsupported "use assignment")
          | .assign _ (.binaryNe _ _) => .refused (.unsupported "inequality assignment")
          | .assign _ (.binaryLe _ _) => .refused (.unsupported "less-equal assignment")
          | .assign _ (.binaryLt _ _) => .refused (.unsupported "less-than assignment")
          | .assign _ (.binaryEq _ _) => .refused (.unsupported "equality assignment")
          | .assign _ (.binaryBitAnd _ _) => .refused (.unsupported "bitwise assignment")
          | .assign _ (.binaryBitXor _ _) => .refused (.unsupported "bitwise-xor assignment")
          | .assign _ (.zstAggregate) => .refused (.unsupported "zst aggregate assignment")
          | .assign _ (.adtAggregate _ _) => .refused (.unsupported "adt aggregate assignment")
          | .assign _ (.discriminant _) => .refused (.unsupported "discriminant assignment")
          | .assign _ (.unsupported kind) => .refused (.unsupported ("assignment " ++ kind))
          | .placeMention _ => .refused (.unsupported "place mention")
          | .storageLive _ | .storageDead _ | .unsupported _ =>
              .refused (.unsupported "statement")

def statementFailureAt (bodyId : String) (blockId : Nat) (state : State)
    (statements : List Statement) : Outcome :=
  match statementFailure state statements with
  | .refused (.unsupported what) =>
      .refused (.unsupported (what ++ " at " ++ bodyId ++ ":b" ++ toString blockId))
  | outcome => outcome

def cfgRunOutcome : Nat → Body → Nat → State → Outcome
  | 0, _, _, _ => .outOfFuel
  | fuel + 1, body, blockId, state =>
      match blockAt body.blocks blockId with
      | none => .refused (.malformed "missing block")
      | some block =>
          match statementsRun block.statements state with
          | none => statementFailureAt body.instanceId blockId state block.statements
          | some firstTrace =>
              match block.terminator with
              | .ret => .returned firstTrace
              | .goto target => cfgRunOutcome fuel body target firstTrace.state
              | .switchInt discr branches otherwise =>
                  match terminatorStep firstTrace.state block.terminator with
                  | some (.jump target) => cfgRunOutcome fuel body target firstTrace.state
                  | _ => .refused (.unsupported "switch operand")
              | .assert cond expected target cleanup =>
                  match operandValue firstTrace.state cond with
                  | none => .refused (.unsupported "assert condition")
                  | some value =>
                      if value == (if expected then 1 else 0) then
                        cfgRunOutcome fuel body target firstTrace.state
                      else match cleanup with
                        | some cleanupTarget => cfgRunOutcome fuel body cleanupTarget firstTrace.state
                        | none => .panicked
              | .drop place target cleanup =>
                  match dropState firstTrace.state place with
                  | none => .refused (.unsupported "drop projection")
                  | some (dropState', _) => cfgRunOutcome fuel body target dropState'
              | .resume => .panicked
              | .unreachable => .ub "unreachable"
              | .call _ _ _ _ _ | .unsupported _ => .refused (.unsupported "terminator")

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

def bindCallCells : State → List Operand → Nat → Option State
  | state, [], _ => some state
  | state, operand :: rest, localId => do
      let value ← operandCell state operand
      bindCallCells (setSlot state localId (cellSlot value)) rest (localId + 1)

def bindEvaluatedCells : State → List Cell → Nat → State
  | state, [], _ => state
  | state, value :: rest, localId =>
      bindEvaluatedCells (setSlot state localId (cellSlot value)) rest (localId + 1)

def bindCallCellsFresh (caller callee : State) (args : List Operand) (localId : Nat) : Option State := do
  let values ← args.mapM (operandCell caller)
  let frameState := { callee with frameId := caller.frameId + 1 }
  let sharedState := { frameState with
    localTypes := callee.localTypes,
    sharedLocals := sharedSlotsFrom caller.frameId caller.locals ++ caller.sharedLocals }
  pure (bindEvaluatedCells
    sharedState
    (values.map (fun value => normalizeAbiCell (shareCell caller.frameId value))) localId)

def returnValue (trace : Trace) : Option Int :=
  (trace.state.locals.find? (fun item => item.1 == 0)).bind fun item =>
    match item.2 with
    | .value value => some value
    | .cell (.int value) => some value
    | .cell _ => none
    | .uninit => none

def returnCell (trace : Trace) : Option Cell :=
  (trace.state.locals.find? (fun item => item.1 == 0)).bind fun item => slotCell item.2

def cfgRunProgram : Nat → Envelope → Body → Nat → State → Option Trace
  | 0, _, _, _, _ => none
  | fuel + 1, program, body, blockId, state => do
      let block ← blockAt body.blocks blockId
      let firstTrace ← statementsRun block.statements state
      match block.terminator with
      | .call _ args destination (some target) _cleanup => do
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
      | .call _ _ _ none _cleanup => none
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

def cfgRunProgramOutcome : Nat → Envelope → Body → Nat → State → Outcome
  | 0, _, _, _, _ => .outOfFuel
  | fuel + 1, program, body, blockId, state =>
      match blockAt body.blocks blockId with
      | none => .refused (.malformed "missing block")
      | some block =>
          match statementsRun block.statements state with
          | none => statementFailureAt body.instanceId blockId state block.statements
          | some firstTrace =>
              match block.terminator with
              | .call _ args destination (some target) cleanup =>
                  match lookupCallBody program body blockId with
                  | none => .refused (.unsupported "unresolved call")
                  | some (edge, callee) =>
                      match edge.callee with
                      | none => .refused (.unsupported "call without callee")
                      | some calleeId =>
                          let callState : State :=
                            { placements := firstTrace.state.placements,
                              sharedLocals := firstTrace.state.sharedLocals,
                              types := firstTrace.state.types,
                              allocations := firstTrace.state.allocations,
                              provenance := firstTrace.state.provenance,
                              localTypes := callee.locals.map (fun loc => (loc.localId, loc.ty)) }
                          match bindCallCellsFresh firstTrace.state callState args 1 with
                          | none => .refused (.unsupported ("call arguments for " ++ calleeId))
                          | some calleeState =>
                              match cfgRunProgramOutcome fuel program callee 0 calleeState with
                              | .returned calleeTrace =>
                                  match returnCell calleeTrace with
                                  | none => .refused (.unsupported "callee return value")
                                  | some value =>
                                      match writeCell firstTrace.state destination value with
                                      | none => .refused (.unsupported "call destination")
                                      | some callerState =>
                                          match cfgRunProgramOutcome fuel program body target callerState with
                                          | .returned suffixTrace =>
                                              let combined : Trace :=
                                                { state := suffixTrace.state,
                                                  events := firstTrace.events ++
                                                    (Event.call calleeId ::
                                                      (calleeTrace.events ++ suffixTrace.events)) }
                                              .returned combined
                                          | outcome => outcome
                              | .panicked =>
                                  match cleanup with
                                  | some cleanupTarget =>
                                      cfgRunProgramOutcome fuel program body cleanupTarget firstTrace.state
                                  | none => .panicked
                              | outcome => outcome
              | .call _ args _ none _cleanup =>
                  match lookupCallBody program body blockId with
                  | none => .refused (.unsupported "unresolved diverging call")
                  | some (edge, callee) =>
                      match edge.callee with
                      | none => .refused (.unsupported "diverging call without callee")
                      | some calleeId =>
                          let callState : State :=
                            { placements := firstTrace.state.placements,
                              sharedLocals := firstTrace.state.sharedLocals,
                              types := firstTrace.state.types,
                              allocations := firstTrace.state.allocations,
                              provenance := firstTrace.state.provenance,
                              localTypes := callee.locals.map (fun loc => (loc.localId, loc.ty)) }
                          match bindCallCellsFresh firstTrace.state callState args 1 with
                          | none => .refused (.unsupported ("diverging call arguments for " ++ calleeId))
                          | some calleeState =>
                              match cfgRunProgramOutcome fuel program callee 0 calleeState with
                              | .returned _ => .refused (.malformed "diverging call returned")
                              | outcome => outcome
              | .ret => .returned firstTrace
              | .goto target => cfgRunProgramOutcome fuel program body target firstTrace.state
              | .switchInt _ _ _ =>
                  match terminatorStep firstTrace.state block.terminator with
                  | some (.jump target) => cfgRunProgramOutcome fuel program body target firstTrace.state
                  | _ => .refused (.unsupported "switch operand")
              | .assert cond expected target cleanup =>
                  match operandValue firstTrace.state cond with
                  | none => .refused (.unsupported "assert condition")
                  | some value =>
                      if value == (if expected then 1 else 0) then
                        cfgRunProgramOutcome fuel program body target firstTrace.state
                      else match cleanup with
                        | some cleanupTarget =>
                            cfgRunProgramOutcome fuel program body cleanupTarget firstTrace.state
                        | none => .panicked
              | .drop place target _ =>
                  match dropState firstTrace.state place with
                  | none => .refused (.unsupported "drop projection")
                  | some (dropState', _) => cfgRunProgramOutcome fuel program body target dropState'
              | .resume => .panicked
              | .unreachable => .ub "unreachable"
              | .unsupported _ => .refused (.unsupported "terminator")

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
      {cleanup : Option Nat}
      {edge : CallEdge} {calleeId : String} {callee : Body} {value : Int}
      (hb : blockAt body.blocks blockId = some block)
      (hs : statementsRun block.statements state = some first)
      (ht : block.terminator = .call func args destination (some target) cleanup)
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
    (allocations : List Allocation := []) (provenance : List (Nat × Nat) := []) : State :=
  { locals := [], placements := allocationPlacements placement allocations,
    types := types, allocations := allocations, provenance := provenance }

def runWithPlacement (placement : Nat → Nat) (program : Envelope) : Option Trace :=
  match program.bodies.find? (·.instanceId == program.entry) with
  | some body => cfgRunProgram 4096 program body 0
      { (initialState placement program.types program.allocations program.provenance) with
        localTypes := body.locals.map (fun loc => (loc.localId, loc.ty)) }
  | none => none

def runOutcome (program : Envelope) : Outcome :=
  match program.bodies.find? (·.instanceId == program.entry) with
  | some body => cfgRunProgramOutcome 4096 program body 0
      { (initialState (fun n => n) program.types program.allocations program.provenance) with
        localTypes := body.locals.map (fun loc => (loc.localId, loc.ty)) }
  | none => .refused (.malformed "missing entry body")

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
              | call func args destination target cleanup =>
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
              | assert cond expected target cleanup =>
                  simp [hterm] at h
                  generalize ht0 : terminatorStep firstTrace.state
                      (Terminator.assert cond expected target cleanup) = transition at h
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
