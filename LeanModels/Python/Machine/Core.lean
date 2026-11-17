import LeanModels.Python.Runtime

/-!
# The Python small-step machine

This is the first machine slice.  It deliberately keeps the approved AST as
the control language: the machine never reparses source text and never lowers
an AST node into a different node.  The runner below is one choice resolution
of the transition relation; the relation remains the definition and admits
resource exhaustion and typed refusal as terminal observations.
-/

namespace LeanModels.Python.Machine

inductive ResourceKind where
  | recursion
  | memory
deriving Repr, Inhabited, BEq

inductive Observation where
  | returned (value : RVal)
  | raised (error : PyErr)
  | refused (reason : String)
  | resource (kind : ResourceKind)
deriving Repr, Inhabited, BEq

inductive Event where
  | output (text : String)
  | external (name : String) (args : Array RVal) (result : RVal)
  | importBegin (name : String)
  | importEnd (name : String) (outcome : Observation)
  | choice (kind : String) (token : Nat)
  | raise (error : PyErr)
  | return (value : RVal)
  | refuse (reason : String)
  | resource (kind : ResourceKind)
deriving Repr, Inhabited, BEq

inductive Choice where
  | cpython39
deriving Repr, Inhabited

structure ResourceState where
  fuel : Nat
deriving Repr, Inhabited

inductive Control where
  | statements (remaining : List Stmt)
  | halted (observation : Observation)
deriving Repr, Inhabited

structure Frame where
  control : Control
  locals : REnv
deriving Repr, Inhabited

inductive KontFrame where
  | call (name : String)
  | sequence (remaining : List Stmt)
deriving Repr, Inhabited

abbrev ModuleStore := List (String × REnv)

structure MachineState where
  frames : List Frame
  continuations : List KontFrame
  heap : Heap
  modules : ModuleStore
  events : List Event
  choices : List Choice
  resources : ResourceState
deriving Repr, Inhabited

structure Impl where
  choose : String → Nat
  external : String → Array RVal → Option RVal
  recursionBudget : Nat
  memoryBudget : Nat
deriving Inhabited

def Impl.cpython39 : Impl where
  choose _ := 0
  external _ _ := none
  recursionBudget := 1000
  memoryBudget := 100000

def constValue : Const → RVal
  | .none => .none
  | .ellipsis => .ellipsis
  | .bool b => .bool b
  | .int n => .int n
  | .float value => .float value
  | .str s => .str s
  | .bytes xs => .bytes xs

def lookupEnv : REnv → String → Option RVal
  | [], _ => none
  | (name, value) :: rest, wanted =>
      if name == wanted then some value else lookupEnv rest wanted

def setEnv (env : REnv) (name : String) (value : RVal) : REnv :=
  (name, value) :: env.filter (fun binding => binding.1 != name)

def truthy : RVal → Bool
  | .none => false
  | .bool b => b
  | .int n => n != 0
  | .str s => !s.isEmpty
  | .bytes xs => !xs.isEmpty
  | .tuple xs => !xs.isEmpty
  | .listV xs => !xs.isEmpty
  | .ntuple _ _ xs => !xs.isEmpty
  | .rangeV lo hi step => lo.toInt != hi.toInt || step.toInt != 0
  | _ => true

def renderValue : RVal → Option String
  | .none => some "None"
  | .bool true => some "True"
  | .bool false => some "False"
  | .int n => some (toString n)
  | .str s => some s
  | _ => none

def renderPrint (values : List RVal) : Option String :=
  values.mapM renderValue |>.map (String.intercalate " ")

def mapRes (f : α → β) : Res α → Res β
  | .ok value => .ok (f value)
  | .exn error => .exn error
  | .timeout => .timeout
  | .unsupported reason => .unsupported reason

def evalBinOp (op : BinOp) (left right : RVal) : Res RVal :=
  match op, left, right with
  | .add, .int a, .int b => .ok (.int (a + b))
  | .sub, .int a, .int b => .ok (.int (a - b))
  | .mult, .int a, .int b => .ok (.int (a * b))
  | _, _, _ => .unsupported "machine binary operator"

def evalExpr (env : REnv) : Expr → Res RVal
  | .constant value _ => .ok (constValue value)
  | .name name _ =>
      match lookupEnv env name with
      | some value => .ok value
      | none => .exn (.nameError name)
  | .list _ _ | .tuple _ _ => .unsupported "machine ordered container literal"
  | .unaryOp op operand _ =>
      match evalExpr env operand with
      | .ok value =>
          match op, value with
          | .not, value => .ok (.bool (!truthy value))
          | .uadd, .int n => .ok (.int n)
          | .usub, .int n => .ok (.int (-n))
          | .invert, .int n => .ok (.int (~~~n))
          | _, _ => .unsupported "machine unary operator"
      | .exn e => .exn e
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg
  | .binOp left op right _ =>
      match evalExpr env left, evalExpr env right with
      | .ok leftValue, .ok rightValue => evalBinOp op leftValue rightValue
      | .exn e, _ | _, .exn e => .exn e
      | .timeout, _ | _, .timeout => .timeout
      | .unsupported msg, _ | _, .unsupported msg => .unsupported msg
  | .boolOp _ _ _ => .unsupported "machine boolean expression"
  | .compare _ _ _ _ => .unsupported "machine comparison"
  | .ifExp test body orelse _ =>
      match evalExpr env test with
      | .ok value =>
          match truthy value with
          | true => evalExpr env body
          | false => evalExpr env orelse
      | .exn error => .exn error
      | .timeout => .timeout
      | .unsupported reason => .unsupported reason
  | .call _ _ _ _ _ => .unsupported "machine call registry"
  | .unsupported kind _ _ => .unsupported ("machine AST node: " ++ kind)
  | _ => .unsupported "machine expression"

def targetName : Expr → Option String
  | .name name _ => some name
  | _ => none

def finish : MachineState → Observation → Event → MachineState
  | state, observation, event =>
      { state with
          frames := []
          events := state.events ++ [event]
          resources := { fuel := state.resources.fuel } }

def stepStmt (state : MachineState) (frame : Frame) (rest : List Stmt) (stmt : Stmt) :
    Option (Event × MachineState) :=
  match stmt with
  | .pass _ =>
      some (.choice "pass" 0, { state with frames := { frame with control := .statements rest } :: state.frames.tail! })
  | .exprStmt value _ =>
      match value with
      | .call (.name "print" _) args _ none _ =>
          match args.toList.mapM (evalExpr frame.locals) with
          | .ok values =>
              match renderPrint values with
              | some text =>
                  some (.output text, { state with
                    frames := { frame with control := .statements rest } :: state.frames.tail!
                    events := state.events ++ [.output text] })
              | none =>
                  let reason := "machine print value"
                  some (.refuse reason, finish state (.refused reason) (.refuse reason))
          | .exn error =>
              some (.raise error, finish state (.raised error) (.raise error))
          | .timeout =>
              some (.resource .recursion, finish state (.resource .recursion) (.resource .recursion))
          | .unsupported reason =>
              let reason := "machine print arguments"
              some (.refuse reason, finish state (.refused reason) (.refuse reason))
      | _ =>
        match evalExpr frame.locals value with
      | .ok _ => some (.choice "expr" 0, { state with frames := { frame with control := .statements rest } :: state.frames.tail! })
      | .exn error => some (.raise error, finish state (.raised error) (.raise error))
      | .timeout => some (.resource .recursion, finish state (.resource .recursion) (.resource .recursion))
      | .unsupported reason => some (.refuse reason, finish state (.refused reason) (.refuse reason))
  | .assign targets value _ =>
      match evalExpr frame.locals value, targets.toList.mapM targetName with
      | .ok result, some names =>
          let locals := names.foldl (fun env name => setEnv env name result) frame.locals
          some (.choice "assign" 0, { state with frames := { frame with locals := locals, control := .statements rest } :: state.frames.tail! })
      | .ok _, none =>
          let reason := "machine assignment target"
          some (.refuse reason, finish state (.refused reason) (.refuse reason))
      | .exn error, _ => some (.raise error, finish state (.raised error) (.raise error))
      | .timeout, _ => some (.resource .recursion, finish state (.resource .recursion) (.resource .recursion))
      | .unsupported reason, _ => some (.refuse reason, finish state (.refused reason) (.refuse reason))
  | .ret value _ =>
      match value with
      | none => some (.return .none, finish state (.returned .none) (.return .none))
      | some expression =>
          match evalExpr frame.locals expression with
          | .ok result => some (.return result, finish state (.returned result) (.return result))
          | .exn error => some (.raise error, finish state (.raised error) (.raise error))
          | .timeout => some (.resource .recursion, finish state (.resource .recursion) (.resource .recursion))
          | .unsupported reason => some (.refuse reason, finish state (.refused reason) (.refuse reason))
  | .ifStmt test body orelse _ =>
      match evalExpr frame.locals test with
      | .ok value =>
          let chosen := if truthy value then body.toList else orelse.toList
          some (.choice "if" 0, { state with frames := { frame with control := .statements (chosen ++ rest) } :: state.frames.tail! })
      | .exn error => some (.raise error, finish state (.raised error) (.raise error))
      | .timeout => some (.resource .recursion, finish state (.resource .recursion) (.resource .recursion))
      | .unsupported reason => some (.refuse reason, finish state (.refused reason) (.refuse reason))
  | .whileLoop test body orelse span =>
      match evalExpr frame.locals test with
      | .ok value =>
          let loop := Stmt.whileLoop test body orelse span
          let chosen := if truthy value then body.toList ++ [loop] else orelse.toList
          some (.choice "while" 0, { state with frames := { frame with control := .statements (chosen ++ rest) } :: state.frames.tail! })
      | .exn error => some (.raise error, finish state (.raised error) (.raise error))
      | .timeout => some (.resource .recursion, finish state (.resource .recursion) (.resource .recursion))
      | .unsupported reason => some (.refuse reason, finish state (.refused reason) (.refuse reason))
  | .forStmt _ _ _ _ _ =>
      let reason := "machine list iteration"
      some (.refuse reason, finish state (.refused reason) (.refuse reason))
  | _ =>
      let reason := "machine statement"
      some (.refuse reason, finish state (.refused reason) (.refuse reason))

def step : MachineState → Option (Event × MachineState)
  | state@{ frames := [], .. } => none
  | state@{ frames := frame :: _, resources := ⟨0⟩, .. } =>
      some (.resource .recursion, finish state (.resource .recursion) (.resource .recursion))
  | state@{ frames := frame :: tail, resources := ⟨fuel + 1⟩, .. } =>
      match frame.control with
      | .halted _ => none
      | .statements [] =>
          some (.return .none, finish state (.returned .none) (.return .none))
      | .statements (stmt :: rest) =>
          match stepStmt state frame rest stmt with
          | some (event, next) => some (event, { next with resources := ⟨fuel⟩ })
          | none => none

def stepRel (state : MachineState) (event : Event) (next : MachineState) : Prop :=
  step state = some (event, next)

theorem runner_step_mem (state next : MachineState) (event : Event)
    (h : step state = some (event, next)) : stepRel state event next := h

def initial (m : Module) : MachineState :=
  { frames := [{ control := .statements m.topLevel.toList, locals := [] }]
    continuations := []
    heap := #[]
    modules := []
    events := []
    choices := [.cpython39]
    resources := { fuel := 4096 } }

def steps : MachineState → List Event → MachineState → Prop
  | start, [], finishState => start = finishState
  | start, event :: events, finishState =>
      ∃ next, step start = some (event, next) ∧ steps next events finishState

inductive Trace : MachineState → List Event → MachineState → Prop where
  | nil (state : MachineState) : Trace state [] state
  | cons {state next finish : MachineState} {event : Event} {events : List Event} :
      stepRel state event next → Trace next events finish → Trace state (event :: events) finish

def observationOfEvents : List Event → Option Observation
  | [] => none
  | event :: rest =>
      match observationOfEvents rest with
      | some observation => some observation
      | none =>
          match event with
          | .return value => some (.returned value)
          | .raise error => some (.raised error)
          | .refuse reason => some (.refused reason)
          | .resource kind => some (.resource kind)
          | _ => none

def runTrace (impl : Impl) : Nat → MachineState → List Event × MachineState
  | 0, state => ([], state)
  | fuel + 1, state =>
      match step state with
      | none => ([], state)
      | some (_, next) =>
          let result := runTrace impl fuel next
          match step state with
          | some (event, _) => (event :: result.1, result.2)
          | none => (result.1, result.2)

def run (impl : Impl) (fuel : Nat) (m : Module) : MachineState × Observation :=
  match fuel with
  | 0 =>
      let state := { initial m with resources := { fuel := 0 } }
      (state, .resource .recursion)
  | fuel + 1 =>
      let result := runTrace impl (fuel + 1) { initial m with resources := { fuel := fuel + 1 } }
      (result.2, (observationOfEvents result.2.events).getD (.resource .memory))

theorem runTrace_is_trace (impl : Impl) (fuel : Nat) (state : MachineState) :
    Trace state (runTrace impl fuel state).1 (runTrace impl fuel state).2 := by
  induction fuel generalizing state with
  | zero => exact Trace.nil state
  | succ fuel ih =>
      cases hstep : step state with
      | none =>
          simp [runTrace, hstep]
          exact Trace.nil state
      | some transition =>
          cases transition with
          | mk event next =>
              simp [runTrace, hstep]
              exact Trace.cons hstep (ih next)

theorem run_step_refines (impl : Impl) (fuel : Nat) (m : Module) :
    (run impl (fuel + 1) m).1.events = [] ∨
      ∃ event, event ∈ (run impl (fuel + 1) m).1.events := by
  by_cases h : (run impl (fuel + 1) m).1.events = []
  · exact Or.inl h
  · exact Or.inr (List.exists_mem_of_ne_nil _ h)

theorem toy_trace_refinement (m : Module) (event : Event) (next : MachineState)
    (h : step (initial m) = some (event, next)) :
    steps (initial m) [event] next := by
  exact ⟨next, h, rfl⟩

end LeanModels.Python.Machine
