import LeanModels.Python.Runtime

namespace LeanModels.Python.Machine

/-!
# Relational Python machine kernel

The machine consumes a small, node-for-node envelope of CPython's AST.  It is
separate from `Module`, the compatibility envelope used by the frozen
interpreters, which has already hoisted definitions and run ingestion passes.
The relation has no fuel, budget, implementation choice, or exception message
text in its configuration.  `runRelation` is an executable resolution of the
relation and its trace theorem is proved against `Step`.

This first kernel slice covers the control and expression-continuation shape.
Unsupported raw nodes are represented structurally and refuse as an event.
-/

structure RParam where
  name : String
  positionalOnly : Bool := false
  keywordOnly : Bool := false
  variadic : Bool := false
  defaults : Option (Array Expr) := none
deriving Repr, Inhabited, BEq

inductive RStmt where
  | pass (span : Span)
  | ret (value : Option Expr) (span : Span)
  | expr (value : Expr) (span : Span)
  | assign (target : Expr) (value : Expr) (span : Span)
  | ifStmt (test : Expr) (body : Array RStmt) (orelse : Array RStmt) (span : Span)
  | whileStmt (test : Expr) (body : Array RStmt) (orelse : Array RStmt) (span : Span)
  | functionDef (name : String) (params : Array RParam) (defaults : Array Expr)
      (body : Array RStmt) (span : Span)
  | classDef (name : String) (bases : Array Expr) (body : Array RStmt) (span : Span)
  | import (module : String) (alias : Option String) (span : Span)
  | unsupported (kind : String) (text : String) (span : Span)
deriving Repr, Inhabited, BEq

structure RFunction where
  name : String
  params : Array RParam
  body : Array RStmt
  globals : String
deriving Repr, Inhabited, BEq

structure RModule where
  body : Array RStmt
deriving Repr, Inhabited, BEq

inductive RResource where
  | recursion
  | memory
deriving Repr, Inhabited, BEq, DecidableEq

inductive RErrClass where
  | recursion
  | memory
  | name
  | type
  | runtime
deriving Repr, Inhabited, BEq, DecidableEq

structure RError where
  errorClass : RErrClass
  args : List RVal
deriving Repr, Inhabited, BEq

inductive REvent where
  | output (text : String)
  | raise (error : RError)
  | return (value : RVal)
  | refuse (reason : String)
  | choice (kind : String) (token : Nat)
deriving Repr, Inhabited, BEq

inductive RLabel where
  | tau
  | event (event : REvent)
deriving Repr, Inhabited, BEq

structure RChoice where
  kind : String
  allowed : List Nat
deriving Repr, Inhabited, BEq

inductive RResourcePoint where
  | framePush
  | allocation
deriving Repr, Inhabited, BEq

inductive RStatus where
  | running
  | finished (event : REvent)
deriving Repr, Inhabited, BEq

inductive RKont where
  | returnValue
  | printValue
  | discardValue
  | sequence (remaining : List RStmt)
  | assign (name : String) (remaining : List RStmt)
  | binOpLeft (op : BinOp) (right : Expr) (continuation : RKont)
  | binOpRight (left : RVal) (op : BinOp) (continuation : RKont)
deriving Repr, Inhabited, BEq

inductive RControl where
  | statements (remaining : List RStmt)
  | evaluate (expression : Expr) (continuation : RKont)
  | continueValue (value : RVal) (continuation : RKont)
  | raising (error : RError)
deriving Repr, Inhabited, BEq

structure RFrame where
  control : RControl
  locals : REnv
  globals : REnv
deriving Repr, Inhabited, BEq

structure RConfig where
  program : RModule
  frames : List RFrame
  heap : Heap
  modules : List (String × REnv)
  functions : List RFunction
  choices : List RChoice
  choiceToken : Option Nat
  status : RStatus
deriving Repr, Inhabited, BEq

def RConfig.initial (program : RModule) : RConfig :=
  { program := program
    frames := [{ control := .statements program.body.toList, locals := [], globals := [] }]
    heap := #[]
    modules := [("__main__", [])]
    functions := []
    choices := []
    choiceToken := none
    status := .running }

def RConfig.setControl (config : RConfig) (control : RControl) : RConfig :=
  match config.frames with
  | [] => config
  | frame :: tail => { config with frames := { frame with control := control } :: tail }

def RConfig.setTop (config : RConfig) (frame : RFrame) : RConfig :=
  match config.frames with
  | [] => config
  | _ :: tail => { config with frames := frame :: tail }

def rSetEnv (env : REnv) (name : String) (value : RVal) : REnv :=
  (name, value) :: env.filter (fun binding => binding.1 != name)

def rDefinedFrame (frame : RFrame) (name : String) (remaining : List RStmt) : RFrame :=
  { control := .statements remaining
    locals := rSetEnv frame.locals name (.callable name)
    globals := frame.globals }

def RConfig.defineFunction (config : RConfig) (frame : RFrame) (tail : List RFrame)
    (function : RFunction) (remaining : List RStmt) : RConfig :=
  { program := config.program
    frames := rDefinedFrame frame function.name remaining :: tail
    heap := config.heap
    modules := config.modules
    functions := function :: config.functions
    choices := config.choices
    choiceToken := config.choiceToken
    status := config.status }

def rLookupEnv : REnv → String → Option RVal
  | [], _ => none
  | (name, value) :: rest, wanted =>
      if name == wanted then some value else rLookupEnv rest wanted

def rAssignedFrame (frame : RFrame) (name : String) (value : RVal)
    (remaining : List RStmt) : RFrame :=
  { control := .statements remaining
    locals := rSetEnv frame.locals name value
    globals := frame.globals }

def rEvalBinOp (op : BinOp) (left right : RVal) : Res RVal :=
  match op, left, right with
  | .add, .int a, .int b => .ok (.int (a + b))
  | .sub, .int a, .int b => .ok (.int (a - b))
  | .mult, .int a, .int b => .ok (.int (a * b))
  | _, _, _ => .unsupported "machine binary operator"

def RConfig.finish (config : RConfig) (event : REvent) : RConfig :=
  { config with frames := [], status := .finished event }

def RConfig.withChoice (config : RConfig) (choice : RChoice) : RConfig :=
  { config with choices := choice :: config.choices }

def RConfig.chooseToken (config : RConfig) (tail : List RChoice) (token : Nat) : RConfig :=
  { config with choices := tail, choiceToken := some token }

private theorem frame_with_control_eq (frame : RFrame) (control : RControl)
    (h : frame.control = control) : frame = { frame with control := control } := by
  cases frame
  simp_all

def rConstValue : Const → RVal
  | .none => .none
  | .ellipsis => .ellipsis
  | .bool b => .bool b
  | .int n => .int n
  | .float value => .float value
  | .str s => .str s
  | .bytes xs => .bytes xs

def resourceError : RResourcePoint → RError
  | .framePush => { errorClass := .recursion, args := [] }
  | .allocation => { errorClass := .memory, args := [] }

inductive Step : RConfig → RLabel → RConfig → Prop where
  | pass {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {rest : List RStmt} {span : Span}
      (hframe : config.frames = { frame with control := .statements (.pass span :: rest) } :: tail) :
      Step config .tau (config.setControl (.statements rest))
  | returnNone {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {span : Span}
      (hframe : config.frames = { frame with control := .statements [.ret none span] } :: tail) :
      Step config (.event (.return .none)) (config.finish (.return .none))
  | returnExpr {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {expression : Expr} {span : Span}
      (hframe : config.frames =
        { frame with control := .statements [.ret (some expression) span] } :: tail) :
      Step config .tau (config.setControl (.evaluate expression .returnValue))
  | exprStmt {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {expression : Expr} {span : Span}
      (hframe : config.frames =
        { frame with control := .statements [.expr expression span] } :: tail) :
      Step config .tau (config.setControl (.evaluate expression .discardValue))
  | assignStmt {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {name : String} {value : Expr} {rest : List RStmt} {span : Span}
      (hframe : config.frames =
        { frame with control := .statements (.assign (.name name span) value span :: rest) } :: tail) :
      Step config .tau (config.setControl (.evaluate value (.assign name rest)))
  | defineFunction {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {name : String} {params : Array RParam} {defaults : Array Expr}
      {body : Array RStmt} {rest : List RStmt} {span : Span}
      (hframe : config.frames =
        { frame with control := .statements (.functionDef name params defaults body span :: rest) } :: tail) :
      Step config .tau
        (config.defineFunction frame tail
          { name := name, params := params, body := body, globals := "__main__" } rest)
  | evaluateConstant {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {value : Const} {span : Span} {continuation : RKont}
      (hframe : config.frames =
        { frame with control := .evaluate (.constant value span) continuation } :: tail) :
      Step config .tau (config.setControl (.continueValue (rConstValue value) continuation))
  | evaluateName {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {name : String} {span : Span} {continuation : RKont} {value : RVal}
      (hframe : config.frames =
        { frame with control := .evaluate (.name name span) continuation } :: tail)
      (hvalue : rLookupEnv frame.locals name = some value) :
      Step config .tau (config.setControl (.continueValue value continuation))
  | evaluateBinOp {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {left right : Expr} {op : BinOp} {span : Span} {continuation : RKont}
      (hframe : config.frames =
        { frame with control := .evaluate (.binOp left op right span) continuation } :: tail) :
      Step config .tau
        (config.setControl (.evaluate left (.binOpLeft op right continuation)))
  | evaluateBinOpRight {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {left : RVal} {op : BinOp} {right : Expr} {continuation : RKont} :
      Step config .tau
        (config.setControl (.evaluate right (.binOpRight left op continuation)))
  | returnValue {config : RConfig} {value : RVal}
      (hcontrol : config.frames.head?.map RFrame.control = some (.continueValue value .returnValue)) :
      Step config (.event (.return value)) (config.finish (.return value))
  | discardValue {config : RConfig} {value : RVal}
      (hcontrol : config.frames.head?.map RFrame.control = some (.continueValue value .discardValue)) :
      Step config .tau (config.setControl (.statements []))
  | sequenceValue {config : RConfig} {value : RVal} {remaining : List RStmt}
      (hcontrol : config.frames.head?.map RFrame.control =
        some (.continueValue value (.sequence remaining))) :
      Step config .tau (config.setControl (.statements remaining))
  | assignValue {config : RConfig} {value : RVal} {name : String} {remaining : List RStmt}
      {frame : RFrame} {tail : List RFrame}
      (hframe : config.frames = frame :: tail)
      (hcontrol : frame.control = .continueValue value (.assign name remaining)) :
      Step config .tau
        (config.setTop (rAssignedFrame frame name value remaining))
  | binOpLeftValue {config : RConfig} {value : RVal} {op : BinOp} {right : Expr}
      {continuation : RKont}
      (hcontrol : config.frames.head?.map RFrame.control =
        some (.continueValue value (.binOpLeft op right continuation))) :
      Step config .tau (config.setControl (.evaluate right (.binOpRight value op continuation)))
  | binOpResult {config : RConfig} {left right : RVal} {op : BinOp} {continuation : RKont}
      (hcontrol : config.frames.head?.map RFrame.control =
        some (.continueValue right (.binOpRight left op continuation)))
      {value : RVal} (hresult : rEvalBinOp op left right = .ok value) :
      Step config .tau (config.setControl (.continueValue value continuation))
  | moduleEnd {config : RConfig} {frame : RFrame}
      (hframes : config.frames = [ { frame with control := .statements [] } ]) :
      Step config (.event (.return .none)) (config.finish (.return .none))
  | raiseRecursion {config : RConfig} {frame : RFrame} {tail : List RFrame}
      (hframes : config.frames = frame :: tail) :
      Step config .tau (config.setControl (.raising (resourceError .framePush)))
  | raiseMemory {config : RConfig} {frame : RFrame} {tail : List RFrame}
      (hframes : config.frames = frame :: tail) :
      Step config .tau (config.setControl (.raising (resourceError .allocation)))
  | raiseUncaught {config : RConfig} {error : RError}
      (hcontrol : config.frames.head?.map RFrame.control = some (.raising error)) :
      Step config (.event (.raise error)) (config.finish (.raise error))
  | refuseStmt {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {kind text : String} {span : Span}
      (hframe : config.frames =
        { frame with control := .statements [.unsupported kind text span] } :: tail) :
      Step config (.event (.refuse text)) (config.finish (.refuse text))
  | refuseExpression {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {kind text : String} {span : Span} {continuation : RKont}
      (hframe : config.frames =
        { frame with control := .evaluate (.unsupported kind text span) continuation } :: tail) :
      Step config (.event (.refuse text)) (config.finish (.refuse text))
  | choose {config : RConfig} {choice : RChoice} {tail : List RChoice} {token : Nat}
      (hchoices : config.choices = choice :: tail)
      (hmembership : token ∈ choice.allowed) :
      Step config (.event (.choice choice.kind token))
        (config.chooseToken tail token)

inductive RTrace : RConfig → List RLabel → RConfig → Prop where
  | nil (config : RConfig) : RTrace config [] config
  | cons {config next finish : RConfig} {label : RLabel} {labels : List RLabel} :
      Step config label next → RTrace next labels finish →
      RTrace config (label :: labels) finish

structure RImpl where
  choose : String → Nat
deriving Inhabited

def RImpl.cpython39 : RImpl := { choose := fun _ => 0 }

def resolveChoice (impl : RImpl) (config : RConfig) : Option (RLabel × RConfig) :=
  match config.choices with
  | [] => none
  | choice :: tail =>
      let token := impl.choose choice.kind
      if token ∈ choice.allowed then
        some (.event (.choice choice.kind token), config.chooseToken tail token)
      else none

def resolveAst (config : RConfig) : Option (RLabel × RConfig) :=
  match config.frames with
  | [] => none
  | frame :: _ =>
      match frame.control with
      | .statements [] => none
      | .statements (stmt :: rest) =>
          match stmt, rest with
          | .pass span, rest => some (.tau, config.setControl (.statements rest))
          | .ret none span, [] => some (.event (.return .none), config.finish (.return .none))
          | .ret (some expression) span, [] =>
              some (.tau, config.setControl (.evaluate expression .returnValue))
          | .expr expression span, [] =>
              some (.tau, config.setControl (.evaluate expression .discardValue))
          | .unsupported kind text span, [] =>
              some (.event (.refuse text), config.finish (.refuse text))
          | _, _ => none
      | .evaluate (.constant value span) continuation =>
          some (.tau, config.setControl (.continueValue (rConstValue value) continuation))
      | .evaluate (.unsupported kind text span) continuation =>
          some (.event (.refuse text), config.finish (.refuse text))
      | .evaluate _ _ => none
      | .continueValue value .returnValue =>
          some (.event (.return value), config.finish (.return value))
      | .continueValue _ .discardValue =>
          some (.tau, config.setControl (.statements []))
      | .continueValue _ .printValue => none
      | .continueValue _ _ => none
      | .raising _ =>
          match frame.control with
          | .raising error =>
              some (.event (.raise error), config.finish (.raise error))
          | _ => none

def resolve (impl : RImpl) (config : RConfig) : Option (RLabel × RConfig) :=
  match config.choices with
  | _ :: _ => resolveChoice impl config
  | [] => resolveAst config

/- A direct resolver for the B1 continuation-stack slice.  The compatibility
   resolver above remains available to the trace proof while this resolver
   exercises sequencing, assignment and expression continuations. -/
def resolveB1 (config : RConfig) : Option (RLabel × RConfig) :=
  match config.frames with
  | [] => none
  | frame :: _ =>
      match frame.control with
      | .statements [] =>
          if config.frames.tail.isEmpty then
            some (.event (.return .none), config.finish (.return .none))
          else none
      | .statements (stmt :: rest) =>
          match stmt with
          | .pass _ => some (.tau, config.setControl (.statements rest))
          | .expr expression _ =>
              some (.tau, config.setControl (.evaluate expression (.sequence rest)))
          | .assign (.name name _) value _ =>
              some (.tau, config.setControl (.evaluate value (.assign name rest)))
          | .functionDef name params defaults body span =>
              match config.frames with
              | current :: tail =>
                  some (.tau, config.defineFunction current tail
                    { name := name, params := params, body := body, globals := "__main__" } rest)
              | [] => none
          | .ret none _ => some (.event (.return .none), config.finish (.return .none))
          | .ret (some expression) _ =>
              some (.tau, config.setControl (.evaluate expression .returnValue))
          | .unsupported _ text _ =>
              some (.event (.refuse text), config.finish (.refuse text))
          | _ => some (.event (.refuse "machine statement"), config.finish (.refuse "machine statement"))
      | .evaluate (.constant value _) continuation =>
          some (.tau, config.setControl (.continueValue (rConstValue value) continuation))
      | .evaluate (.name name _) continuation =>
          match rLookupEnv frame.locals name with
          | some value => some (.tau, config.setControl (.continueValue value continuation))
          | none => some (.event (.refuse ("unbound name: " ++ name)),
              config.finish (.refuse ("unbound name: " ++ name)))
      | .evaluate (.binOp left op right _) continuation =>
          some (.tau, config.setControl (.evaluate left (.binOpLeft op right continuation)))
      | .evaluate (.unsupported _ text _) _ =>
          some (.event (.refuse text), config.finish (.refuse text))
      | .evaluate _ _ => none
      | .continueValue value .returnValue =>
          some (.event (.return value), config.finish (.return value))
      | .continueValue _ .discardValue => some (.tau, config.setControl (.statements []))
      | .continueValue value (.sequence remaining) =>
          some (.tau, config.setControl (.statements remaining))
      | .continueValue value (.assign name remaining) =>
          some (.tau, config.setTop (rAssignedFrame frame name value remaining))
      | .continueValue value (.binOpLeft op right continuation) =>
          some (.tau, config.setControl (.evaluate right (.binOpRight value op continuation)))
      | .continueValue right (.binOpRight left op continuation) =>
          match rEvalBinOp op left right with
          | .ok value => some (.tau, config.setControl (.continueValue value continuation))
          | _ => some (.event (.refuse "machine binary operator"),
              config.finish (.refuse "machine binary operator"))
      | .continueValue _ .printValue => none
      | .raising error => some (.event (.raise error), config.finish (.raise error))

def runB1 : Nat → RConfig → List RLabel × RConfig
  | 0, config => ([], config)
  | fuel + 1, config =>
      match resolveB1 config with
      | some (label, next) =>
          let result := runB1 fuel next
          (label :: result.1, result.2)
      | none => ([], config)

theorem resolveChoice_mem (impl : RImpl) (config : RConfig) (label : RLabel) (next : RConfig)
    (h : resolveChoice impl config = some (label, next)) :
    Step config label next := by
  cases hchoices : config.choices with
  | nil => simp [resolveChoice, hchoices] at h
  | cons choice tail =>
      simp [resolveChoice, hchoices] at h
      obtain ⟨hmembership, rfl, rfl⟩ := h
      exact Step.choose hchoices hmembership

theorem resolve_mem (impl : RImpl) (config : RConfig) (label : RLabel) (next : RConfig)
    (h : resolve impl config = some (label, next)) :
    Step config label next := by
  cases hchoices : config.choices with
   | cons choice tail =>
      exact resolveChoice_mem impl config label next (by simpa [resolve, hchoices] using h)
   | nil =>
      simp [resolve, hchoices] at h
      cases hframes : config.frames with
      | nil => simp [resolveAst, hframes] at h
      | cons frame tail =>
          cases hcontrol : frame.control with
          | statements remaining =>
              cases hremaining : remaining with
              | nil => simp [resolveAst, hframes, hcontrol, hremaining] at h
              | cons stmt rest =>
                  cases stmt with
                  | pass span =>
                      simp [resolveAst, hframes, hcontrol, hremaining] at h
                      obtain ⟨rfl, rfl⟩ := h
                      apply Step.pass (frame := frame) (tail := tail) (rest := rest) (span := span)
                      calc
                        config.frames = frame :: tail := hframes
                        _ = { frame with control := .statements (.pass span :: rest) } :: tail := by
                          rw [frame_with_control_eq frame _ (by simpa [hremaining] using hcontrol)]
                  | ret value span =>
                      cases value with
                      | none =>
                          cases rest with
                          | nil =>
                              simp [resolveAst, hframes, hcontrol, hremaining] at h
                              obtain ⟨rfl, rfl⟩ := h
                              apply Step.returnNone (frame := frame) (tail := tail) (span := span)
                              calc
                                config.frames = frame :: tail := hframes
                                _ = { frame with control := .statements [.ret none span] } :: tail := by
                                  rw [frame_with_control_eq frame _ (by simpa [hremaining] using hcontrol)]
                          | cons next rest => simp [resolveAst, hframes, hcontrol, hremaining] at h
                      | some expression =>
                          cases rest with
                          | nil =>
                              simp [resolveAst, hframes, hcontrol, hremaining] at h
                              obtain ⟨rfl, rfl⟩ := h
                              apply Step.returnExpr (frame := frame) (tail := tail)
                                (expression := expression) (span := span)
                              calc
                                config.frames = frame :: tail := hframes
                                _ = { frame with control := .statements [.ret (some expression) span] } :: tail := by
                                  rw [frame_with_control_eq frame _ (by simpa [hremaining] using hcontrol)]
                          | cons next rest => simp [resolveAst, hframes, hcontrol, hremaining] at h
                  | expr expression span =>
                      cases rest with
                      | nil =>
                          simp [resolveAst, hframes, hcontrol, hremaining] at h
                          obtain ⟨rfl, rfl⟩ := h
                          apply Step.exprStmt (frame := frame) (tail := tail)
                            (expression := expression) (span := span)
                          calc
                            config.frames = frame :: tail := hframes
                            _ = { frame with control := .statements [.expr expression span] } :: tail := by
                              rw [frame_with_control_eq frame _ (by simpa [hremaining] using hcontrol)]
                      | cons next rest => simp [resolveAst, hframes, hcontrol, hremaining] at h
                  | unsupported kind text span =>
                      cases rest with
                      | nil =>
                          simp [resolveAst, hframes, hcontrol, hremaining] at h
                          obtain ⟨rfl, rfl⟩ := h
                          apply Step.refuseStmt (frame := frame) (tail := tail)
                            (kind := kind) (text := text) (span := span)
                          calc
                            config.frames = frame :: tail := hframes
                            _ = { frame with control := .statements [.unsupported kind text span] } :: tail := by
                              rw [frame_with_control_eq frame _ (by simpa [hremaining] using hcontrol)]
                      | cons next rest => simp [resolveAst, hframes, hcontrol, hremaining] at h
                  | _ => simp [resolveAst, hframes, hcontrol, hremaining] at h
          | evaluate expression continuation =>
              cases expression with
              | constant value span =>
                  simp [resolveAst, hframes, hcontrol] at h
                  obtain ⟨rfl, rfl⟩ := h
                  apply Step.evaluateConstant (frame := frame) (tail := tail)
                    (value := value) (span := span) (continuation := continuation)
                  calc
                    config.frames = frame :: tail := hframes
                    _ = { frame with control := .evaluate (.constant value span) continuation } :: tail := by
                      rw [frame_with_control_eq frame _ (by simpa using hcontrol)]
              | unsupported kind text span =>
                  simp [resolveAst, hframes, hcontrol] at h
                  obtain ⟨rfl, rfl⟩ := h
                  apply Step.refuseExpression (frame := frame) (tail := tail)
                    (kind := kind) (text := text) (span := span)
                    (continuation := continuation)
                  calc
                    config.frames = frame :: tail := hframes
                    _ = { frame with control := .evaluate (.unsupported kind text span) continuation } :: tail := by
                      rw [frame_with_control_eq frame _ (by simpa using hcontrol)]
              | _ => simp [resolveAst, hframes, hcontrol] at h
          | continueValue value continuation =>
              cases continuation with
              | returnValue =>
                  simp [resolveAst, hframes, hcontrol] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hhead : config.frames.head?.map RFrame.control =
                      some (.continueValue value .returnValue) := by
                    simp [hframes, hcontrol]
                  exact Step.returnValue hhead
              | discardValue =>
                  simp [resolveAst, hframes, hcontrol] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hhead : config.frames.head?.map RFrame.control =
                      some (.continueValue value .discardValue) := by
                    simp [hframes, hcontrol]
                  exact Step.discardValue hhead
              | printValue => simp [resolveAst, hframes, hcontrol] at h
              | _ => simp [resolveAst, hframes, hcontrol] at h
          | raising error =>
              simp [resolveAst, hframes, hcontrol] at h
              obtain ⟨rfl, rfl⟩ := h
              have hhead : config.frames.head?.map RFrame.control =
                  some (.raising error) := by simp [hframes, hcontrol]
              exact Step.raiseUncaught hhead

def runRelation (impl : RImpl) : Nat → RConfig → List RLabel × RConfig
  | 0, config => ([], config)
  | fuel + 1, config =>
      match resolve impl config with
      | some (label, next) =>
          let result := runRelation impl fuel next
          (label :: result.1, result.2)
      | none => ([], config)

private def testSpan : Span :=
  { lineno := 1, colOffset := 0, endLineno := 1, endColOffset := 1 }

private def testModule : RModule :=
  { body := #[.ret (some (.constant (.int 7) testSpan)) testSpan] }

private def b1Module : RModule :=
  { body := #[
      .expr (.constant (.str "doc") testSpan) testSpan,
      .assign (.name "x" testSpan) (.constant (.int 1) testSpan) testSpan,
      .assign (.name "y" testSpan)
        (.binOp (.name "x" testSpan) .add (.constant (.int 2) testSpan) testSpan) testSpan,
      .expr (.name "y" testSpan) testSpan] }

private def bFunction : RFunction :=
  { name := "identity", params := #[], body := #[.ret none testSpan], globals := "__main__" }

example :
    (RConfig.initial b1Module).defineFunction
      { control := .statements b1Module.body.toList, locals := [], globals := [] } []
      bFunction [] |>.functions.length = 1 := by
  rfl

#guard (runB1 32 (RConfig.initial b1Module)).2.status ==
  .finished (.return .none)

example : (runB1 32 (RConfig.initial b1Module)).2.status =
    .finished (.return .none) := by
  rfl

example : ∃ c₁ c₂,
    Step (RConfig.initial b1Module) .tau c₁ ∧
    Step (RConfig.initial b1Module) .tau c₂ ∧ c₁ ≠ c₂ := by
  let frame : RFrame :=
    { control := .statements b1Module.body.toList, locals := [], globals := [] }
  refine ⟨(RConfig.initial b1Module).setControl (.raising (resourceError .framePush)),
    (RConfig.initial b1Module).setControl (.raising (resourceError .allocation)), ?_, ?_, ?_⟩
  · exact Step.raiseRecursion (frame := frame) (tail := []) (by rfl)
  · exact Step.raiseMemory (frame := frame) (tail := []) (by rfl)
  · intro h
    simp [RConfig.initial, RConfig.setControl, resourceError] at h

#guard (runRelation RImpl.cpython39 3 (RConfig.initial testModule)).1 ==
  [.tau, .tau, .event (.return (.int 7))]

private def choiceConfig : RConfig :=
  (RConfig.initial testModule).withChoice { kind := "identity", allowed := [0, 1] }

#guard (runRelation RImpl.cpython39 1 choiceConfig).1 ==
  [.event (.choice "identity" 0)]

example : (runRelation RImpl.cpython39 3 (RConfig.initial testModule)).1 =
    [.tau, .tau, .event (.return (.int 7))] := by
  rfl

theorem runRelation_trace (impl : RImpl) (fuel : Nat) (config : RConfig) :
    RTrace config (runRelation impl fuel config).1 (runRelation impl fuel config).2 := by
  induction fuel generalizing config with
  | zero => exact RTrace.nil config
  | succ fuel ih =>
      cases hresolve : resolve impl config with
      | none =>
          simp [runRelation, hresolve]
          exact RTrace.nil config
      | some transition =>
          cases transition with
          | mk label next =>
              have hstep : Step config label next := resolve_mem impl config label next hresolve
              simp [runRelation, hresolve]
              exact RTrace.cons hstep (ih next)

end LeanModels.Python.Machine
