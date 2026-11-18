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
deriving Repr, Inhabited, BEq

inductive RControl where
  | statements (remaining : List RStmt)
  | evaluate (expression : Expr) (continuation : RKont)
  | continueValue (value : RVal) (continuation : RKont)
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
  choices : List RChoice
  pending : List RError
  resourcePoint : Option RResourcePoint
  status : RStatus
deriving Repr, Inhabited, BEq

def RConfig.initial (program : RModule) : RConfig :=
  { program := program
    frames := [{ control := .statements program.body.toList, locals := [], globals := [] }]
    heap := #[]
    choices := []
    pending := []
    resourcePoint := none
    status := .running }

def RConfig.setControl (config : RConfig) (control : RControl) : RConfig :=
  match config.frames with
  | [] => config
  | frame :: tail => { config with frames := { frame with control := control } :: tail }

def RConfig.finish (config : RConfig) (event : REvent) : RConfig :=
  { config with frames := [], status := .finished event }

def RConfig.withChoice (config : RConfig) (choice : RChoice) : RConfig :=
  { config with choices := choice :: config.choices }

def RConfig.withResourcePoint (config : RConfig) (point : RResourcePoint) : RConfig :=
  { config with resourcePoint := some point }

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
  | evaluateConstant {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {value : Const} {span : Span} {continuation : RKont}
      (hframe : config.frames =
        { frame with control := .evaluate (.constant value span) continuation } :: tail) :
      Step config .tau (config.setControl (.continueValue (rConstValue value) continuation))
  | returnValue {config : RConfig} {value : RVal}
      (hcontrol : config.frames.head?.map RFrame.control = some (.continueValue value .returnValue)) :
      Step config (.event (.return value)) (config.finish (.return value))
  | discardValue {config : RConfig} {value : RVal}
      (hcontrol : config.frames.head?.map RFrame.control = some (.continueValue value .discardValue)) :
      Step config .tau (config.setControl (.statements []))
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
        { config with choices := tail }
  | raiseResource {config : RConfig} {point : RResourcePoint}
      (hpoint : config.resourcePoint = some point) :
      Step config (.event (.raise (resourceError point)))
        { config with pending := (resourceError point :: config.pending), resourcePoint := none }

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
        some (.event (.choice choice.kind token), { config with choices := tail })
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

def resolve (impl : RImpl) (config : RConfig) : Option (RLabel × RConfig) :=
  match config.choices with
  | _ :: _ => resolveChoice impl config
  | [] => resolveAst config

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
