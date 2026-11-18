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
  keywordVariadic : Bool := false
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
  | functionDefKw (name : String) (params : Array RParam) (defaults : Array Expr)
      (keywordDefaults : Array (Option Expr)) (body : Array RStmt) (span : Span)
  | classDef (name : String) (bases : Array Expr) (body : Array RStmt) (span : Span)
  | import (module : String) (alias : Option String) (span : Span)
  | unsupported (kind : String) (text : String) (span : Span)
deriving Repr, Inhabited, BEq

structure RFunction where
  name : String
  params : Array RParam
  defaults : Array Expr := #[]
  defaultValues : Array RVal := #[]
  keywordDefaultValues : Array (Option RVal) := #[]
  body : Array RStmt
  globals : String
  captured : REnv := []
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
  | index
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

inductive RResourcePoint where
  | framePush
  | allocation
deriving Repr, Inhabited, BEq

inductive RLabel where
  | tau
  | event (event : REvent)
deriving Repr, Inhabited, BEq

structure RChoice where
  kind : String
  allowed : List Nat
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
  | assignSubscriptReceiver (receiver : Expr) (index : Expr) (remaining : List RStmt)
  | assignSubscriptIndex (value : RVal) (index : Expr) (remaining : List RStmt)
  | assignSubscriptDone (receiver : RVal) (value : RVal) (remaining : List RStmt)
  | binOpLeft (op : BinOp) (right : Expr) (continuation : RKont)
  | binOpRight (left : RVal) (op : BinOp) (continuation : RKont)
  | unaryValue (op : UnaryOp) (continuation : RKont)
  | subscriptValue (index : Expr) (continuation : RKont)
  | subscriptIndex (receiver : RVal) (continuation : RKont)
  | tupleElements (remaining : List Expr) (values : List RVal) (continuation : RKont)
  | listElements (remaining : List Expr) (values : List RVal) (continuation : RKont)
  | dictKey (value : Expr) (remaining : List (Expr × Expr))
      (entries : List (RVal × RVal)) (continuation : RKont)
  | dictValue (key : RVal) (remaining : List (Expr × Expr))
      (entries : List (RVal × RVal)) (continuation : RKont)
  | ifBranch (body : List RStmt) (orelse : List RStmt) (remaining : List RStmt)
  | ifExpression (body : Expr) (orelse : Expr) (continuation : RKont)
  | callCallee (args : List Expr) (keywords : List (String × Expr)) (continuation : RKont)
  | callArg (callee : RVal) (remaining : List Expr) (values : List RVal)
      (continuation : RKont)
  | callArgsKeywords (callee : RVal) (remaining : List Expr) (values : List RVal)
      (remainingKeywords : List (String × Expr)) (keywordValues : List (String × RVal))
      (continuation : RKont)
  | callKeyword (callee : RVal) (name : String) (remaining : List (String × Expr))
      (positionalValues : List RVal) (keywordValues : List (String × RVal))
      (continuation : RKont)
  | callReturn (continuation : RKont)
deriving Repr, Inhabited, BEq

inductive RControl where
  | statements (remaining : List RStmt)
  | evaluate (expression : Expr) (continuation : RKont)
  | continueValue (value : RVal) (continuation : RKont)
  | raising (error : RError)
  /-- A rule has reached a resource point.  The relation admits both the
  ordinary continuation and the corresponding catchable resource raise. -/
  | resourceChoice (point : RResourcePoint) (continuation : RControl)
  /-- A configuration reached a construct for which the current machine
  slice has no rule.  Refusal is represented in the state before its event
  is emitted, so a stuck state can never silently terminate. -/
  | refusing (reason : String)
deriving Repr, Inhabited, BEq

structure RFrame where
  control : RControl
  locals : REnv
  globals : REnv
  module : String := "__main__"
  cells : REnv := []
deriving Repr, Inhabited, BEq

structure RConfig where
  program : RModule
  frames : List RFrame
  heap : Heap
  modules : List (String × REnv)
  functions : List RFunction
  builtins : List String
  choices : List RChoice
  choiceToken : Option Nat
  status : RStatus
deriving Repr, Inhabited, BEq

def RConfig.initial (program : RModule) : RConfig :=
  { program := program
    frames := [{ control := .statements program.body.toList, locals := [], globals := [], module := "__main__" }]
    heap := #[]
    modules := [("__main__", [])]
    functions := []
    builtins := ["print", "abs", "len"]
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

def rSetModule : List (String × REnv) → String → String → RVal → List (String × REnv)
  | [], module, name, value => [(module, [(name, value)])]
  | (current, env) :: rest, module, name, value =>
      if current == module then
        (current, rSetEnv env name value) :: rest
      else (current, env) :: rSetModule rest module name value

def rDefinedFrame (frame : RFrame) (name : String) (remaining : List RStmt) : RFrame :=
  { control := .statements remaining
    locals := rSetEnv frame.locals name (.callable name)
    globals := frame.globals
    module := frame.module
    cells := frame.cells }

def RConfig.defineFunction (config : RConfig) (frame : RFrame) (tail : List RFrame)
    (function : RFunction) (remaining : List RStmt) : RConfig :=
  { program := config.program
    frames := rDefinedFrame frame function.name remaining :: tail
    heap := config.heap
    modules := rSetModule config.modules frame.module function.name (.callable function.name)
    functions := function :: config.functions
    builtins := config.builtins
    choices := config.choices
    choiceToken := config.choiceToken
    status := config.status }

def rLookupEnv : REnv → String → Option RVal
  | [], _ => none
  | (name, value) :: rest, wanted =>
      if name == wanted then some value else rLookupEnv rest wanted

def rReadCell (heap : Heap) (value : RVal) : Option RVal :=
  match value with
  | .ref address =>
      match heap.get? address with
      | some (.cell (some contents)) => some contents
      | some _ => some value
      | none => none
  | _ => some value

def rLookupCaptured (heap : Heap) (env : REnv) (name : String) : Option RVal :=
  match rLookupEnv env name with
  | some value => rReadCell heap value
  | none => none

def rWriteCell (heap : Heap) (env : REnv) (name : String) (value : RVal) : Option Heap :=
  match rLookupEnv env name with
  | some (.ref address) =>
      match heap.get? address with
      | some (.cell _) => heap.update address (.cell (some value))
      | _ => none
  | _ => none

def rCaptureEnv : Heap → REnv → Heap × REnv
  | heap, [] => (heap, [])
  | heap, (name, value) :: rest =>
      match value with
      | .ref _ =>
          let result := rCaptureEnv heap rest
          (result.1, (name, value) :: result.2)
      | _ =>
          let allocated := Heap.alloc heap (.cell (some value))
          let result := rCaptureEnv allocated.1 rest
          (result.1, (name, .ref allocated.2) :: result.2)

def rCaptureLocals (heap : Heap) (frame : RFrame) : Heap × RFrame × REnv :=
  let result := rCaptureEnv heap (frame.locals ++ frame.cells)
  (result.1, { frame with locals := result.2 }, result.2)

def rCellAssignedFrame (frame : RFrame) (remaining : List RStmt) : RFrame :=
  { frame with control := .statements remaining }

def rLookupModule : List (String × REnv) → String → String → Option RVal
  | [], _, _ => none
  | (module, env) :: rest, wantedModule, wantedName =>
      if module == wantedModule then rLookupEnv env wantedName
      else rLookupModule rest wantedModule wantedName

def rFunction : List RFunction → String → Option RFunction
  | [], _ => none
  | function :: rest, name =>
      if function.name == name then some function else rFunction rest name

def rBuiltin (builtins : List String) (name : String) : Option RVal :=
  if name ∈ builtins then some (.callable name) else none

def rConstValue : Const → RVal
  | .none => .none
  | .ellipsis => .ellipsis
  | .bool b => .bool b
  | .int n => .int n
  | .float value => .float value
  | .str s => .str s
  | .bytes xs => .bytes xs

def rConstValues : List Expr → Option (List RVal)
  | [] => some []
  | .constant value _ :: rest =>
      match rConstValues rest with
      | some values => some (rConstValue value :: values)
      | none => none
  | _ :: _ => none

def rEvalDefaultValues (defaults : Array Expr) : Option (Array RVal) :=
  (rConstValues defaults.toList).map List.toArray

def rEvalKeywordDefaultValues : List (Option Expr) → Option (List (Option RVal))
  | [] => some []
  | none :: rest =>
      match rEvalKeywordDefaultValues rest with
      | some values => some (none :: values)
      | none => none
  | some expression :: rest =>
      match rConstValues [expression], rEvalKeywordDefaultValues rest with
      | some [value], some values => some (some value :: values)
      | _, _ => none

def rBindKeyword : REnv → List RParam → String → RVal → Option REnv
  | env, [], _, _ => none
  | env, parameter :: rest, name, value =>
      if parameter.name == name then
        if parameter.keywordVariadic then rBindKeyword env rest name value
        else if parameter.positionalOnly || parameter.variadic
            || Option.isSome (rLookupEnv env name) then none
        else some ((name, value) :: env)
      else rBindKeyword env rest name value

def rBindKeywords : REnv → List RParam → List (String × RVal) → Option REnv
  | env, _, [] => some env
  | env, params, (name, value) :: rest =>
      match rBindKeyword env params name value with
      | some updated => rBindKeywords updated params rest
      | none =>
          if params.any (fun parameter => parameter.keywordVariadic) then
            rBindKeywords env params rest
          else none

def rBindKeywordDefaults : REnv → List RParam → List (Option RVal) → Option REnv
  | env, [], _ => some env
  | env, parameter :: rest, default :: defaults =>
      if parameter.keywordOnly then
        match rLookupEnv env parameter.name, default with
        | some _, _ => rBindKeywordDefaults env rest defaults
        | none, some value =>
            rBindKeywordDefaults ((parameter.name, value) :: env) rest defaults
        | none, none => none
      else rBindKeywordDefaults env rest (default :: defaults)
  | env, parameter :: rest, [] =>
      if parameter.keywordOnly then none else rBindKeywordDefaults env rest []

def rBindPositionalDefaults : REnv → List RParam → List RVal → Option REnv
  | env, [], _ => some env
  | env, parameter :: rest, value :: values =>
      if Option.isSome (rLookupEnv env parameter.name) then
        rBindPositionalDefaults env rest values
      else rBindPositionalDefaults ((parameter.name, value) :: env) rest values
  | _, _, [] => none

def rAllBound : REnv → List RParam → Bool
  | _, [] => true
  | env, parameter :: rest =>
      Option.isSome (rLookupEnv env parameter.name) && rAllBound env rest

def rBindArguments (params : Array RParam) (defaults : Array RVal)
    (keywordDefaults : Array (Option RVal)) (values : List RVal)
    (keywords : List (String × RVal)) (kwargsValue : Option RVal) : Option REnv :=
  let parameters := params.toList
  let positional := parameters.filter
    (fun parameter => !parameter.keywordOnly && !parameter.variadic && !parameter.keywordVariadic)
  let variadic := parameters.filter (fun parameter => parameter.variadic && !parameter.keywordVariadic)
  let keywordVariadic := parameters.filter (fun parameter => parameter.keywordVariadic)
  if variadic.length > 1 || keywordVariadic.length > 1 then none
  else if defaults.size > positional.length then none
  else if variadic.isEmpty && values.length > positional.length then none
  else
    let missing := positional.length - values.length
    let supplied := values.take positional.length
    let initialEnv := (positional.map (fun parameter => parameter.name)).zip supplied
    let withVariadic :=
      match variadic with
      | [] => initialEnv
      | parameter :: _ => (parameter.name, .tuple (values.drop positional.length).toArray) :: initialEnv
    let withKeywordVariadic :=
      match keywordVariadic, kwargsValue with
      | [], _ => withVariadic
      | parameter :: _, some value => (parameter.name, value) :: withVariadic
      | _, none => withVariadic
    match rBindKeywords withKeywordVariadic parameters keywords with
    | some env =>
        if !keywordVariadic.isEmpty && kwargsValue.isNone then none
        else
          let defaultParameters := positional.drop (positional.length - defaults.size)
          match rBindPositionalDefaults env defaultParameters defaults.toList with
          | some withPositionalDefaults =>
              if rAllBound withPositionalDefaults positional then
                rBindKeywordDefaults withPositionalDefaults parameters keywordDefaults.toList
              else none
          | none => none
    | none => none

def rCallFrame (function : RFunction) (values : List RVal)
    (keywords : List (String × RVal)) (kwargsValue : Option RVal) : Option RFrame :=
  match rBindArguments function.params function.defaultValues function.keywordDefaultValues
      values keywords kwargsValue with
  | none => none
  | some locals =>
      some { control := .statements function.body.toList
             locals := locals
             globals := []
             module := function.globals
             cells := function.captured }

def rKeywordVariadicName : List RParam → Option String
  | [] => none
  | parameter :: rest =>
      if parameter.keywordVariadic then some parameter.name
      else rKeywordVariadicName rest

def rBuildKwargs (heap : Heap) (keywords : List (String × RVal)) : Heap × RVal :=
  let entries := (keywords.map (fun pair =>
    match pair with | (name, value) => (RVal.str name, value))).toArray
  let allocated := Heap.alloc heap (.dict entries 0)
  (allocated.1, .ref allocated.2)

def rBuildDict (heap : Heap) (entries : List (RVal × RVal)) : Heap × RVal :=
  let allocated := Heap.alloc heap (.dict entries.toArray 0)
  (allocated.1, .ref allocated.2)

def rLookupDictEntries : List (RVal × RVal) → RVal → Option RVal
  | [], _ => none
  | (key, value) :: rest, index =>
      if key == index then some value else rLookupDictEntries rest index

def rLookupDict (heap : Heap) (receiver index : RVal) : Option RVal :=
  match receiver with
  | .ref address =>
      match heap.get? address with
      | some (.dict entries _) =>
          rLookupDictEntries entries.toList index
      | _ => none
  | _ => none

def rUpdateDictEntries : List (RVal × RVal) → RVal → RVal → List (RVal × RVal)
  | [], key, value => [(key, value)]
  | (currentKey, currentValue) :: rest, key, value =>
      if currentKey == key then (key, value) :: rest
      else (currentKey, currentValue) :: rUpdateDictEntries rest key value

def rUpdateDict (heap : Heap) (receiver index value : RVal) : Option Heap :=
  match receiver with
  | .ref address =>
      match heap.get? address with
      | some (.dict entries version) =>
          Heap.update heap address (.dict (rUpdateDictEntries entries.toList index value).toArray (version + 1))
      | _ => none
  | _ => none

def rIndexValue (receiver index : RVal) : Option RVal :=
  let select (values : Array RVal) (position : Int) : Option RVal :=
    let length := values.size
    let normalized := if position < 0 then position + length else position
    if normalized < 0 then none
    else GetElem?.getElem? values normalized.toNat
  match receiver, index with
  | .tuple values, .int position => select values position
  | .listV values, .int position => select values position
  | _, _ => none

def rRenderPrintWithSep (separator : String) : List RVal → Option String
  | [] => some ""
  | value :: rest =>
      let rendered := match value with
        | .none => some "None"
        | .bool true => some "True"
        | .bool false => some "False"
        | .int n => some (toString n)
        | .str text => some text
        | _ => none
      match rendered, rRenderPrintWithSep separator rest with
      | some text, some tail =>
          if tail.isEmpty then some text else some (text ++ separator ++ tail)
      | _, _ => none

def rRenderPrint : List RVal → Option String := rRenderPrintWithSep " "

def rLen (value : RVal) : Option RVal :=
  match value with
  | .str text => some (.int text.length)
  | .tuple values => some (.int values.size)
  | .listV values => some (.int values.size)
  | _ => none

def RConfig.setModules (config : RConfig) (module : String) (name : String) (value : RVal) : RConfig :=
  { config with modules := rSetModule config.modules module name value }

def rAssignedFrame (frame : RFrame) (name : String) (value : RVal)
    (remaining : List RStmt) : RFrame :=
  { control := .statements remaining
    locals := rSetEnv frame.locals name value
    globals := frame.globals
    module := frame.module }

def rEvalBinOp (op : BinOp) (left right : RVal) : Res RVal :=
  match op, left, right with
  | .add, .int a, .int b => .ok (.int (a + b))
  | .sub, .int a, .int b => .ok (.int (a - b))
  | .mult, .int a, .int b => .ok (.int (a * b))
  | _, _, _ => .unsupported "machine binary operator"

def rTruthy : RVal → Bool
  | .none => false
  | .bool value => value
  | .int value => value != 0
  | .float value => !Float64.isZero value
  | .str value => !value.isEmpty
  | .tuple values => !values.isEmpty
  | .listV values => !values.isEmpty
  | _ => true

def rEvalUnary (op : UnaryOp) (value : RVal) : Option RVal :=
  match op, value with
  | .usub, .int number => some (.int (-number))
  | .uadd, .int number => some (.int number)
  | .not, value => some (.bool (!rTruthy value))
  | _, _ => none

def RConfig.finish (config : RConfig) (event : REvent) : RConfig :=
  { config with frames := [], status := .finished event }

def RConfig.withChoice (config : RConfig) (choice : RChoice) : RConfig :=
  { config with choices := choice :: config.choices }

def RConfig.chooseToken (config : RConfig) (tail : List RChoice) (token : Nat) : RConfig :=
  { config with choices := tail, choiceToken := some token }

def rStartCall (config : RConfig) (callee : RVal) (values : List RVal)
    (keywords : List (String × RVal)) (continuation : RKont) :
    Option (RLabel × RConfig) :=
  match callee with
  | .callable name =>
      match rFunction config.functions name with
      | some function =>
          let builtKwargs :=
            if keywords.isEmpty then (config.heap, none)
            else
              match rKeywordVariadicName function.params.toList with
              | some _ =>
                  let allocated := rBuildKwargs config.heap keywords
                  (allocated.1, some allocated.2)
              | none => (config.heap, none)
          match config.frames with
          | caller :: tail =>
              match rCallFrame function values keywords builtKwargs.2 with
              | some calleeFrame =>
                  some (.tau, { config with heap := builtKwargs.1, frames :=
                    calleeFrame :: { caller with
                      control := .continueValue .none (.callReturn continuation) } :: tail })
              | none => some (.event (.refuse "machine argument binder"),
                  config.finish (.refuse "machine argument binder"))
          | _ => some (.event (.refuse "machine call stack"),
              config.finish (.refuse "machine call stack"))
      | none =>
          if name == "print" then
            let separator := match rLookupEnv keywords "sep" with
              | some (.str text) => text
              | _ => " "
            match rRenderPrintWithSep separator values with
            | some text => some (.event (.output text),
                config.setControl (.continueValue .none continuation))
            | none => some (.tau, config.setControl (.refusing "machine print"))
          else if name == "len" then
            match values with
            | [value] =>
              match rLen value with
              | some result => some (.tau, config.setControl (.continueValue result continuation))
              | none => some (.tau, config.setControl (.refusing "machine len"))
            | _ => some (.tau, config.setControl (.refusing "machine len"))
          else some (.event (.refuse ("unknown function: " ++ name)),
            config.finish (.refuse ("unknown function: " ++ name)))
  | _ => some (.event (.refuse "machine non-callable"),
      config.finish (.refuse "machine non-callable"))

private theorem frame_with_control_eq (frame : RFrame) (control : RControl)
    (h : frame.control = control) : frame = { frame with control := control } := by
  cases frame
  simp_all

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
  | resourceProceed {config : RConfig} {point : RResourcePoint} {continuation : RControl}
      (hcontrol : config.frames.head?.map RFrame.control =
        some (.resourceChoice point continuation)) :
      Step config .tau (config.setControl continuation)
  | resourceRaise {config : RConfig} {point : RResourcePoint} {continuation : RControl}
      (hcontrol : config.frames.head?.map RFrame.control =
        some (.resourceChoice point continuation)) :
      Step config .tau (config.setControl (.raising (resourceError point)))
  | refuseControl {config : RConfig} {reason : String}
      (hcontrol : config.frames.head?.map RFrame.control = some (.refusing reason)) :
      Step config (.event (.refuse reason)) (config.finish (.refuse reason))
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
      | .refusing reason => some (.event (.refuse reason), config.finish (.refuse reason))
      | .resourceChoice _ continuation =>
          some (.tau, config.setControl continuation)
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
      | .refusing reason =>
          some (.event (.refuse reason), config.finish (.refuse reason))
      | .resourceChoice _ continuation =>
          some (.tau, config.setControl continuation)
      | .statements [] =>
          if config.frames.tail.isEmpty then
            some (.event (.return .none), config.finish (.return .none))
          else some (.tau, config.setControl (.continueValue .none .returnValue))
      | .statements (stmt :: rest) =>
          match stmt with
          | .pass _ => some (.tau, config.setControl (.statements rest))
          | .expr expression _ =>
              some (.tau, config.setControl (.evaluate expression (.sequence rest)))
          | .assign (.name name _) value _ =>
              some (.tau, config.setControl (.evaluate value (.assign name rest)))
          | .assign (.subscript receiver index _) value _ =>
              some (.tau, config.setControl
                (.evaluate value (.assignSubscriptReceiver receiver index rest)))
          | .ifStmt test body orelse _ =>
              some (.tau, config.setControl
                (.evaluate test (.ifBranch body.toList orelse.toList rest)))
          | .functionDef name params defaults body span =>
              match config.frames with
              | current :: tail =>
                  match rEvalDefaultValues defaults with
                  | none => some (.event (.refuse "machine default expression"),
                      config.finish (.refuse "machine default expression"))
                  | some defaultValues =>
                      let captured := rCaptureLocals config.heap current
                      let capturedFrame := captured.2.1
                      let function :=
                        { name := name, params := params, defaults := defaults,
                          defaultValues := defaultValues, keywordDefaultValues := #[], body := body,
                          globals := current.module, captured := captured.2.2 }
                      let defined := config.defineFunction capturedFrame tail function rest
                      some (.tau, { defined with heap := captured.1 })
              | [] => none
          | .functionDefKw name params defaults keywordDefaults body span =>
              match config.frames with
              | current :: tail =>
                  match rEvalDefaultValues defaults, rEvalKeywordDefaultValues keywordDefaults.toList with
                  | some defaultValues, some keywordDefaultValues =>
                      let captured := rCaptureLocals config.heap current
                      let capturedFrame := captured.2.1
                      let function :=
                        { name := name, params := params, defaults := defaults,
                          defaultValues := defaultValues,
                          keywordDefaultValues := keywordDefaultValues.toArray,
                          body := body, globals := current.module, captured := captured.2.2 }
                      let defined := config.defineFunction capturedFrame tail function rest
                      some (.tau, { defined with heap := captured.1 })
                  | _, _ => some (.event (.refuse "machine default expression"),
                      config.finish (.refuse "machine default expression"))
              | [] => none
          | .ret none _ => some (.tau, config.setControl (.continueValue .none .returnValue))
          | .ret (some expression) _ =>
              some (.tau, config.setControl (.evaluate expression .returnValue))
          | .unsupported _ text _ =>
              some (.event (.refuse text), config.finish (.refuse text))
          | _ => some (.event (.refuse "machine statement"), config.finish (.refuse "machine statement"))
      | .evaluate (.constant value _) continuation =>
          some (.tau, config.setControl (.continueValue (rConstValue value) continuation))
      | .evaluate (.name name _) continuation =>
          match rLookupCaptured config.heap frame.locals name with
          | some value => some (.tau, config.setControl (.continueValue value continuation))
          | none =>
              match rLookupCaptured config.heap frame.globals name with
              | some value => some (.tau, config.setControl (.continueValue value continuation))
              | none =>
                  match rLookupCaptured config.heap frame.cells name with
                  | some value =>
                      some (.tau, config.setControl (.continueValue value continuation))
                  | none =>
                      match rLookupModule config.modules frame.module name with
                      | some value =>
                          match rReadCell config.heap value with
                          | some value => some (.tau, config.setControl (.continueValue value continuation))
                          | none => some (.event (.refuse ("unbound name: " ++ name)),
                              config.finish (.refuse ("unbound name: " ++ name)))
                      | none =>
                          match rBuiltin config.builtins name with
                          | some value => some (.tau, config.setControl (.continueValue value continuation))
                          | none => some (.event (.refuse ("unbound name: " ++ name)),
                              config.finish (.refuse ("unbound name: " ++ name)))
      | .evaluate (.call function args keywords unsupported _) continuation =>
          match unsupported, keywords.toList with
          | some text, _ => some (.event (.refuse text), config.finish (.refuse text))
          | none, keywordList => some (.tau, config.setControl
              (.evaluate function (.callCallee args.toList keywordList continuation)))
      | .evaluate (.binOp left op right _) continuation =>
          some (.tau, config.setControl (.evaluate left (.binOpLeft op right continuation)))
      | .evaluate (.unaryOp op operand _) continuation =>
          some (.tau, config.setControl (.evaluate operand (.unaryValue op continuation)))
      | .evaluate (.subscript receiver index _) continuation =>
          some (.tau, config.setControl (.evaluate receiver (.subscriptValue index continuation)))
      | .evaluate (.tuple elements _) continuation =>
          match elements.toList with
          | [] => some (.tau, config.setControl (.continueValue (.tuple #[]) continuation))
          | first :: rest =>
              some (.tau, config.setControl
                (.evaluate first (.tupleElements rest [] continuation)))
      | .evaluate (.list elements _) continuation =>
          match elements.toList with
          | [] => some (.tau, config.setControl (.continueValue (.listV #[]) continuation))
          | first :: rest =>
              some (.tau, config.setControl
                (.evaluate first (.listElements rest [] continuation)))
      | .evaluate (.dict keys values _) continuation =>
          let pairs := keys.toList.zip values.toList
          match pairs with
          | [] =>
              let allocated := rBuildDict config.heap []
              some (.tau, { config with heap := allocated.1 } |>.setControl
                (.continueValue allocated.2 continuation))
          | (key, value) :: rest =>
              some (.tau, config.setControl
                (.evaluate key (.dictKey value rest [] continuation)))
      | .evaluate (.ifExp test body orelse _) continuation =>
          some (.tau, config.setControl
            (.evaluate test (.ifExpression body orelse continuation)))
      | .evaluate (.unsupported _ text _) _ =>
          some (.event (.refuse text), config.finish (.refuse text))
      | .evaluate _ _ =>
          some (.tau, config.setControl (.refusing "machine expression"))
      | .continueValue value .returnValue =>
          match config.frames with
          | _callee :: caller :: tail =>
              match caller.control with
              | .continueValue _ (.callReturn continuation) =>
                  some (.tau, { config with frames :=
                    { caller with control := .continueValue value continuation } :: tail })
              | _ => some (.event (.refuse "machine call stack"),
                  config.finish (.refuse "machine call stack"))
          | [_] => some (.event (.return value), config.finish (.return value))
          | [] => none
      | .continueValue _ .discardValue => some (.tau, config.setControl (.statements []))
      | .continueValue value (.sequence remaining) =>
          some (.tau, config.setControl (.statements remaining))
      | .continueValue value (.assignSubscriptReceiver receiver index remaining) =>
          some (.tau, config.setControl
            (.evaluate receiver (.assignSubscriptIndex value index remaining)))
      | .continueValue receiver (.assignSubscriptIndex originalValue index remaining) =>
          some (.tau, config.setControl
            (.evaluate index (.assignSubscriptDone receiver originalValue remaining)))
      | .continueValue index (.assignSubscriptDone receiver value remaining) =>
          match rUpdateDict config.heap receiver index value with
          | some heap => some (.tau, { config with heap := heap }.setControl (.statements remaining))
          | none => some (.tau, config.setControl (.refusing "machine subscript assignment"))
      | .continueValue value (.assign name remaining) =>
          match rWriteCell config.heap frame.locals name value with
          | some heap =>
              let next := { config.setTop (rCellAssignedFrame frame remaining) with heap := heap }
              if config.frames.tail.isEmpty then
                some (.tau, next.setModules frame.module name value)
              else
                some (.tau, next)
          | none =>
              match rWriteCell config.heap frame.cells name value with
              | some heap =>
                  let next := { config.setTop (rCellAssignedFrame frame remaining) with heap := heap }
                  if config.frames.tail.isEmpty then
                    some (.tau, next.setModules frame.module name value)
                  else
                    some (.tau, next)
              | none =>
                  let next := config.setTop (rAssignedFrame frame name value remaining)
                  if config.frames.tail.isEmpty then
                    some (.tau, next.setModules frame.module name value)
                  else
                    some (.tau, next)
      | .continueValue value (.binOpLeft op right continuation) =>
          some (.tau, config.setControl (.evaluate right (.binOpRight value op continuation)))
      | .continueValue value (.unaryValue op continuation) =>
          match rEvalUnary op value with
          | some result => some (.tau, config.setControl (.continueValue result continuation))
          | none => some (.tau, config.setControl (.refusing "machine unary operator"))
      | .continueValue receiver (.subscriptValue index continuation) =>
          some (.tau, config.setControl (.evaluate index (.subscriptIndex receiver continuation)))
      | .continueValue value (.ifBranch body orelse remaining) =>
          let selected := if rTruthy value then body else orelse
          some (.tau, config.setControl (.statements (selected ++ remaining)))
      | .continueValue value (.ifExpression body orelse continuation) =>
          some (.tau, config.setControl
            (.evaluate (if rTruthy value then body else orelse) continuation))
      | .continueValue index (.subscriptIndex receiver continuation) =>
          match rLookupDict config.heap receiver index with
          | some value => some (.tau, config.setControl (.continueValue value continuation))
          | none =>
              match rIndexValue receiver index with
              | some value => some (.tau, config.setControl (.continueValue value continuation))
              | none =>
                  match receiver, index with
                  | .tuple _, (.int _) | .listV _, (.int _) =>
                      some (.event (.raise { errorClass := .index, args := [] }),
                        config.finish (.raise { errorClass := .index, args := [] }))
                  | _, _ => some (.tau, config.setControl (.refusing "machine subscript"))
      | .continueValue value (.tupleElements remaining values continuation) =>
          match remaining with
          | next :: rest =>
              some (.tau, config.setControl
                (.evaluate next (.tupleElements rest (values ++ [value]) continuation)))
          | [] =>
              some (.tau, config.setControl
                (.continueValue (.tuple (values.toArray ++ #[value])) continuation))
      | .continueValue value (.listElements remaining values continuation) =>
          match remaining with
          | next :: rest =>
              some (.tau, config.setControl
                (.evaluate next (.listElements rest (values ++ [value]) continuation)))
          | [] =>
              some (.tau, config.setControl
                (.continueValue (.listV (values.toArray ++ #[value])) continuation))
      | .continueValue key (.dictKey value remaining entries continuation) =>
          some (.tau, config.setControl
            (.evaluate value (.dictValue key remaining entries continuation)))
      | .continueValue value (.dictValue key remaining entries continuation) =>
          let updated := entries ++ [(key, value)]
          match remaining with
          | (nextKey, nextValue) :: rest =>
              some (.tau, config.setControl
                (.evaluate nextKey (.dictKey nextValue rest updated continuation)))
          | [] =>
              let allocated := rBuildDict config.heap updated
              some (.tau, { config with heap := allocated.1 } |>.setControl
                (.continueValue allocated.2 continuation))
      | .continueValue right (.binOpRight left op continuation) =>
          match rEvalBinOp op left right with
          | .ok value => some (.tau, config.setControl (.continueValue value continuation))
          | _ => some (.event (.refuse "machine binary operator"),
              config.finish (.refuse "machine binary operator"))
      | .continueValue callee (.callCallee args keywords continuation) =>
          match args, keywords with
          | [], [] => rStartCall config callee [] [] continuation
          | [], (name, expression) :: rest =>
              some (.tau, config.setControl (.evaluate expression
                (.callKeyword callee name rest [] [] continuation)))
          | first :: rest, _ =>
              some (.tau, config.setControl (.evaluate first
                (.callArgsKeywords callee rest [] keywords [] continuation)))
      | .continueValue value
          (.callArgsKeywords callee remaining values remainingKeywords keywordValues continuation) =>
          match remaining with
          | next :: rest =>
              some (.tau, config.setControl (.evaluate next
                (.callArgsKeywords callee rest (values ++ [value]) remainingKeywords
                  keywordValues continuation)))
          | [] =>
              match remainingKeywords with
              | (name, expression) :: rest =>
                  some (.tau, config.setControl (.evaluate expression
                    (.callKeyword callee name rest (values ++ [value]) keywordValues continuation)))
              | [] => rStartCall config callee (values ++ [value]) keywordValues continuation
      | .continueValue value
          (.callKeyword callee currentName remaining positionalValues keywordValues continuation) =>
          match remaining with
          | (nextName, expression) :: rest =>
              some (.tau, config.setControl (.evaluate expression
                (.callKeyword callee nextName rest positionalValues
                  ((currentName, value) :: keywordValues) continuation)))
          | [] => rStartCall config callee positionalValues
              ((currentName, value) :: keywordValues) continuation
      | .continueValue value (.callArg callee remaining values continuation) =>
          match remaining with
          | next :: rest =>
              some (.tau, config.setControl (.evaluate next
                (.callArg callee rest (values ++ [value]) continuation)))
          | [] => rStartCall config callee (values ++ [value]) [] continuation
      | .continueValue _ (.callReturn _) =>
          some (.tau, config.setControl (.refusing "machine call return"))
      | .continueValue _ .printValue =>
          some (.tau, config.setControl (.refusing "machine print continuation"))
      | .raising error => some (.event (.raise error), config.finish (.raise error))

def runB1 : Nat → RConfig → List RLabel × RConfig
  | 0, config => ([], config)
  | fuel + 1, config =>
      match config.status, resolveB1 config with
      | .finished _, _ => ([], config)
      | .running, some (label, next) =>
          let result := runB1 fuel next
          (label :: result.1, result.2)
      | .running, none =>
          let stuck := config.finish (.refuse "machine stuck")
          ([.event (.refuse "machine stuck")], stuck)

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
          | refusing reason =>
              simp [resolveAst, hframes, hcontrol] at h
              obtain ⟨rfl, rfl⟩ := h
              have hhead : config.frames.head?.map RFrame.control =
                  some (.refusing reason) := by simp [hframes, hcontrol]
              exact Step.refuseControl hhead
          | resourceChoice point continuation =>
              simp [resolveAst, hframes, hcontrol] at h
              obtain ⟨rfl, rfl⟩ := h
              have hhead : config.frames.head?.map RFrame.control =
                  some (.resourceChoice point continuation) := by simp [hframes, hcontrol]
              exact Step.resourceProceed hhead
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

private def b1RefusalModule : RModule :=
  { body := #[.unsupported "Unsupported" "unsupported node" testSpan] }

private def bResourceConfig : RConfig :=
  let initial := RConfig.initial b1Module
  let frame : RFrame :=
    { control := .resourceChoice .framePush (.statements [])
      locals := [], globals := [] }
  { initial with frames := [frame] }

private def bStuckConfig : RConfig :=
  { RConfig.initial b1Module with frames := [] }

private def bFunction : RFunction :=
  { name := "identity", params := #[], body := #[.ret none testSpan], globals := "__main__" }

private def bGlobalModule : RModule :=
  { body := #[
      .assign (.name "x" testSpan) (.constant (.int 1) testSpan) testSpan,
      .functionDef "read" #[] #[]
        #[.ret (some (.name "x" testSpan)) testSpan] testSpan,
      .assign (.name "x" testSpan) (.constant (.int 2) testSpan) testSpan,
      .expr (.call (.name "read" testSpan) #[] #[] none testSpan) testSpan] }

private def bCallModule : RModule :=
  { body := #[
      .functionDef "identity" #[{ name := "value" }] #[]
        #[.ret (some (.name "value" testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "identity" testSpan)
        #[.constant (.int 7) testSpan] #[] none testSpan)) testSpan] }

private def bBuiltinModule : RModule :=
  { body := #[.expr (.call (.name "print" testSpan)
      #[.constant (.str "hello") testSpan] #[] none testSpan) testSpan] }

private def bTruthinessModule : RModule :=
  { body := #[
      .ifStmt (.constant (.float (Float64.ofBits 0)) testSpan)
        #[.expr (.call (.name "print" testSpan)
          #[.constant (.int 1) testSpan] #[] none testSpan) testSpan]
        #[.expr (.call (.name "print" testSpan)
          #[.constant (.int 2) testSpan] #[] none testSpan) testSpan] testSpan] }

private def bTupleModule : RModule :=
  { body := #[.ret (some (.subscript
      (.tuple #[.constant (.int 1) testSpan, .constant (.int 2) testSpan] testSpan)
      (.constant (.int (-1)) testSpan) testSpan)) testSpan] }

private def bLenModule : RModule :=
  { body := #[.expr (.call (.name "print" testSpan)
      #[.call (.name "len" testSpan)
        #[.tuple #[.constant (.int 1) testSpan, .constant (.int 2) testSpan] testSpan]
        #[] none testSpan] #[] none testSpan) testSpan] }

private def bDictModule : RModule :=
  { body := #[.ret (some (.subscript
      (.dict #[.constant (.str "x") testSpan] #[.constant (.int 7) testSpan] testSpan)
      (.constant (.str "x") testSpan) testSpan)) testSpan] }

private def bClosureModule : RModule :=
  { body := #[.functionDef "outer" #[] #[]
        #[.assign (.name "x" testSpan) (.constant (.int 9) testSpan) testSpan,
          .functionDef "inner" #[] #[]
            #[.ret (some (.name "x" testSpan)) testSpan] testSpan,
          .assign (.name "x" testSpan) (.constant (.int 10) testSpan) testSpan,
          .ret (some (.call (.name "inner" testSpan) #[] #[] none testSpan)) testSpan]
        testSpan,
      .ret (some (.call (.name "outer" testSpan) #[] #[] none testSpan)) testSpan] }

private def bCellModule : RModule :=
  { body := #[.assign (.name "x" testSpan) (.constant (.int 12) testSpan) testSpan,
      .ret (some (.name "x" testSpan)) testSpan] }

private def bCellConfig : RConfig :=
  let initial := RConfig.initial bCellModule
  let frame : RFrame :=
    { control := .statements bCellModule.body.toList, locals := [], globals := [] }
  { initial with
    heap := #[.cell (some (.int 11))],
    frames := [{ frame with cells := [("x", RVal.ref 0)] }] }

private def bDefaultModule : RModule :=
  { body := #[
      .functionDef "defaulted" #[{ name := "value", defaults := some #[.constant (.int 7) testSpan] }]
        #[.constant (.int 7) testSpan]
        #[.ret (some (.name "value" testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "defaulted" testSpan) #[] #[] none testSpan)) testSpan] }

private def bKeywordModule : RModule :=
  { body := #[
      .functionDefKw "keyworded"
        #[{ name := "a" }, { name := "b", keywordOnly := true }] #[]
        #[some (.constant (.int 3) testSpan)]
        #[.ret (some (.name "b" testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "keyworded" testSpan)
        #[.constant (.int 1) testSpan]
        #[("b", Expr.constant (.int 4) testSpan)] none testSpan)) testSpan] }

private def bKeywordDefaultModule : RModule :=
  { body := #[
      .functionDefKw "keyworded"
        #[{ name := "a" }, { name := "b", keywordOnly := true }] #[]
        #[some (.constant (.int 3) testSpan)]
        #[.ret (some (.name "b" testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "keyworded" testSpan)
        #[.constant (.int 1) testSpan] #[] none testSpan)) testSpan] }

private def bMixedDefaultKeywordModule : RModule :=
  { body := #[
      .functionDefKw "show" #[{ name := "left" }, { name := "right" }] #[.constant (.int 0) testSpan]
        #[] #[.expr (.call (.name "print" testSpan)
          #[.name "left" testSpan, .name "right" testSpan] #[] none testSpan) testSpan] testSpan,
      .expr (.call (.name "show" testSpan) #[.constant (.int 1) testSpan]
        #[("right", Expr.constant (.int 2) testSpan)] none testSpan) testSpan] }

private def bPositionalOnlyModule : RModule :=
  { body := #[
      .functionDef "positional" #[{ name := "value", positionalOnly := true }] #[]
        #[.ret (some (.name "value" testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "positional" testSpan)
        #[.constant (.int 5) testSpan] #[] none testSpan)) testSpan] }

private def bPositionalOnlyKeywordModule : RModule :=
  { body := #[
      .functionDef "positional" #[{ name := "value", positionalOnly := true }] #[]
        #[.ret (some (.name "value" testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "positional" testSpan) #[]
        #[("value", Expr.constant (.int 5) testSpan)] none testSpan)) testSpan] }

private def bVarargModule : RModule :=
  { body := #[
      .functionDef "collect" #[{ name := "items", variadic := true }] #[]
        #[.ret (some (.name "items" testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "collect" testSpan)
        #[.constant (.int 1) testSpan, .constant (.int 2) testSpan] #[] none testSpan)) testSpan] }

private def bKwargModule : RModule :=
  { body := #[
      .functionDef "collectKw" #[{ name := "items", keywordVariadic := true }] #[]
        #[.ret (some (.name "items" testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "collectKw" testSpan) #[]
        #[("a", Expr.constant (.int 1) testSpan),
          ("b", Expr.constant (.int 2) testSpan)] none testSpan)) testSpan] }

private def bKwargLookupModule : RModule :=
  { body := #[
      .functionDef "pickKw" #[{ name := "items", keywordVariadic := true }] #[]
        #[.ret (some (.subscript (.name "items" testSpan)
          (.constant (.str "a") testSpan) testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "pickKw" testSpan) #[]
        #[("a", Expr.constant (.int 9) testSpan)] none testSpan)) testSpan] }

private def bDuplicateKeywordModule : RModule :=
  { body := #[
      .functionDefKw "keyworded" #[{ name := "a" }, { name := "b", keywordOnly := true }] #[]
        #[some (.constant (.int 3) testSpan)]
        #[.ret (some (.name "b" testSpan)) testSpan] testSpan,
      .ret (some (.call (.name "keyworded" testSpan)
        #[.constant (.int 1) testSpan]
        #[("b", Expr.constant (.int 4) testSpan),
          ("b", Expr.constant (.int 5) testSpan)] none testSpan)) testSpan] }


example :
    ((RConfig.initial b1Module).defineFunction
      { control := .statements b1Module.body.toList, locals := [], globals := [] } []
      bFunction []).functions.length = 1 := by
  rfl

#guard (runB1 32 (RConfig.initial b1Module)).2.status ==
  .finished (.return .none)


#guard (runB1 8 (RConfig.initial b1RefusalModule)).2.status ==
  .finished (.refuse "unsupported node")

#guard (runB1 1 bStuckConfig).2.status ==
  .finished (.refuse "machine stuck")

example : (runB1 32 (RConfig.initial b1Module)).2.status =
    .finished (.return .none) := by
  rfl

example :
    (runB1 64 (RConfig.initial bGlobalModule)).2.status =
      .finished (.return .none) := by
  rfl

example :
    rLookupModule (runB1 64 (RConfig.initial bGlobalModule)).2.modules
      "__main__" "x" = some (.int 2) := by
  rfl

example :
    (runB1 64 (RConfig.initial bCallModule)).2.status =
      .finished (.return (.int 7)) := by
  rfl

example :
    (runB1 8 (RConfig.initial bBuiltinModule)).2.status =
      .finished (.return .none) := by
  rfl

#guard (runB1 16 (RConfig.initial bBuiltinModule)).1 ==
  [.tau, .tau, .tau, .tau, .tau, .event (.output "hello"), .tau,
    .event (.return .none)]

#guard (runB1 32 (RConfig.initial bTruthinessModule)).1 ==
  [.tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau,
    .event (.output "2"), .tau, .event (.return .none)]

#guard (runB1 32 (RConfig.initial bTupleModule)).2.status ==
  .finished (.return (.int 2))

#guard (runB1 32 (RConfig.initial bLenModule)).1 ==
  [.tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau,
    .event (.output "2"), .tau, .event (.return .none)]

#guard (runB1 32 (RConfig.initial bDictModule)).2.status ==
  .finished (.return (.int 7))

#guard (runB1 128 (RConfig.initial bMixedDefaultKeywordModule)).2.status ==
  .finished (.return .none)

example :
    (runB1 128 (RConfig.initial bClosureModule)).2.status =
      .finished (.return (.int 10)) := by
  rfl

example :
    (runB1 12 bCellConfig).2.status =
      .finished (.return (.int 12)) := by
  rfl

example :
    (runB1 64 (RConfig.initial bDefaultModule)).2.status =
      .finished (.return (.int 7)) := by
  rfl

example :
    (runB1 96 (RConfig.initial bKeywordModule)).2.status =
      .finished (.return (.int 4)) := by
  rfl

example :
    (runB1 96 (RConfig.initial bKeywordDefaultModule)).2.status =
      .finished (.return (.int 3)) := by
  rfl

example :
    (runB1 96 (RConfig.initial bPositionalOnlyModule)).2.status =
      .finished (.return (.int 5)) := by
  rfl

example :
    (runB1 96 (RConfig.initial bPositionalOnlyKeywordModule)).2.status =
      .finished (.refuse "machine argument binder") := by
  rfl

example :
    (runB1 96 (RConfig.initial bVarargModule)).2.status =
      .finished (.return (.tuple #[.int 1, .int 2])) := by
  rfl

example :
    (runB1 96 (RConfig.initial bKwargModule)).2.status =
      .finished (.return (.ref 0)) := by
  rfl

#guard (runB1 128 (RConfig.initial bKwargLookupModule)).2.status ==
  .finished (.return (.int 9))

example :
    (runB1 96 (RConfig.initial bDuplicateKeywordModule)).2.status =
      .finished (.refuse "machine argument binder") := by
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

example : ∃ c₁ c₂,
    Step bResourceConfig .tau c₁ ∧
    Step bResourceConfig .tau c₂ ∧ c₁ ≠ c₂ := by
  refine ⟨bResourceConfig.setControl (.statements []),
    bResourceConfig.setControl (.raising (resourceError .framePush)), ?_, ?_, ?_⟩
  · exact Step.resourceProceed (by rfl)
  · exact Step.resourceRaise (by rfl)
  · simp [bResourceConfig, RConfig.setControl, resourceError]

example : ∃ next,
    Step bResourceConfig .tau next ∧
      next.frames.head?.map RFrame.control = some (.raising (resourceError .framePush)) := by
  refine ⟨bResourceConfig.setControl (.raising (resourceError .framePush)),
    Step.resourceRaise (by rfl), ?_⟩
  rfl

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
