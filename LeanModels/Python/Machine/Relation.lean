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

inductive RRawExpr where
  /-- A raw machine expression keeps its CPython node kind and child order
  until the corresponding expression semantics is implemented. -/
  | node (kind : String) (children : Array RRawExpr) (span : Span)
deriving Repr, Inhabited, BEq

inductive RStmt where
  | pass (span : Span)
  | ret (value : Option Expr) (span : Span)
  | expr (value : Expr) (span : Span)
  | exprRaw (value : RRawExpr) (span : Span)
  /-- A statement whose direct expression fields contain a machine-frontier
      node.  Keep the statement kind and child order until its semantics is
      implemented instead of converting through the compatibility `Expr`. -/
  | raw (kind : String) (children : Array RRawExpr) (span : Span)
  | assign (target : Expr) (value : Expr) (span : Span)
  | assignMany (targets : Array Expr) (value : Expr) (span : Span)
  | annAssign (target : Expr) (annotation : Expr) (value : Option Expr)
      (simple : Bool) (span : Span)
  | unpackAssign (before : Array String) (star : String) (after : Array String)
      (value : Expr) (span : Span)
  | augAssign (target : Expr) (op : BinOp) (value : Expr) (span : Span)
  | delete (target : Expr) (span : Span)
  | deleteMany (targets : Array Expr) (span : Span)
  | raise (exception : Option Expr) (cause : Option Expr) (span : Span)
  | assertStmt (test : Expr) (msg : Option Expr) (span : Span)
  | yieldStmt (value : Option Expr) (span : Span)
  | yieldFrom (value : Expr) (span : Span)
  | brk (span : Span)
  | cont (span : Span)
  | ifStmt (test : Expr) (body : Array RStmt) (orelse : Array RStmt) (span : Span)
  | whileStmt (test : Expr) (body : Array RStmt) (orelse : Array RStmt) (span : Span)
  | forStmt (target : Expr) (iter : Expr) (body : Array RStmt) (orelse : Array RStmt)
      (span : Span)
  | asyncForStmt (target : Expr) (iter : Expr) (body : Array RStmt)
      (orelse : Array RStmt) (span : Span)
  | functionDef (name : String) (params : Array RParam) (defaults : Array Expr)
      (body : Array RStmt) (span : Span)
  | functionDefFull (name : String) (params : Array RParam) (defaults : Array Expr)
      (decorators : Array Expr) (returns : Option Expr) (body : Array RStmt) (span : Span)
  | functionDefKw (name : String) (params : Array RParam) (defaults : Array Expr)
      (keywordDefaults : Array (Option Expr)) (body : Array RStmt) (span : Span)
  | classDef (name : String) (bases : Array Expr) (keywords : Array (String × Expr))
      (decorators : Array Expr) (body : Array RStmt) (span : Span)
  | withStmt (items : Array (Expr × Option Expr)) (body : Array RStmt) (isAsync : Bool)
      (span : Span)
  | tryStmt (body : Array RStmt)
      (handlers : Array (Option Expr × Option String × Array RStmt))
      (orelse : Array RStmt) (finalbody : Array RStmt) (span : Span)
  | import (module : String) (alias : Option String) (span : Span)
  | importMany (names : Array (String × Option String)) (span : Span)
  | importFrom (module : Option String) (names : Array (String × Option String))
      (level : Nat) (span : Span)
  | global (names : Array String) (span : Span)
  | nonlocal (names : Array String) (span : Span)
  | unsupported (kind : String) (text : String) (span : Span)
deriving Repr, Inhabited, BEq

structure RFunction where
  /-- Stable identity for a function value.  CPython binds the object created
  by each `def`, so an alias keeps that object when the defining name is
  rebound later. -/
  id : Nat := 0
  name : String
  params : Array RParam
  defaults : Array Expr := #[]
  defaultValues : Array RVal := #[]
  keywordDefaultValues : Array (Option RVal) := #[]
  body : Array RStmt
  globals : String
  captured : REnv := []
  globalNames : List String := []
  nonlocalNames : List String := []
  localNames : List String := []
deriving Repr, Inhabited, BEq

structure RClass where
  id : Nat := 0
  name : String
  attrs : REnv := []
  bases : Array Nat := #[]
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
  | unboundLocal
  | type
  | index
  | attribute
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
  | assignPattern (target : Expr) (remaining : List RStmt)
  | assignUnpack (before : Array String) (star : String) (after : Array String)
      (remaining : List RStmt)
  | augAssignLeft (name : String) (op : BinOp) (value : Expr) (remaining : List RStmt)
  | augAssignRight (left : RVal) (name : String) (op : BinOp) (remaining : List RStmt)
  | augAssignAttributeReceiver (attr : String) (op : BinOp) (value : Expr)
      (remaining : List RStmt)
  | augAssignAttributeValue (receiver : RVal) (attr : String) (op : BinOp)
      (value : Expr) (remaining : List RStmt)
  | augAssignAttributeRight (receiver : RVal) (attr : String) (left : RVal)
      (op : BinOp) (remaining : List RStmt)
  | assignSubscriptReceiver (receiver : Expr) (index : Expr) (remaining : List RStmt)
  | assignSubscriptIndex (value : RVal) (index : Expr) (remaining : List RStmt)
  | assignSubscriptDone (receiver : RVal) (value : RVal) (remaining : List RStmt)
  | assignAttributeReceiver (receiver : Expr) (attr : String) (remaining : List RStmt)
  | assignAttributeValue (attr : String) (value : RVal) (remaining : List RStmt)
  | deleteAttributeReceiver (attr : String) (remaining : List RStmt)
  | deleteSubscriptReceiver (index : Expr) (remaining : List RStmt)
  | deleteSubscriptIndex (receiver : RVal) (remaining : List RStmt)
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
  | whileBranch (test : Expr) (body : List RStmt) (orelse : List RStmt)
      (remaining : List RStmt) (span : Span)
  | forIter (target : Expr) (body : List RStmt) (orelse : List RStmt)
      (remaining : List RStmt)
  | forNext (target : Expr) (values : List RVal) (body : List RStmt)
      (orelse : List RStmt) (remaining : List RStmt)
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
  | callReturnInstance (instanceValue : RVal) (continuation : RKont)
  | lenResult (continuation : RKont)
  | reprResult (continuation : RKont)
  | strResult (continuation : RKont)
  | absResult (continuation : RKont)
  | subscriptResult (continuation : RKont)
  | setitemResult (remaining : List RStmt)
  | compareResult (op : CmpOp) (continuation : RKont)
  | unaryResult (continuation : RKont)
  | binaryResult (continuation : RKont)
  | classDef (name : String) (bases : Array Nat) (remaining : List RStmt)
  | classDefBases (name : String) (body : List RStmt) (remaining : List RStmt)
      (baseExpressions : List Expr) (baseValues : List RVal)
  | attributeValue (attr : String) (continuation : RKont)
  | compareLeft (op : CmpOp) (right : Expr) (continuation : RKont)
  | compareRight (left : RVal) (op : CmpOp) (continuation : RKont)
deriving Repr, Inhabited, BEq

inductive RControl where
  | statements (remaining : List RStmt)
  | evaluate (expression : Expr) (continuation : RKont)
  | continueValue (value : RVal) (continuation : RKont)
  | raising (error : RError)
  /-- A rule has reached a resource point.  The relation admits both the
  ordinary continuation and the corresponding catchable resource raise. -/
  | resourceChoice (point : RResourcePoint) (continuation : RControl)
  | allocateList (values : List RVal) (continuation : RKont)
  | allocateDict (entries : List (RVal × RVal)) (continuation : RKont)
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
  completion : Option RKont := none
  globalNames : List String := []
  nonlocalNames : List String := []
  localNames : List String := []
deriving Repr, Inhabited, BEq

structure RConfig where
  program : RModule
  frames : List RFrame
  heap : Heap
  modules : List (String × REnv)
  functions : List RFunction
  nextFunctionId : Nat
  classes : List RClass
  nextClassId : Nat
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
    nextFunctionId := 0
    classes := []
    nextClassId := 0
    builtins := ["print", "abs", "len", "repr", "str"]
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

def rFunctionToken (id : Nat) : String :=
  "__machine_fn:" ++ String.ofList (List.replicate id 'x')

def rSetModule : List (String × REnv) → String → String → RVal → List (String × REnv)
  | [], module, name, value => [(module, [(name, value)])]
  | (current, env) :: rest, module, name, value =>
      if current == module then
        (current, rSetEnv env name value) :: rest
      else (current, env) :: rSetModule rest module name value

def rDefinedFrame (frame : RFrame) (name : String) (id : Nat) (remaining : List RStmt) : RFrame :=
  { control := .statements remaining
    locals := rSetEnv frame.locals name (.callable (rFunctionToken id))
    globals := frame.globals
    module := frame.module
    cells := frame.cells
    completion := frame.completion
    globalNames := frame.globalNames
    nonlocalNames := frame.nonlocalNames
    localNames := frame.localNames }

def RConfig.defineFunction (config : RConfig) (frame : RFrame) (tail : List RFrame)
    (function : RFunction) (remaining : List RStmt) : RConfig :=
  { program := config.program
    frames := rDefinedFrame frame function.name function.id remaining :: tail
    heap := config.heap
    modules := rSetModule config.modules frame.module function.name
      (.callable (rFunctionToken function.id))
    functions := function :: config.functions
    nextFunctionId := max config.nextFunctionId (function.id + 1)
    classes := config.classes
    nextClassId := config.nextClassId
    builtins := config.builtins
    choices := config.choices
    choiceToken := config.choiceToken
    status := config.status }

def RConfig.defineMethod (config : RConfig) (frame : RFrame) (tail : List RFrame)
    (function : RFunction) (remaining : List RStmt) : RConfig :=
  { config with
    frames := rDefinedFrame frame function.name function.id remaining :: tail
    functions := function :: config.functions
    nextFunctionId := max config.nextFunctionId (function.id + 1) }

def rLookupEnv : REnv → String → Option RVal
  | [], _ => none
  | (name, value) :: rest, wanted =>
      if name == wanted then some value else rLookupEnv rest wanted

def rDeleteEnv (env : REnv) (name : String) : Option REnv :=
  if rLookupEnv env name |>.isSome then some (env.filter (fun binding => binding.1 != name)) else none

def rDeleteModule : List (String × REnv) → String → String → Option (List (String × REnv))
  | [], _, _ => none
  | (current, env) :: rest, module, name =>
      if current == module then
        match rDeleteEnv env name with
        | some updated => some ((current, updated) :: rest)
        | none => none
      else
        match rDeleteModule rest module name with
        | some updated => some ((current, env) :: updated)
        | none => none

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

def rFunctionByToken : List RFunction → String → Option RFunction
  | [], _ => none
  | function :: rest, token =>
      if rFunctionToken function.id == token then some function
      else rFunctionByToken rest token

def rClassToken (id : Nat) : String :=
  "__machine_class:" ++ String.ofList (List.replicate id 'x')

def rBoundMethodToken (functionToken : String) (address : Addr) : String :=
  "__machine_bound:" ++ functionToken ++ "|" ++ toString address

def rBoundMethodInfo (token : String) : Option (String × Addr) :=
  if token.startsWith "__machine_bound:" then
    let suffix := String.ofList (token.toList.drop "__machine_bound:".length)
    match suffix.splitOn "|" with
    | [functionToken, addressText] =>
        addressText.toNat?.map (fun address => (functionToken, address))
    | _ => none
  else none

def rClassByToken : List RClass → String → Option RClass
  | [], _ => none
  | cls :: rest, token =>
      if rClassToken cls.id == token then some cls
      else rClassByToken rest token

def rClassById : List RClass → Nat → Option RClass
  | [], _ => none
  | cls :: rest, id =>
      if cls.id == id then some cls else rClassById rest id

def rLookupClassAttrFuel (classes : List RClass) : Nat → Nat → String → Option RVal
  | 0, _, _ => none
  | fuel + 1, classId, attr =>
      match rClassById classes classId with
      | none => none
      | some cls =>
          match rLookupEnv cls.attrs attr with
          | some value => some value
          | none =>
              let rec search : List Nat → Option RVal
                | [] => none
                | base :: rest =>
                    match rLookupClassAttrFuel classes fuel base attr with
                    | some value => some value
                    | none => search rest
              search cls.bases.toList

def rLookupClassAttr (classes : List RClass) (classId : Nat) (attr : String) : Option RVal :=
  rLookupClassAttrFuel classes classes.length classId attr

def rLookupInstanceAttr (heap : Heap) (address : Addr) (attr : String) : Option RVal :=
  match heap.get? address with
  | some (.instance _ attrs) => rLookupEnv attrs.toList attr
  | _ => none

def rUpdateInstanceAttr (heap : Heap) (address : Addr) (attr : String) (value : RVal) : Option Heap :=
  match heap.get? address with
  | some (.instance cls attrs) =>
      Heap.update heap address (.instance cls (rSetEnv attrs.toList attr value).toArray)
  | _ => none

def rDeleteInstanceAttr (heap : Heap) (address : Addr) (attr : String) : Option Heap :=
  match heap.get? address with
  | some (.instance cls attrs) =>
      match rDeleteEnv attrs.toList attr with
      | some updated => Heap.update heap address (.instance cls updated.toArray)
      | none => none
  | _ => none

def rLookupInstanceClassAttr (heap : Heap) (classes : List RClass)
    (address : Addr) (attr : String) : Option RVal :=
  match heap.get? address with
  | some (.instance cls attrs) =>
      match rLookupEnv attrs.toList attr with
      | some value => some value
      | none => rLookupClassAttr classes cls attr
  | _ => none

def rHeapIsInstance (heap : Heap) (address : Addr) : Bool :=
  match heap.get? address with
  | some (.instance _ _) => true
  | _ => false

def rUpdateClassAttr : List RClass → String → String → RVal → Option (List RClass)
  | [], _, _, _ => none
  | cls :: rest, token, attr, value =>
      if rClassToken cls.id == token then
        some ({ cls with attrs := rSetEnv cls.attrs attr value } :: rest)
      else
        match rUpdateClassAttr rest token attr value with
        | some updated => some (cls :: updated)
        | none => none

def rDeleteClassAttr : List RClass → String → String → Option (List RClass)
  | [], _, _ => none
  | cls :: rest, token, attr =>
      if rClassToken cls.id == token then
        match rDeleteEnv cls.attrs attr with
        | some attrs => some ({ cls with attrs := attrs } :: rest)
        | none => none
      else
        match rDeleteClassAttr rest token attr with
        | some updated => some (cls :: updated)
        | none => none

def rClassBodySupportedAfterDoc : List RStmt → Bool
  | [] => true
  | .pass _ :: rest => rClassBodySupportedAfterDoc rest
  | .assign (.name _ _) _ _ :: rest => rClassBodySupportedAfterDoc rest
  | .functionDef _ _ _ _ _ :: rest => rClassBodySupportedAfterDoc rest
  | .functionDefKw _ _ _ _ _ _ :: rest => rClassBodySupportedAfterDoc rest
  | _ => false

def rClassBodySupported : List RStmt → Bool
  | [] => true
  | .expr (.constant (.str _) _) _ :: rest => rClassBodySupportedAfterDoc rest
  | statements => rClassBodySupportedAfterDoc statements

def rClassDoc : List RStmt → Option RVal
  | .expr (.constant (.str text) _) _ :: _ => some (.str text)
  | _ => none

def rDirectBaseIds (classes : List RClass) : List RVal → Option (Array Nat)
  | [] => some #[]
  | .callable token :: rest =>
      match rClassByToken classes token, rDirectBaseIds classes rest with
      | some cls, some ids =>
          if cls.bases.isEmpty && cls.id ∉ ids.toList then some (#[cls.id] ++ ids)
          else none
      | _, _ => none
  | _ :: _ => none

def rFinishClass (config : RConfig) (classFrame : RFrame) (tail : List RFrame)
    (name : String) (bases : Array Nat) (remaining : List RStmt) : Option RConfig :=
  match tail with
  | caller :: rest =>
      let cls : RClass := RClass.mk config.nextClassId name classFrame.locals bases
      some { config with
        frames := { caller with control := .statements remaining } :: rest
        modules := rSetModule config.modules caller.module name (.callable (rClassToken cls.id))
        classes := cls :: config.classes
        nextClassId := config.nextClassId + 1 }
  | [] => none

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
             cells := function.captured
             globalNames := function.globalNames
             nonlocalNames := function.nonlocalNames
             localNames := function.localNames }

def rKeywordVariadicName : List RParam → Option String
  | [] => none
  | parameter :: rest =>
      if parameter.keywordVariadic then some parameter.name
      else rKeywordVariadicName rest

def rScopeNames : List RStmt → List String × List String
  | [] => ([], [])
  | .global names _ :: rest =>
      let tail := rScopeNames rest
      (names.toList ++ tail.1, tail.2)
  | .nonlocal names _ :: rest =>
      let tail := rScopeNames rest
      (tail.1, names.toList ++ tail.2)
  | _ :: rest => rScopeNames rest

def rTargetNames : Expr → List String
  | .name name _ => [name]
  | _ => []

def rBoundNames : List RStmt → List String
  | [] => []
  | .assign target _ _ :: rest => rTargetNames target ++ rBoundNames rest
  | .assignMany targets _ _ :: rest => targets.toList.flatMap rTargetNames ++ rBoundNames rest
  | .unpackAssign before star after _ _ :: rest =>
      before.toList ++ [star] ++ after.toList ++ rBoundNames rest
  | .augAssign target _ _ _ :: rest => rTargetNames target ++ rBoundNames rest
  | .delete target _ :: rest => rTargetNames target ++ rBoundNames rest
  | .deleteMany targets _ :: rest => targets.toList.flatMap rTargetNames ++ rBoundNames rest
  | .forStmt target _ _ _ _ :: rest => rTargetNames target ++ rBoundNames rest
  | .asyncForStmt target _ _ _ _ :: rest => rTargetNames target ++ rBoundNames rest
  | .ifStmt _ _ _ _ :: rest => rBoundNames rest
  | .whileStmt _ _ _ _ :: rest => rBoundNames rest
  | .functionDef name _ _ _ _ :: rest => name :: rBoundNames rest
  | .functionDefFull name _ _ _ _ _ _ :: rest => name :: rBoundNames rest
  | .functionDefKw name _ _ _ _ _ :: rest => name :: rBoundNames rest
  | .classDef name _ _ _ _ _ :: rest => name :: rBoundNames rest
  | .global names _ :: rest => (rBoundNames rest).filter (fun name => name ∉ names.toList)
  | .nonlocal names _ :: rest => (rBoundNames rest).filter (fun name => name ∉ names.toList)
  | _ :: rest => rBoundNames rest

def rBuildKwargs (heap : Heap) (keywords : List (String × RVal)) : Heap × RVal :=
  let entries := (keywords.map (fun pair =>
    match pair with | (name, value) => (RVal.str name, value))).toArray
  let allocated := Heap.alloc heap (.dict entries 0)
  (allocated.1, .ref allocated.2)

def rBuildDict (heap : Heap) (entries : List (RVal × RVal)) : Heap × RVal :=
  let allocated := Heap.alloc heap (.dict entries.toArray 0)
  (allocated.1, .ref allocated.2)

def rBuildList (heap : Heap) (values : List RVal) : Heap × RVal :=
  let allocated := Heap.alloc heap (.list values.toArray)
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

def rDictContains (heap : Heap) (receiver index : RVal) : Bool :=
  Option.isSome (rLookupDict heap receiver index)

def rContains (heap : Heap) (receiver index : RVal) : Bool :=
  match receiver with
  | .tuple values | .listV values => values.toList.any (fun value => value == index)
  | .ref address =>
      match heap.get? address with
      | some (.dict entries _) => entries.toList.any (fun entry => entry.1 == index)
      | some (.list values) => values.toList.any (fun value => value == index)
      | _ => false
  | _ => false

def rEqual (heap : Heap) (left right : RVal) : Bool :=
  match left, right with
  | .ref a, .ref b =>
      if a == b then true
      else
        match heap.get? a, heap.get? b with
        | some (.list xs), some (.list ys) => xs.toList == ys.toList
        | _, _ => false
  | .ref a, .listV ys =>
      match heap.get? a with
      | some (.list xs) => xs.toList == ys.toList
      | _ => false
  | .listV xs, .ref b =>
      match heap.get? b with
      | some (.list ys) => xs.toList == ys.toList
      | _ => false
  | .tuple xs, .tuple ys => xs.toList == ys.toList
  | .listV xs, .listV ys => xs.toList == ys.toList
  | _, _ => left == right

def rLookupAttribute (heap : Heap) (receiver : RVal) (attr : String) : Option RVal :=
  match receiver, attr with
  | .ref address, "get" =>
      match heap.get? address with
      | some (.dict _ _) => some (.callable ("__machine_dict_get:" ++ toString address))
      | _ => none
  | .ref address, "append" =>
      match heap.get? address with
      | some (.list _) => some (.callable ("__machine_list_append:" ++ toString address))
      | _ => none
  | .ref address, "pop" =>
      match heap.get? address with
      | some (.list _) => some (.callable ("__machine_list_pop:" ++ toString address))
      | _ => none
  | .ref address, "insert" =>
      match heap.get? address with
      | some (.list _) => some (.callable ("__machine_list_insert:" ++ toString address))
      | _ => none
  | _, _ => none

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

def rUpdateList (heap : Heap) (receiver index value : RVal) : Option Heap :=
  match receiver with
  | .ref address =>
      match heap.get? address, index with
      | some (.list values), .int position =>
          let normalized := if position < 0 then position + values.size else position
          if normalized < 0 then none
          else
            let i := normalized.toNat
            if h : i < values.size then Heap.update heap address (.list (values.set i value h))
            else none
      | _, _ => none
  | _ => none

def rListPop (heap : Heap) (receiver : RVal) : Option (Heap × RVal) :=
  match receiver with
  | .ref address =>
      match heap.get? address with
      | some (.list values) =>
          match values.toList.getLast? with
          | some value =>
              let shortened := values.extract 0 (values.size - 1)
              match Heap.update heap address (.list shortened) with
              | some updated => some (updated, value)
              | none => none
          | none => none
      | _ => none
  | _ => none

def rListInsert (heap : Heap) (receiver : RVal) (position : RVal) (value : RVal) : Option Heap :=
  match receiver, position with
  | .ref address, .int rawPosition =>
      match heap.get? address with
      | some (.list values) =>
          let length := values.size
          let position := if rawPosition < 0 then rawPosition + length else rawPosition
          let clamped : Int := if position < 0 then 0 else if position > length then length else position
          let rec insertAt : Nat → List RVal → List RVal
            | 0, rest => value :: rest
            | _, [] => [value]
            | n, head :: rest => head :: insertAt (n - 1) rest
          Heap.update heap address (.list (insertAt clamped.toNat values.toList).toArray)
      | _ => none
  | _, _ => none

def rDeleteDictEntries : List (RVal × RVal) → RVal → Option (List (RVal × RVal))
  | [], _ => none
  | (key, value) :: rest, wanted =>
      if key == wanted then some rest
      else rDeleteDictEntries rest wanted |>.map (fun tail => (key, value) :: tail)

def rDeleteSubscript (heap : Heap) (receiver index : RVal) : Option Heap :=
  match receiver with
  | .ref address =>
      match heap.get? address with
      | some (.dict entries version) =>
          rDeleteDictEntries entries.toList index |>.bind fun updated =>
            Heap.update heap address (.dict updated.toArray (version + 1))
      | some (.list values) =>
          match index with
          | .int position =>
              let normalized := if position < 0 then position + values.size else position
              if normalized < 0 then none
              else
                let i := normalized.toNat
                if h : i < values.size then
                  Heap.update heap address (.list ((values.toList.eraseIdx i).toArray))
                else none
          | _ => none
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

def rIndexHeapValue (heap : Heap) (receiver index : RVal) : Option RVal :=
  match receiver with
  | .ref address =>
      match heap.get? address with
      | some (.list values) =>
          match index with
          | .int position =>
              let length := values.size
              let normalized := if position < 0 then position + length else position
              if normalized < 0 then none
              else GetElem?.getElem? values normalized.toNat
          | _ => none
      | _ => none
  | _ => none

def rIterValues (heap : Heap) (value : RVal) : Option (List RVal) :=
  match value with
  | .tuple values | .listV values => some values.toList
  | .str text => some (text.toList.map (fun character => .str (String.ofList [character])))
  | .ref address =>
      match heap.get? address with
      | some (.list values) => some values.toList
      | _ => none
  | _ => none

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

def rLen (heap : Heap) (value : RVal) : Option RVal :=
  match value with
  | .str text => some (.int text.length)
  | .tuple values => some (.int values.size)
  | .listV values => some (.int values.size)
  | .ref address =>
      match heap.get? address with
      | some (.dict entries _) => some (.int entries.size)
      | some (.list values) => some (.int values.size)
      | _ => none
  | _ => none

def RConfig.setModules (config : RConfig) (module : String) (name : String) (value : RVal) : RConfig :=
  { config with modules := rSetModule config.modules module name value }

def rAssignedFrame (frame : RFrame) (name : String) (value : RVal)
    (remaining : List RStmt) : RFrame :=
  { control := .statements remaining
    locals := rSetEnv frame.locals name value
    globals := frame.globals
    module := frame.module
    cells := frame.cells
    completion := frame.completion
    globalNames := frame.globalNames
    nonlocalNames := frame.nonlocalNames }

def rAssignName (config : RConfig) (frame : RFrame) (name : String) (value : RVal)
    (remaining : List RStmt) : RConfig :=
  if name ∈ frame.globalNames then
    let next := config.setTop { frame with control := .statements remaining }
    next.setModules frame.module name value
  else
    match rWriteCell config.heap frame.locals name value with
    | some heap =>
        let next := { config.setTop (rCellAssignedFrame frame remaining) with heap := heap }
        if config.frames.tail.isEmpty then next.setModules frame.module name value else next
    | none =>
        match rWriteCell config.heap frame.cells name value with
        | some heap =>
            let next := { config.setTop (rCellAssignedFrame frame remaining) with heap := heap }
            if config.frames.tail.isEmpty then next.setModules frame.module name value else next
        | none =>
            let next := config.setTop (rAssignedFrame frame name value remaining)
            if config.frames.tail.isEmpty then next.setModules frame.module name value else next

def rPatternValues (target : Expr) (value : RVal) : Option (List (String × RVal)) :=
  match target, value with
  | .name name _, value => some [(name, value)]
  | .tuple targets _, .tuple values | .list targets _, .tuple values =>
      let targetList := targets.toList
      let valueList := values.toList
      if targets.size != values.size then none
      else
        (targetList.zip valueList).mapM fun pair =>
          match pair.1 with
          | .name name _ => some (name, pair.2)
          | _ => none
  | .tuple targets _, .ref _ | .list targets _, .ref _ => none
  | _, _ => none

def rUnpackPatternValues (heap : Heap) (before : Array String) (star : String)
    (after : Array String) (value : RVal) : Option (List (String × RVal)) :=
  match rIterValues heap value with
  | some valueList =>
      if valueList.length < before.size + after.size then none
      else
        let prefixValues := valueList.take before.size
        let suffixValues := valueList.drop (valueList.length - after.size)
        let middleValues := valueList.drop before.size |>.take
          (valueList.length - before.size - after.size)
        let prefixBindings := before.toList.zip prefixValues
        let suffixBindings := after.toList.zip suffixValues
        some ((star, .listV middleValues.toArray) ::
          (prefixBindings ++ suffixBindings))
  | none => none

def rAssignPattern (frame : RFrame) (target : Expr) (value : RVal) (remaining : List RStmt)
    : Option RFrame :=
  match rPatternValues target value with
  | none => none
  | some bindings =>
      let locals := bindings.foldl (fun env binding => rSetEnv env binding.1 binding.2) frame.locals
      some { frame with control := .statements remaining, locals := locals }

def rAssignUnpack (heap : Heap) (frame : RFrame) (before : Array String) (star : String)
    (after : Array String) (value : RVal) (remaining : List RStmt) : Option RFrame :=
  match rUnpackPatternValues heap before star after value with
  | none => none
  | some bindings =>
      let locals := bindings.foldl (fun env binding => rSetEnv env binding.1 binding.2) frame.locals
      some { frame with control := .statements remaining, locals := locals }

def rEvalBinOp (op : BinOp) (left right : RVal) : Res RVal :=
  match op, left, right with
  | .add, .int a, .int b => .ok (.int (a + b))
  | .add, .str a, .str b => .ok (.str (a ++ b))
  | .sub, .int a, .int b => .ok (.int (a - b))
  | .mult, .int a, .int b => .ok (.int (a * b))
  | _, _, _ => .unsupported "machine binary operator"

def rEvalCompare (heap : Heap) (op : CmpOp) (left right : RVal) : Option RVal :=
  match op with
  | .eq => some (.bool (rEqual heap left right))
  | .notEq => some (.bool (!rEqual heap left right))
  | .lt => match left, right with
      | .int a, .int b => some (.bool (a < b))
      | _, _ => none
  | .ltE => match left, right with
      | .int a, .int b => some (.bool (a ≤ b))
      | _, _ => none
  | .gt => match left, right with
      | .int a, .int b => some (.bool (a > b))
      | _, _ => none
  | .gtE => match left, right with
      | .int a, .int b => some (.bool (a ≥ b))
      | _, _ => none
  | .inOp =>
      match left with
      | .ref address =>
          if rHeapIsInstance heap address then none
          else some (.bool (rContains heap right left))
      | _ => some (.bool (rContains heap right left))
  | .notIn =>
      match left with
      | .ref address =>
          if rHeapIsInstance heap address then none
          else some (.bool (!rContains heap right left))
      | _ => some (.bool (!rContains heap right left))
  | _ => none

def rTruthy : RVal → Bool
  | .none => false
  | .bool value => value
  | .int value => value != 0
  | .float value => !Float64.isZero value
  | .str value => !value.isEmpty
  | .tuple values => !values.isEmpty
  | .listV values => !values.isEmpty
  | .ref _ => true
  | _ => true

def rEvalUnary (op : UnaryOp) (value : RVal) : Option RVal :=
  match op, value with
  | .usub, .int number => some (.int (-number))
  | .uadd, .int number => some (.int number)
  | .not, value => some (.bool (!rTruthy value))
  | _, _ => none

def rLookupFrameName (config : RConfig) (frame : RFrame) (name : String) : Option RVal :=
  let moduleValue := rLookupModule config.modules frame.module name
  let readModule := moduleValue.bind (rReadCell config.heap)
  if config.frames.tail.isEmpty then
    match readModule with
    | some value => some value
    | none => rLookupCaptured config.heap frame.locals name
  else if name ∈ frame.globalNames then readModule
  else if name ∈ frame.localNames then
    match rLookupCaptured config.heap frame.locals name with
    | some value => some value
    | none =>
        match rLookupCaptured config.heap frame.cells name with
        | some value => some value
        | none => none
  else
    match rLookupCaptured config.heap frame.locals name with
    | some value => some value
    | none =>
        match rLookupCaptured config.heap frame.cells name with
        | some value => some value
        | none =>
            match rLookupCaptured config.heap frame.globals name with
            | some value => some value
            | none => readModule

def rEvalDefaultExprIn (config : RConfig) (frame : RFrame) : Expr → Option RVal
  | .constant value _ => some (rConstValue value)
  | .name name _ => rLookupFrameName config frame name
  | .unaryOp op operand _ =>
      (rEvalDefaultExprIn config frame operand).bind (rEvalUnary op)
  | .binOp left op right _ =>
      match rEvalDefaultExprIn config frame left,
          rEvalDefaultExprIn config frame right with
      | some leftValue, some rightValue =>
          match rEvalBinOp op leftValue rightValue with
          | .ok value => some value
          | _ => none
      | _, _ => none
  | _ => none

def rEvalDefaultValuesIn (config : RConfig) (frame : RFrame) : List Expr → Option (List RVal)
  | [] => some []
  | expression :: rest =>
      match rEvalDefaultExprIn config frame expression,
          rEvalDefaultValuesIn config frame rest with
      | some value, some values => some (value :: values)
      | _, _ => none

def rEvalKeywordDefaultValuesIn (config : RConfig) (frame : RFrame) :
    List (Option Expr) → Option (List (Option RVal))
  | [] => some []
  | none :: rest =>
      (rEvalKeywordDefaultValuesIn config frame rest).map (List.cons none)
  | some expression :: rest =>
      match rEvalDefaultExprIn config frame expression,
          rEvalKeywordDefaultValuesIn config frame rest with
      | some value, some values => some (some value :: values)
      | _, _ => none

def RConfig.finish (config : RConfig) (event : REvent) : RConfig :=
  { config with frames := [], status := .finished event }

def RConfig.withChoice (config : RConfig) (choice : RChoice) : RConfig :=
  { config with choices := choice :: config.choices }

def RConfig.chooseToken (config : RConfig) (tail : List RChoice) (token : Nat) : RConfig :=
  { config with choices := tail, choiceToken := some token }

def rStartClassCall (config : RConfig) (cls : RClass) (values : List RVal)
    (keywords : List (String × RVal)) (continuation : RKont) :
    Option (RLabel × RConfig) :=
  let allocated := Heap.alloc config.heap (.instance cls.id #[])
  let instanceValue := RVal.ref allocated.2
  match rLookupClassAttr config.classes cls.id "__init__" with
  | some (.callable token) =>
      match rFunctionByToken config.functions token, config.frames with
      | some function, caller :: tail =>
          let builtKwargs :=
            if keywords.isEmpty then (allocated.1, none)
            else
              match rKeywordVariadicName function.params.toList with
              | some _ =>
                  let kwargs := rBuildKwargs allocated.1 keywords
                  (kwargs.1, some kwargs.2)
              | none => (allocated.1, none)
          match rCallFrame function (instanceValue :: values) keywords builtKwargs.2 with
          | some calleeFrame =>
              let pushed := { calleeFrame with control :=
                (.resourceChoice .framePush (.statements function.body.toList)) }
              let resumed := { caller with
                control := .continueValue instanceValue
                  (.callReturnInstance instanceValue continuation) }
              let updated := { config with heap := builtKwargs.1 }
              some (.tau, { updated with frames := pushed :: resumed :: tail })
          | none =>
              let error : RError := { errorClass := .type, args := [] }
              some (.event (.raise error), config.finish (.raise error))
      | _, _ => some (.event (.refuse "machine class constructor"),
          config.finish (.refuse "machine class constructor"))
  | some _ => some (.event (.refuse "machine class constructor"),
      config.finish (.refuse "machine class constructor"))
  | none =>
      if values.isEmpty && keywords.isEmpty then
        some (.tau, { config with heap := allocated.1 }.setControl
          (.continueValue instanceValue continuation))
      else
        let error : RError := { errorClass := .type, args := [] }
        some (.event (.raise error), config.finish (.raise error))

def rStartFunctionCall (config : RConfig) (function : RFunction) (values : List RVal)
    (keywords : List (String × RVal)) (continuation : RKont) :
    Option (RLabel × RConfig) :=
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
          let pushed := { calleeFrame with control :=
            (.resourceChoice .framePush (.statements function.body.toList)) }
          let resumed := { caller with
            control := .continueValue .none (.callReturn continuation) }
          let updated := { config with heap := builtKwargs.1 }
          some (.tau, { updated with frames := pushed :: resumed :: tail })
      | none =>
          let error : RError := { errorClass := .type, args := [] }
          some (.event (.raise error), config.finish (.raise error))
  | _ => some (.event (.refuse "machine call stack"),
      config.finish (.refuse "machine call stack"))

def rStartInstanceDunderCall (config : RConfig) (value : RVal) (attrName : String)
    (continuation : RKont) : Option (RLabel × RConfig) :=
  match value with
  | .ref address =>
      match config.heap.get? address with
      | some (.instance cls _) =>
          match rLookupClassAttr config.classes cls attrName with
          | some (.callable token) =>
              match rFunctionByToken config.functions token with
              | some function => rStartFunctionCall config function [value] [] continuation
              | none => some (.event (.refuse ("machine " ++ attrName)),
                  config.finish (.refuse ("machine " ++ attrName)))
          | some _ => some (.tau, config.setControl (.refusing ("machine " ++ attrName)))
          | none => some (.tau, config.setControl (.refusing ("machine " ++ attrName)))
      | _ => some (.tau, config.setControl (.refusing ("machine " ++ attrName)))
  | _ => some (.tau, config.setControl (.refusing ("machine " ++ attrName)))

def rStartContainsCall (config : RConfig) (op : CmpOp) (left right : RVal)
    (continuation : RKont) : Option (RLabel × RConfig) :=
  match right with
  | .ref address =>
      match config.heap.get? address with
      | some (.instance cls _) =>
          match rLookupClassAttr config.classes cls "__contains__" with
          | some (.callable token) =>
              match rFunctionByToken config.functions token with
              | some function => rStartFunctionCall config function [right, left] []
                  (.compareResult op continuation)
              | none => some (.event (.refuse "machine __contains__"),
                  config.finish (.refuse "machine __contains__"))
          | some _ => some (.tau, config.setControl (.refusing "machine __contains__"))
          | none => some (.tau, config.setControl (.refusing "machine comparison"))
      | _ =>
          match rEvalCompare config.heap op left right with
          | some result => some (.tau, config.setControl (.continueValue result continuation))
          | none => some (.tau, config.setControl (.refusing "machine comparison"))
  | _ =>
      match rEvalCompare config.heap op left right with
      | some result => some (.tau, config.setControl (.continueValue result continuation))
      | none => some (.tau, config.setControl (.refusing "machine comparison"))

def rStartCall (config : RConfig) (callee : RVal) (values : List RVal)
    (keywords : List (String × RVal)) (continuation : RKont) :
    Option (RLabel × RConfig) :=
  match callee with
  | .callable name =>
      let boundMethod := rBoundMethodInfo name
      let functionToken := match boundMethod with
        | some (token, _) => token
        | none => name
      let callValues := match boundMethod with
        | some (_, address) => (.ref address) :: values
        | none => values
      match rFunctionByToken config.functions functionToken with
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
                    match rCallFrame function callValues keywords builtKwargs.2 with
                    | some calleeFrame =>
                        let pushed := { calleeFrame with control :=
                          (.resourceChoice .framePush (.statements function.body.toList)) }
                        let resumed := { caller with
                          control := .continueValue .none (.callReturn continuation) }
                        let updated := { config with heap := builtKwargs.1 }
                        some (.tau, { updated with frames := pushed :: resumed :: tail })
                    | none =>
                        let error : RError := { errorClass := .type, args := [] }
                        some (.event (.raise error), config.finish (.raise error))
                | _ => some (.event (.refuse "machine call stack"),
                    config.finish (.refuse "machine call stack"))
      | none => if name.startsWith "__machine_dict_get:" then
        match (name.drop "__machine_dict_get:".length).toNat?, values with
        | some address, [key] =>
            let result := (rLookupDict config.heap (.ref address) key).getD .none
            some (.tau, config.setControl (.continueValue result continuation))
        | some address, [key, default] =>
            let result := (rLookupDict config.heap (.ref address) key).getD default
            some (.tau, config.setControl (.continueValue result continuation))
        | _, _ => some (.event (.refuse "machine dict.get"),
            config.finish (.refuse "machine dict.get"))
      else if name.startsWith "__machine_list_append:" then
        match (name.drop "__machine_list_append:".length).toNat?, values with
        | some address, [value] =>
            match config.heap.get? address with
            | some (.list current) =>
                match Heap.update config.heap address (.list (current.push value)) with
                | some heap => some (.tau, { config with heap := heap } |>.setControl
                    (.continueValue .none continuation))
                | none => some (.event (.refuse "machine list.append"),
                    config.finish (.refuse "machine list.append"))
            | _ => some (.event (.refuse "machine list.append"),
                config.finish (.refuse "machine list.append"))
        | _, _ => some (.event (.refuse "machine list.append"),
            config.finish (.refuse "machine list.append"))
      else if name.startsWith "__machine_list_pop:" then
        match (name.drop "__machine_list_pop:".length).toNat?, values with
        | some address, [] =>
            match rListPop config.heap (.ref address) with
            | some (heap, value) => some (.tau, { config with heap := heap } |>.setControl
                (.continueValue value continuation))
            | none => some (.event (.raise { errorClass := .index, args := [] }),
                config.finish (.raise { errorClass := .index, args := [] }))
        | _, _ => some (.event (.refuse "machine list.pop"),
            config.finish (.refuse "machine list.pop"))
      else if name.startsWith "__machine_list_insert:" then
        match (name.drop "__machine_list_insert:".length).toNat?, values with
        | some address, [position, value] =>
            match rListInsert config.heap (.ref address) position value with
            | some heap => some (.tau, { config with heap := heap } |>.setControl
                (.continueValue .none continuation))
            | none => some (.event (.refuse "machine list.insert"),
                config.finish (.refuse "machine list.insert"))
        | _, _ => some (.event (.refuse "machine list.insert"),
            config.finish (.refuse "machine list.insert"))
      else if Option.isSome (rClassByToken config.classes name) then
        match rClassByToken config.classes name with
        | some cls => rStartClassCall config cls values keywords continuation
        | none => some (.event (.refuse "machine class"),
            config.finish (.refuse "machine class"))
      else match rFunction config.functions name with
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
                  let pushed := { calleeFrame with control :=
                    (.resourceChoice .framePush (.statements function.body.toList)) }
                  let resumed := { caller with
                    control := .continueValue .none (.callReturn continuation) }
                  let updated := { config with heap := builtKwargs.1 }
                  some (.tau, { updated with frames := pushed :: resumed :: tail })
              | none =>
                  let error : RError := { errorClass := .type, args := [] }
                  some (.event (.raise error), config.finish (.raise error))
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
              match value with
              | .ref address =>
                  match config.heap.get? address with
                  | some (.instance cls _) =>
                      match rLookupClassAttr config.classes cls "__len__" with
                      | some (.callable token) =>
                          match rFunctionByToken config.functions token with
                          | some function =>
                              rStartFunctionCall config function [value] []
                                (.lenResult continuation)
                          | none => some (.event (.refuse "machine __len__"),
                              config.finish (.refuse "machine __len__"))
                      | some _ => some (.tau, config.setControl
                          (.refusing "machine __len__"))
                      | none =>
                          match rLen config.heap value with
                          | some result => some (.tau, config.setControl
                              (.continueValue result continuation))
                          | none => some (.tau, config.setControl (.refusing "machine len"))
                  | _ =>
                      match rLen config.heap value with
                      | some result => some (.tau, config.setControl
                          (.continueValue result continuation))
                      | none => some (.tau, config.setControl (.refusing "machine len"))
              | _ =>
                  match rLen config.heap value with
                  | some result => some (.tau, config.setControl (.continueValue result continuation))
                  | none => some (.tau, config.setControl (.refusing "machine len"))
            | _ => some (.tau, config.setControl (.refusing "machine len"))
          else if name == "repr" then
            match values with
            | [value] =>
                match value with
                | .ref address =>
                    match config.heap.get? address with
                    | some (.instance cls _) =>
                        match rLookupClassAttr config.classes cls "__repr__" with
                        | some (.callable token) =>
                            match rFunctionByToken config.functions token with
                            | some function =>
                                rStartFunctionCall config function [value] []
                                  (.reprResult continuation)
                            | none => some (.event (.refuse "machine __repr__"),
                                config.finish (.refuse "machine __repr__"))
                        | some _ => some (.tau, config.setControl
                            (.refusing "machine __repr__"))
                        | none => some (.tau, config.setControl
                            (.refusing "machine repr"))
                    | _ => some (.tau, config.setControl (.refusing "machine repr"))
                | _ => some (.tau, config.setControl (.refusing "machine repr"))
            | _ => some (.tau, config.setControl (.refusing "machine repr"))
          else if name == "str" then
            match values with
            | [value] => rStartInstanceDunderCall config value "__str__"
                (.strResult continuation)
            | _ => some (.tau, config.setControl (.refusing "machine str"))
          else if name == "abs" then
            match values with
            | [value] => rStartInstanceDunderCall config value "__abs__"
                (.absResult continuation)
            | _ => some (.tau, config.setControl (.refusing "machine abs"))
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
  | allocateListProceed {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {values : List RVal} {continuation : RKont}
      (hframes : config.frames = { frame with control := .allocateList values continuation } :: tail) :
      Step config .tau
        (let allocated := rBuildList config.heap values
         let updated := { config with heap := allocated.1 }
         { updated with frames := frame :: tail } |>.setControl
           (.continueValue allocated.2 continuation))
  | allocateDictProceed {config : RConfig} {frame : RFrame} {tail : List RFrame}
      {entries : List (RVal × RVal)} {continuation : RKont}
      (hframes : config.frames = { frame with control := .allocateDict entries continuation } :: tail) :
      Step config .tau
        (let allocated := rBuildDict config.heap entries
         let updated := { config with heap := allocated.1 }
         { updated with frames := frame :: tail } |>.setControl
           (.continueValue allocated.2 continuation))
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
      | .allocateList values continuation =>
          let allocated := rBuildList config.heap values
          some (.tau, { config with heap := allocated.1 } |>.setControl
            (.continueValue allocated.2 continuation))
      | .allocateDict entries continuation =>
          let allocated := rBuildDict config.heap entries
          some (.tau, { config with heap := allocated.1 } |>.setControl
            (.continueValue allocated.2 continuation))
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
      | .allocateList values continuation =>
          let allocated := rBuildList config.heap values
          some (.tau, { config with heap := allocated.1 } |>.setControl
            (.continueValue allocated.2 continuation))
      | .allocateDict entries continuation =>
          let allocated := rBuildDict config.heap entries
          some (.tau, { config with heap := allocated.1 } |>.setControl
            (.continueValue allocated.2 continuation))
      | .statements [] =>
          match frame.completion with
          | some continuation =>
              some (.tau, config.setTop
                { frame with control := .continueValue .none continuation, completion := none })
          | none =>
              if config.frames.tail.isEmpty then
                some (.event (.return .none), config.finish (.return .none))
              else some (.tau, config.setControl (.continueValue .none .returnValue))
      | .statements (stmt :: rest) =>
          match stmt with
          | .pass _ => some (.tau, config.setControl (.statements rest))
          | .expr expression _ =>
              some (.tau, config.setControl (.evaluate expression (.sequence rest)))
          | .exprRaw _ _ =>
              some (.event (.refuse "machine raw expression"),
                config.finish (.refuse "machine raw expression"))
          | .raw kind _ _ =>
              some (.event (.refuse ("machine raw statement: " ++ kind)),
                config.finish (.refuse ("machine raw statement: " ++ kind)))
          | .assign (.name name _) value _ =>
              some (.tau, config.setControl (.evaluate value (.assign name rest)))
          | .assign (.subscript receiver index _) value _ =>
              some (.tau, config.setControl
                (.evaluate value (.assignSubscriptReceiver receiver index rest)))
          | .assign (.attribute receiver attr _) value _ =>
              some (.tau, config.setControl
                (.evaluate value (.assignAttributeReceiver receiver attr rest)))
          | .unpackAssign before star after value _ =>
              some (.tau, config.setControl
                (.evaluate value (.assignUnpack before star after rest)))
          | .augAssign (.name name span) op value _ =>
              some (.tau, config.setControl
                (.evaluate (.name name span)
                  (.augAssignLeft name op value rest)))
          | .augAssign (.attribute receiver attr _) op value _ =>
              some (.tau, config.setControl
                (.evaluate receiver (.augAssignAttributeReceiver attr op value rest)))
          | .augAssign _ _ _ _ =>
              some (.event (.refuse "machine augmented assignment target"),
                config.finish (.refuse "machine augmented assignment target"))
          | .delete (.name name _) _ =>
              if !config.frames.tail.isEmpty && name ∈ frame.localNames
                  && name ∉ frame.globalNames && name ∉ frame.nonlocalNames then
                match rDeleteEnv frame.locals name with
                | some locals =>
                    let updated := { frame with control := .statements rest, locals := locals }
                    some (.tau, config.setTop updated)
                | none =>
                    let error : RError := { errorClass := .unboundLocal, args := [] }
                    some (.event (.raise error), config.finish (.raise error))
              else if config.functions.any (fun function => function.name == name) then
                some (.event (.refuse "machine delete function"),
                  config.finish (.refuse "machine delete function"))
              else
                let locals := (rDeleteEnv frame.locals name).getD frame.locals
                match rDeleteModule config.modules frame.module name with
                | some modules =>
                    let next := config.setTop
                      { frame with control := .statements rest, locals := locals }
                    some (.tau, { next with modules := modules })
                | none => some (.tau, config.setControl (.refusing "machine delete name"))
          | .delete _ _ =>
              match stmt with
              | .delete (.subscript receiver index _) _ =>
                  some (.tau, config.setControl
                    (.evaluate receiver (.deleteSubscriptReceiver index rest)))
              | .delete (.attribute receiver attr _) _ =>
                  some (.tau, config.setControl
                    (.evaluate receiver (.deleteAttributeReceiver attr rest)))
              | _ => some (.event (.refuse "machine delete target"),
                  config.finish (.refuse "machine delete target"))
          | .deleteMany _ _ =>
              some (.event (.refuse "machine delete target"),
                config.finish (.refuse "machine delete target"))
          | .raise _ _ _ =>
              some (.event (.refuse "machine raise"), config.finish (.refuse "machine raise"))
          | .assertStmt _ _ _ =>
              some (.event (.refuse "machine assert"), config.finish (.refuse "machine assert"))
          | .yieldStmt _ _ =>
              some (.event (.refuse "machine yield"), config.finish (.refuse "machine yield"))
          | .yieldFrom _ _ =>
              some (.event (.refuse "machine yield-from"),
                config.finish (.refuse "machine yield-from"))
          | .brk _ =>
              some (.event (.refuse "machine break"), config.finish (.refuse "machine break"))
          | .cont _ =>
              some (.event (.refuse "machine continue"), config.finish (.refuse "machine continue"))
          | .import _ _ _ =>
              some (.event (.refuse "machine import"), config.finish (.refuse "machine import"))
          | .importMany _ _ =>
              some (.event (.refuse "machine import"), config.finish (.refuse "machine import"))
          | .importFrom _ _ _ _ =>
              some (.event (.refuse "machine import-from"), config.finish (.refuse "machine import-from"))
          | .classDef _ _ _ _ _ _ =>
              match stmt with
              | .classDef name bases keywords decorators body _ =>
                  if keywords.isEmpty && decorators.isEmpty
                      && rClassBodySupported body.toList then
                    match bases.toList with
                    | [] =>
                        match config.frames with
                        | _ :: tail =>
                            let classFrame : RFrame :=
                              { control := .statements body.toList
                                locals := (rClassDoc body.toList).map (fun value => ("__doc__", value))
                                  |>.toList
                                globals := frame.globals
                                module := frame.module
                                completion := some (.classDef name #[] rest)
                                globalNames := []
                                nonlocalNames := []
                                localNames := [] }
                            some (.tau, { config with frames := classFrame :: frame :: tail })
                        | [] => none
                    | first :: restBases =>
                        some (.tau, config.setControl
                          (.evaluate first (.classDefBases name body.toList rest restBases [])))
                  else
                    some (.event (.refuse "machine class"),
                      config.finish (.refuse "machine class"))
              | _ => some (.event (.refuse "machine class"),
                  config.finish (.refuse "machine class"))
          | .withStmt _ _ _ _ =>
              some (.event (.refuse "machine with"), config.finish (.refuse "machine with"))
          | .tryStmt _ _ _ _ _ =>
              some (.event (.refuse "machine try"), config.finish (.refuse "machine try"))
          | .assignMany _ _ _ =>
              some (.event (.refuse "machine multiple-target assignment"),
                config.finish (.refuse "machine multiple-target assignment"))
          | .annAssign _ _ _ _ _ =>
              some (.event (.refuse "machine annotated assignment"),
                config.finish (.refuse "machine annotated assignment"))
          | .functionDefFull _ _ _ _ _ _ _ =>
              some (.event (.refuse "machine function metadata"),
                config.finish (.refuse "machine function metadata"))
          | .assign target value _ =>
              some (.tau, config.setControl (.evaluate value (.assignPattern target rest)))
          | .ifStmt test body orelse _ =>
              some (.tau, config.setControl
                (.evaluate test (.ifBranch body.toList orelse.toList rest)))
          | .whileStmt test body orelse span =>
              some (.tau, config.setControl
                (.evaluate test (.whileBranch test body.toList orelse.toList rest span)))
          | .forStmt target iter body orelse _ =>
              some (.tau, config.setControl
                (.evaluate iter (.forIter target body.toList orelse.toList rest)))
          | .asyncForStmt _ _ _ _ _ =>
              some (.event (.refuse "machine async-for"),
                config.finish (.refuse "machine async-for"))
          | .global names _ =>
              let updated := { frame with control := .statements rest }
              some (.tau, config.setTop { updated with
                globalNames := names.toList ++ frame.globalNames })
          | .nonlocal names _ =>
              let updated := { frame with control := .statements rest }
              some (.tau, config.setTop { updated with
                nonlocalNames := names.toList ++ frame.nonlocalNames })
          | .functionDef name params defaults body span =>
              match config.frames with
              | current :: tail =>
                  match rEvalDefaultValuesIn config current defaults.toList with
                  | none => some (.event (.refuse "machine default expression"),
                      config.finish (.refuse "machine default expression"))
                  | some defaultValues =>
                      let defaultValues := defaultValues.toArray
                      let inClass := match current.completion with
                        | some (.classDef _ _ _) => true
                        | _ => false
                      let captured :=
                        if inClass || tail.isEmpty then (config.heap, current, [])
                        else rCaptureLocals config.heap current
                      let capturedFrame := captured.2.1
                      let scopeNames := rScopeNames body.toList
                      let function :=
                        { id := config.nextFunctionId, name := name, params := params, defaults := defaults,
                          defaultValues := defaultValues, keywordDefaultValues := #[], body := body,
                          globals := current.module, captured := captured.2.2,
                          globalNames := scopeNames.1, nonlocalNames := scopeNames.2,
                          localNames := (rBoundNames body.toList).filter
                            (fun name => name ∉ scopeNames.1 && name ∉ scopeNames.2) }
                      let defined :=
                        if inClass then config.defineMethod current tail function rest
                        else config.defineFunction capturedFrame tail function rest
                      some (.tau, { defined with heap := captured.1 })
              | [] => none
          | .functionDefKw name params defaults keywordDefaults body span =>
              match config.frames with
              | current :: tail =>
                  match rEvalDefaultValuesIn config current defaults.toList,
                      rEvalKeywordDefaultValuesIn config current keywordDefaults.toList with
                  | some defaultValues, some keywordDefaultValues =>
                      let defaultValues := defaultValues.toArray
                      let inClass := match current.completion with
                        | some (.classDef _ _ _) => true
                        | _ => false
                      let captured :=
                        if inClass || tail.isEmpty then (config.heap, current, [])
                        else rCaptureLocals config.heap current
                      let capturedFrame := captured.2.1
                      let scopeNames := rScopeNames body.toList
                      let function :=
                        { id := config.nextFunctionId, name := name, params := params, defaults := defaults,
                          defaultValues := defaultValues,
                          keywordDefaultValues := keywordDefaultValues.toArray,
                          body := body, globals := current.module, captured := captured.2.2,
                          globalNames := scopeNames.1, nonlocalNames := scopeNames.2,
                          localNames := (rBoundNames body.toList).filter
                            (fun name => name ∉ scopeNames.1 && name ∉ scopeNames.2) }
                      let defined :=
                        if inClass then config.defineMethod current tail function rest
                        else config.defineFunction capturedFrame tail function rest
                      some (.tau, { defined with heap := captured.1 })
                  | _, _ => some (.event (.refuse "machine default expression"),
                      config.finish (.refuse "machine default expression"))
              | [] => none
          | .ret none _ => some (.tau, config.setControl (.continueValue .none .returnValue))
          | .ret (some expression) _ =>
              some (.tau, config.setControl (.evaluate expression .returnValue))
          | .unsupported _ text _ =>
              some (.event (.refuse text), config.finish (.refuse text))
      | .evaluate (.constant value _) continuation =>
          some (.tau, config.setControl (.continueValue (rConstValue value) continuation))
      | .evaluate (.name name _) continuation =>
          match rLookupFrameName config frame name with
          | some value => some (.tau, config.setControl (.continueValue value continuation))
          | none =>
              if !config.frames.tail.isEmpty && name ∈ frame.localNames
                  && name ∉ frame.globalNames && name ∉ frame.nonlocalNames then
                let error : RError := { errorClass := .unboundLocal, args := [] }
                some (.event (.raise error), config.finish (.raise error))
              else
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
      | .evaluate (.attribute value attr _) continuation =>
          some (.tau, config.setControl (.evaluate value (.attributeValue attr continuation)))
      | .evaluate (.compare left #[op] #[right] _) continuation =>
          some (.tau, config.setControl (.evaluate left (.compareLeft op right continuation)))
      | .evaluate (.tuple elements _) continuation =>
          match elements.toList with
          | [] => some (.tau, config.setControl (.continueValue (.tuple #[]) continuation))
          | first :: rest =>
              some (.tau, config.setControl
                (.evaluate first (.tupleElements rest [] continuation)))
      | .evaluate (.list elements _) continuation =>
          match elements.toList with
          | [] =>
              some (.tau, config.setControl
                (.resourceChoice .allocation (.allocateList [] continuation)))
          | first :: rest =>
              some (.tau, config.setControl
                (.evaluate first (.listElements rest [] continuation)))
      | .evaluate (.dict keys values _) continuation =>
          let pairs := keys.toList.zip values.toList
          match pairs with
          | [] =>
              some (.tau, config.setControl
                (.resourceChoice .allocation (.allocateDict [] continuation)))
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
              | .continueValue _ (.callReturnInstance instanceValue continuation) =>
                  if value == .none then
                    some (.tau, { config with frames :=
                      { caller with control := .continueValue instanceValue continuation } :: tail })
                  else
                    let error : RError := { errorClass := .type, args := [] }
                    some (.event (.raise error), config.finish (.raise error))
              | _ => some (.event (.refuse "machine call stack"),
                  config.finish (.refuse "machine call stack"))
          | [_] => some (.event (.return value), config.finish (.return value))
          | [] => none
      | .continueValue _ .discardValue => some (.tau, config.setControl (.statements []))
      | .continueValue value (.lenResult continuation) =>
          match value with
          | .int length =>
              if length < 0 then some (.tau, config.setControl
                (.refusing "machine __len__ result"))
              else some (.tau, config.setControl (.continueValue value continuation))
          | _ => some (.tau, config.setControl (.refusing "machine __len__ result"))
      | .continueValue value (.reprResult continuation) =>
          match value with
          | .str _ => some (.tau, config.setControl (.continueValue value continuation))
          | _ => some (.tau, config.setControl (.refusing "machine __repr__ result"))
      | .continueValue value (.strResult continuation) =>
          match value with
          | .str _ => some (.tau, config.setControl (.continueValue value continuation))
          | _ => some (.tau, config.setControl (.refusing "machine __str__ result"))
      | .continueValue value (.absResult continuation) =>
          match value with
          | .int _ => some (.tau, config.setControl (.continueValue value continuation))
          | _ => some (.tau, config.setControl (.refusing "machine __abs__ result"))
      | .continueValue value (.sequence remaining) =>
          some (.tau, config.setControl (.statements remaining))
      | .continueValue _ (.classDef name bases remaining) =>
          match config.frames with
          | classFrame :: tail =>
              match rFinishClass config classFrame tail name bases remaining with
              | some next => some (.tau, next)
              | none => some (.event (.refuse "machine class stack"),
                  config.finish (.refuse "machine class stack"))
          | [] => none
      | .continueValue value (.classDefBases name body remaining baseExpressions baseValues) =>
          match baseExpressions with
          | nextBase :: restBases =>
              some (.tau, config.setControl
                (.evaluate nextBase (.classDefBases name body remaining restBases
                  (baseValues ++ [value]))))
          | [] =>
              match rDirectBaseIds config.classes (baseValues ++ [value]), config.frames with
              | some baseIds, caller :: tail =>
                  let classFrame : RFrame :=
                    { control := .statements body
                      locals := (rClassDoc body).map (fun value => ("__doc__", value)) |>.toList
                      globals := caller.globals
                      module := caller.module
                      completion := some (.classDef name baseIds remaining)
                      globalNames := []
                      nonlocalNames := []
                      localNames := [] }
                  some (.tau, { config with frames := classFrame :: caller :: tail })
              | _, _ => some (.event (.refuse "machine class"),
                  config.finish (.refuse "machine class"))
      | .continueValue value (.assignSubscriptReceiver receiver index remaining) =>
          some (.tau, config.setControl
            (.evaluate receiver (.assignSubscriptIndex value index remaining)))
      | .continueValue receiver (.assignSubscriptIndex originalValue index remaining) =>
          some (.tau, config.setControl
            (.evaluate index (.assignSubscriptDone receiver originalValue remaining)))
      | .continueValue originalValue (.assignAttributeReceiver receiver attr remaining) =>
          some (.tau, config.setControl
            (.evaluate receiver (.assignAttributeValue attr originalValue remaining)))
      | .continueValue index (.assignSubscriptDone receiver value remaining) =>
          match receiver with
          | .ref address =>
              match config.heap.get? address with
              | some (.instance cls _) =>
                  match rLookupClassAttr config.classes cls "__setitem__" with
                  | some (.callable token) =>
                      match rFunctionByToken config.functions token with
                      | some function =>
                          rStartFunctionCall config function [receiver, index, value] []
                            (.setitemResult remaining)
                      | none => some (.event (.refuse "machine __setitem__"),
                          config.finish (.refuse "machine __setitem__"))
                  | some _ => some (.tau, config.setControl
                      (.refusing "machine __setitem__"))
                  | none => some (.tau, config.setControl
                      (.refusing "machine subscript assignment"))
              | _ =>
                  match rUpdateDict config.heap receiver index value with
                  | some heap => some (.tau, { config with heap := heap }.setControl
                      (.statements remaining))
                  | none =>
                      match rUpdateList config.heap receiver index value with
                      | some heap => some (.tau, { config with heap := heap }.setControl
                          (.statements remaining))
                      | none => some (.tau, config.setControl
                          (.refusing "machine subscript assignment"))
          | _ =>
            match rUpdateDict config.heap receiver index value with
          | some heap => some (.tau, { config with heap := heap }.setControl (.statements remaining))
          | none =>
              match rUpdateList config.heap receiver index value with
              | some heap => some (.tau, { config with heap := heap }.setControl (.statements remaining))
              | none => some (.tau, config.setControl (.refusing "machine subscript assignment"))
      | .continueValue _ (.setitemResult remaining) =>
          some (.tau, config.setControl (.statements remaining))
      | .continueValue receiver (.assignAttributeValue attr value remaining) =>
          match receiver with
          | .ref address =>
              if rHeapIsInstance config.heap address then
                match rUpdateInstanceAttr config.heap address attr value with
                | some heap =>
                    some (.tau, { config with heap := heap }.setControl
                      (.statements remaining))
                | none =>
                    let error : RError := { errorClass := .attribute, args := [] }
                    some (.event (.raise error), config.finish (.raise error))
              else some (.tau, config.setControl (.refusing "machine attribute assignment"))
          | .callable token =>
              match rUpdateClassAttr config.classes token attr value with
              | some classes =>
                  some (.tau, { config with classes := classes }.setControl
                    (.statements remaining))
              | none => some (.tau, config.setControl (.refusing "machine attribute assignment"))
          | _ =>
              let error : RError := { errorClass := .attribute, args := [] }
              some (.event (.raise error), config.finish (.raise error))
      | .continueValue receiver (.deleteAttributeReceiver attr remaining) =>
          match receiver with
          | .ref address =>
              if rHeapIsInstance config.heap address then
                match rDeleteInstanceAttr config.heap address attr with
                | some heap =>
                    some (.tau, { config with heap := heap }.setControl
                      (.statements remaining))
                | none =>
                    let error : RError := { errorClass := .attribute, args := [] }
                    some (.event (.raise error), config.finish (.raise error))
              else
                some (.tau, config.setControl (.refusing "machine attribute deletion"))
          | .callable token =>
              match rDeleteClassAttr config.classes token attr with
              | some classes =>
                  some (.tau, { config with classes := classes }.setControl
                    (.statements remaining))
              | none =>
                  let error : RError := { errorClass := .attribute, args := [] }
                  some (.event (.raise error), config.finish (.raise error))
          | _ =>
              let error : RError := { errorClass := .attribute, args := [] }
              some (.event (.raise error), config.finish (.raise error))
      | .continueValue receiver (.deleteSubscriptReceiver index remaining) =>
          some (.tau, config.setControl (.evaluate index (.deleteSubscriptIndex receiver remaining)))
      | .continueValue index (.deleteSubscriptIndex receiver remaining) =>
          match rDeleteSubscript config.heap receiver index with
          | some heap => some (.tau, { config with heap := heap }.setControl (.statements remaining))
          | none => some (.tau, config.setControl (.refusing "machine subscript deletion"))
      | .continueValue value (.assign name remaining) =>
          some (.tau, rAssignName config frame name value remaining)
      | .continueValue value (.assignPattern target remaining) =>
          match rAssignPattern frame target value remaining with
          | some updated => some (.tau, config.setTop updated)
          | none => some (.tau, config.setControl (.refusing "machine assignment pattern"))
      | .continueValue value (.assignUnpack before star after remaining) =>
          match rAssignUnpack config.heap frame before star after value remaining with
          | some updated => some (.tau, config.setTop updated)
          | none => some (.tau, config.setControl (.refusing "machine starred assignment"))
      | .continueValue left (.augAssignLeft name op value remaining) =>
          some (.tau, config.setControl (.evaluate value (.augAssignRight left name op remaining)))
      | .continueValue right (.augAssignRight left name op remaining) =>
          match rEvalBinOp op left right with
          | .ok result =>
              some (.tau, rAssignName config frame name result remaining)
          | .exn _ => some (.tau, config.setControl (.refusing "machine augmented assignment"))
          | .unsupported reason => some (.tau, config.setControl (.refusing reason))
          | .timeout => some (.tau, config.setControl (.refusing "machine augmented assignment"))
      | .continueValue receiver (.augAssignAttributeReceiver attr op value remaining) =>
          match receiver with
          | .callable token =>
              match rClassByToken config.classes token with
              | some cls =>
                  match rLookupClassAttr config.classes cls.id attr with
                  | some left => some (.tau, config.setControl
                      (.continueValue left
                        (.augAssignAttributeValue receiver attr op value remaining)))
                  | none =>
                      let error : RError := { errorClass := .attribute, args := [] }
                      some (.event (.raise error), config.finish (.raise error))
              | none =>
                  let error : RError := { errorClass := .attribute, args := [] }
                  some (.event (.raise error), config.finish (.raise error))
          | .ref address =>
              if rHeapIsInstance config.heap address then
                match rLookupInstanceClassAttr config.heap config.classes address attr with
                | some left => some (.tau, config.setControl
                    (.continueValue left
                      (.augAssignAttributeValue receiver attr op value remaining)))
                | none =>
                    let error : RError := { errorClass := .attribute, args := [] }
                    some (.event (.raise error), config.finish (.raise error))
              else
                let error : RError := { errorClass := .attribute, args := [] }
                some (.event (.raise error), config.finish (.raise error))
          | _ =>
              let error : RError := { errorClass := .attribute, args := [] }
              some (.event (.raise error), config.finish (.raise error))
      | .continueValue left (.augAssignAttributeValue receiver attr op value remaining) =>
          some (.tau, config.setControl
            (.evaluate value (.augAssignAttributeRight receiver attr left op remaining)))
      | .continueValue right (.augAssignAttributeRight receiver attr left op remaining) =>
          match rEvalBinOp op left right with
          | .ok result =>
              match receiver with
              | .callable token =>
                  match rUpdateClassAttr config.classes token attr result with
                  | some classes =>
                      some (.tau, { config with classes := classes }.setControl
                        (.statements remaining))
                  | none => some (.tau, config.setControl
                      (.refusing "machine augmented attribute assignment"))
              | .ref address =>
                  if rHeapIsInstance config.heap address then
                    match rUpdateInstanceAttr config.heap address attr result with
                    | some heap => some (.tau, { config with heap := heap }.setControl
                        (.statements remaining))
                    | none => some (.tau, config.setControl
                        (.refusing "machine augmented attribute assignment"))
                  else some (.tau, config.setControl
                    (.refusing "machine augmented attribute assignment"))
              | _ => some (.tau, config.setControl
                  (.refusing "machine augmented attribute assignment"))
          | .exn _ => some (.tau, config.setControl (.refusing "machine augmented assignment"))
          | .unsupported reason => some (.tau, config.setControl (.refusing reason))
          | .timeout => some (.tau, config.setControl (.refusing "machine augmented assignment"))
      | .continueValue value (.binOpLeft op right continuation) =>
          some (.tau, config.setControl (.evaluate right (.binOpRight value op continuation)))
      | .continueValue value (.unaryValue op continuation) =>
          match op, value with
          | .usub, .ref address =>
              match config.heap.get? address with
              | some (.instance cls _) =>
                  match rLookupClassAttr config.classes cls "__neg__" with
                  | some (.callable token) =>
                      match rFunctionByToken config.functions token with
                      | some function => rStartFunctionCall config function [value] []
                          (.unaryResult continuation)
                      | none => some (.event (.refuse "machine unary dunder"),
                          config.finish (.refuse "machine unary dunder"))
                  | some _ => some (.tau, config.setControl (.refusing "machine unary dunder"))
                  | none => some (.tau, config.setControl (.refusing "machine unary operator"))
              | _ => some (.tau, config.setControl (.refusing "machine unary operator"))
          | .uadd, .ref address =>
              match config.heap.get? address with
              | some (.instance cls _) =>
                  match rLookupClassAttr config.classes cls "__pos__" with
                  | some (.callable token) =>
                      match rFunctionByToken config.functions token with
                      | some function => rStartFunctionCall config function [value] []
                          (.unaryResult continuation)
                      | none => some (.event (.refuse "machine unary dunder"),
                          config.finish (.refuse "machine unary dunder"))
                  | some _ => some (.tau, config.setControl (.refusing "machine unary dunder"))
                  | none => some (.tau, config.setControl (.refusing "machine unary operator"))
              | _ => some (.tau, config.setControl (.refusing "machine unary operator"))
          | _, _ =>
              match rEvalUnary op value with
              | some result => some (.tau, config.setControl (.continueValue result continuation))
              | none => some (.tau, config.setControl (.refusing "machine unary operator"))
      | .continueValue value (.unaryResult continuation) =>
          some (.tau, config.setControl (.continueValue value continuation))
      | .continueValue receiver (.subscriptValue index continuation) =>
          some (.tau, config.setControl (.evaluate index (.subscriptIndex receiver continuation)))
      | .continueValue receiver (.attributeValue attr continuation) =>
          match rLookupAttribute config.heap receiver attr with
          | some value => some (.tau, config.setControl (.continueValue value continuation))
          | none =>
              match receiver with
              | .ref address =>
                  if rHeapIsInstance config.heap address then
                    match rLookupInstanceAttr config.heap address attr with
                    | some value =>
                        some (.tau, config.setControl (.continueValue value continuation))
                    | none =>
                        match config.heap.get? address with
                        | some (.instance cls _) =>
                            match rClassById config.classes cls with
                            | some classValue =>
                                match rLookupClassAttr config.classes classValue.id attr with
                                | some (.callable token) =>
                                    let bound := rBoundMethodToken token address
                                    some (.tau, config.setControl
                                      (.continueValue (.callable bound) continuation))
                                | some value =>
                                    some (.tau, config.setControl
                                      (.continueValue value continuation))
                                | none =>
                                    let error : RError := { errorClass := .attribute, args := [] }
                                    some (.event (.raise error), config.finish (.raise error))
                            | none =>
                                let error : RError := { errorClass := .attribute, args := [] }
                                some (.event (.raise error), config.finish (.raise error))
                        | _ =>
                            let error : RError := { errorClass := .attribute, args := [] }
                            some (.event (.raise error), config.finish (.raise error))
                  else some (.tau, config.setControl (.refusing "machine attribute"))
              | .callable token =>
                  match rClassByToken config.classes token with
                  | some cls =>
                      match rLookupClassAttr config.classes cls.id attr with
                      | some value =>
                          some (.tau, config.setControl (.continueValue value continuation))
                      | none =>
                          let error : RError := { errorClass := .attribute, args := [] }
                          some (.event (.raise error), config.finish (.raise error))
                  | none => some (.tau, config.setControl (.refusing "machine attribute"))
              | _ => some (.tau, config.setControl (.refusing "machine attribute"))
      | .continueValue left (.compareLeft op right continuation) =>
          some (.tau, config.setControl (.evaluate right (.compareRight left op continuation)))
      | .continueValue right (.compareRight left op continuation) =>
          if op == .inOp || op == .notIn then
            rStartContainsCall config op left right continuation
          else
            match rEvalCompare config.heap op left right with
            | some value => some (.tau, config.setControl (.continueValue value continuation))
            | none => some (.tau, config.setControl (.refusing "machine comparison"))
      | .continueValue value (.compareResult op continuation) =>
          match value with
          | .bool result =>
              some (.tau, config.setControl (.continueValue
                (if result then .bool (op == .inOp) else .bool (op != .inOp)) continuation))
          | _ => some (.tau, config.setControl (.refusing "machine __contains__ result"))
      | .continueValue value (.ifBranch body orelse remaining) =>
          let selected := if rTruthy value then body else orelse
          some (.tau, config.setControl (.statements (selected ++ remaining)))
      | .continueValue value (.whileBranch test body orelse remaining span) =>
          if rTruthy value then
            some (.tau, config.setControl
              (.statements (body ++ [.whileStmt test body.toArray orelse.toArray span] ++ remaining)))
          else
            some (.tau, config.setControl (.statements (orelse ++ remaining)))
      | .continueValue value (.forIter target body orelse remaining) =>
          match rIterValues config.heap value with
          | some values =>
              some (.tau, config.setControl
                (.continueValue .none (.forNext target values body orelse remaining)))
          | none => some (.tau, config.setControl (.refusing "machine for iterable"))
      | .continueValue value (.forNext target values body orelse remaining) =>
          match values with
          | [] => some (.tau, config.setControl (.statements (orelse ++ remaining)))
          | next :: restValues =>
              match rPatternValues target next with
              | some bindings =>
                  let locals := bindings.foldl
                    (fun env binding => rSetEnv env binding.1 binding.2) frame.locals
                  some (.tau, config.setTop { frame with
                    control := .statements body,
                    locals := locals,
                    completion := some (.forNext target restValues body orelse remaining) })
              | none => some (.tau, config.setControl (.refusing "machine for target"))
      | .continueValue value (.ifExpression body orelse continuation) =>
          some (.tau, config.setControl
            (.evaluate (if rTruthy value then body else orelse) continuation))
      | .continueValue index (.subscriptIndex receiver continuation) =>
          match receiver with
          | .ref address =>
              match config.heap.get? address with
              | some (.instance cls _) =>
                  match rLookupClassAttr config.classes cls "__getitem__" with
                  | some (.callable token) =>
                      match rFunctionByToken config.functions token with
                      | some function =>
                          rStartFunctionCall config function [receiver, index] []
                            (.subscriptResult continuation)
                      | none => some (.event (.refuse "machine __getitem__"),
                          config.finish (.refuse "machine __getitem__"))
                  | some _ => some (.tau, config.setControl
                      (.refusing "machine __getitem__"))
                  | none => some (.tau, config.setControl
                      (.refusing "machine subscript"))
              | _ =>
                  match rLookupDict config.heap receiver index with
                  | some value => some (.tau, config.setControl (.continueValue value continuation))
                  | none =>
                      match rIndexHeapValue config.heap receiver index with
                      | some value => some (.tau, config.setControl (.continueValue value continuation))
                      | none =>
                          match rIndexValue receiver index with
                          | some value => some (.tau, config.setControl (.continueValue value continuation))
                          | none => some (.tau, config.setControl (.refusing "machine subscript"))
          | _ =>
            match rLookupDict config.heap receiver index with
          | some value => some (.tau, config.setControl (.continueValue value continuation))
          | none =>
              match rIndexHeapValue config.heap receiver index with
              | some value => some (.tau, config.setControl (.continueValue value continuation))
              | none =>
                  match rIndexValue receiver index with
                  | some value => some (.tau, config.setControl (.continueValue value continuation))
                  | none =>
                      match receiver, index with
                      | .tuple _, (.int _) | .listV _, (.int _) | .ref _, (.int _) =>
                          some (.event (.raise { errorClass := .index, args := [] }),
                            config.finish (.raise { errorClass := .index, args := [] }))
                      | _, _ => some (.tau, config.setControl (.refusing "machine subscript"))
      | .continueValue value (.subscriptResult continuation) =>
          some (.tau, config.setControl (.continueValue value continuation))
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
                (.resourceChoice .allocation
                  (.allocateList (values ++ [value]) continuation)))
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
              some (.tau, config.setControl
                (.resourceChoice .allocation (.allocateDict updated continuation)))
      | .continueValue right (.binOpRight left op continuation) =>
          match op, left with
          | .add, .ref address =>
              match config.heap.get? address with
              | some (.instance cls _) =>
                  match rLookupClassAttr config.classes cls "__add__" with
                  | some (.callable token) =>
                      match rFunctionByToken config.functions token with
                      | some function => rStartFunctionCall config function [left, right] []
                          (.binaryResult continuation)
                      | none => some (.event (.refuse "machine __add__"),
                          config.finish (.refuse "machine __add__"))
                  | some _ => some (.tau, config.setControl (.refusing "machine __add__"))
                  | none => some (.tau, config.setControl (.refusing "machine binary operator"))
              | _ => some (.tau, config.setControl (.refusing "machine binary operator"))
          | .sub, .ref address =>
              match config.heap.get? address with
              | some (.instance cls _) =>
                  match rLookupClassAttr config.classes cls "__sub__" with
                  | some (.callable token) =>
                      match rFunctionByToken config.functions token with
                      | some function => rStartFunctionCall config function [left, right] []
                          (.binaryResult continuation)
                      | none => some (.event (.refuse "machine __sub__"),
                          config.finish (.refuse "machine __sub__"))
                  | some _ => some (.tau, config.setControl (.refusing "machine __sub__"))
                  | none => some (.tau, config.setControl (.refusing "machine binary operator"))
              | _ => some (.tau, config.setControl (.refusing "machine binary operator"))
          | .mult, .ref address =>
              match config.heap.get? address with
              | some (.instance cls _) =>
                  match rLookupClassAttr config.classes cls "__mul__" with
                  | some (.callable token) =>
                      match rFunctionByToken config.functions token with
                      | some function => rStartFunctionCall config function [left, right] []
                          (.binaryResult continuation)
                      | none => some (.event (.refuse "machine __mul__"),
                          config.finish (.refuse "machine __mul__"))
                  | some _ => some (.tau, config.setControl (.refusing "machine __mul__"))
                  | none => some (.tau, config.setControl (.refusing "machine binary operator"))
              | _ => some (.tau, config.setControl (.refusing "machine binary operator"))
          | .div, .ref address =>
              match config.heap.get? address with
              | some (.instance cls _) =>
                  match rLookupClassAttr config.classes cls "__truediv__" with
                  | some (.callable token) =>
                      match rFunctionByToken config.functions token with
                      | some function => rStartFunctionCall config function [left, right] []
                          (.binaryResult continuation)
                      | none => some (.event (.refuse "machine __truediv__"),
                          config.finish (.refuse "machine __truediv__"))
                  | some _ => some (.tau, config.setControl (.refusing "machine __truediv__"))
                  | none => some (.tau, config.setControl (.refusing "machine binary operator"))
              | _ => some (.tau, config.setControl (.refusing "machine binary operator"))
          | _, _ =>
              match rEvalBinOp op left right with
              | .ok value => some (.tau, config.setControl (.continueValue value continuation))
              | _ => some (.event (.refuse "machine binary operator"),
                  config.finish (.refuse "machine binary operator"))
      | .continueValue value (.binaryResult continuation) =>
          some (.tau, config.setControl (.continueValue value continuation))
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
      | .continueValue _ (.callReturnInstance _ _) =>
          some (.tau, config.setControl (.refusing "machine call return"))
      | .continueValue _ .printValue =>
          some (.tau, config.setControl (.refusing "machine print continuation"))
      | .raising error => some (.event (.raise error), config.finish (.raise error))

def runB1 : Nat → RConfig → List RLabel × RConfig
  | 0, config => ([], config)
  | fuel + 1, config =>
      match config.status with
      | .finished _ => ([], config)
      | .running =>
          match config.choices, resolveB1 config with
          | choice :: tail, _ =>
              let token := 0
              if token ∈ choice.allowed then
                let next := config.chooseToken tail token
                let result := runB1 fuel next
                (.event (.choice choice.kind token) :: result.1, result.2)
              else
                let stuck := config.finish (.refuse "machine choice")
                ([.event (.refuse "machine choice")], stuck)
          | [], some (label, next) =>
              let result := runB1 fuel next
              (label :: result.1, result.2)
          | [], none =>
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
          | allocateList values continuation =>
              simp [resolveAst, hframes, hcontrol] at h
              obtain ⟨rfl, rfl⟩ := h
              apply Step.allocateListProceed (config := config) (frame := frame) (tail := tail)
                (values := values) (continuation := continuation)
              calc
                config.frames = frame :: tail := hframes
                _ = { frame with control := .allocateList values continuation } :: tail := by
                  exact congrArg (fun current => current :: tail)
                    (frame_with_control_eq frame _ hcontrol)
          | allocateDict entries continuation =>
              simp [resolveAst, hframes, hcontrol] at h
              obtain ⟨rfl, rfl⟩ := h
              apply Step.allocateDictProceed (config := config) (frame := frame) (tail := tail)
                (entries := entries) (continuation := continuation)
              calc
                config.frames = frame :: tail := hframes
                _ = { frame with control := .allocateDict entries continuation } :: tail := by
                  exact congrArg (fun current => current :: tail)
                    (frame_with_control_eq frame _ hcontrol)
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

private def bAllocationConfig : RConfig :=
  let initial := RConfig.initial b1Module
  let frame : RFrame :=
    { control := .resourceChoice .allocation
        (.allocateList [.int 1] .discardValue)
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

private def bWhileModule : RModule :=
  { body := #[
      .assign (.name "total" testSpan) (.constant (.int 0) testSpan) testSpan,
      .assign (.name "i" testSpan) (.constant (.int 0) testSpan) testSpan,
      .whileStmt
        (.compare (.name "i" testSpan) #[.lt] #[.constant (.int 3) testSpan] testSpan)
        #[.assign (.name "total" testSpan)
            (.binOp (.name "total" testSpan) .add (.name "i" testSpan) testSpan) testSpan,
          .assign (.name "i" testSpan)
            (.binOp (.name "i" testSpan) .add (.constant (.int 1) testSpan) testSpan) testSpan]
        #[] testSpan,
      .ret (some (.name "total" testSpan)) testSpan] }

private def bForModule : RModule :=
  { body := #[
      .assign (.name "total" testSpan) (.constant (.int 0) testSpan) testSpan,
      .forStmt (.name "x" testSpan)
        (.list #[.constant (.int 1) testSpan, .constant (.int 2) testSpan,
          .constant (.int 3) testSpan] testSpan)
        #[.assign (.name "total" testSpan)
            (.binOp (.name "total" testSpan) .add (.name "x" testSpan) testSpan) testSpan]
        #[] testSpan,
      .ret (some (.name "total" testSpan)) testSpan] }

private def bGlobalDeclModule : RModule :=
  { body := #[
      .assign (.name "value" testSpan) (.constant (.int 1) testSpan) testSpan,
      .functionDef "update" #[] #[]
        #[.global #["value"] testSpan,
          .assign (.name "value" testSpan) (.constant (.int 7) testSpan) testSpan]
        testSpan,
      .expr (.call (.name "update" testSpan) #[] #[] none testSpan) testSpan,
      .expr (.call (.name "print" testSpan) #[.name "value" testSpan] #[] none testSpan) testSpan] }

private def bDictModule : RModule :=
  { body := #[.ret (some (.subscript
      (.dict #[.constant (.str "x") testSpan] #[.constant (.int 7) testSpan] testSpan)
      (.constant (.str "x") testSpan) testSpan)) testSpan] }

private def bDictMethodModule : RModule :=
  { body := #[
      .assign (.name "d" testSpan)
        (.dict #[.constant (.str "x") testSpan] #[.constant (.int 7) testSpan] testSpan) testSpan,
      .ret (some (.tuple #[
        .call (.attribute (.name "d" testSpan) "get" testSpan)
          #[.constant (.str "x") testSpan] #[] none testSpan,
        .compare (.constant (.int 3) testSpan) #[.inOp]
          #[.name "d" testSpan] testSpan] testSpan)) testSpan] }

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

#guard (runB1 256 (RConfig.initial bWhileModule)).2.status ==
  .finished (.return (.int 3))

#guard (runB1 256 (RConfig.initial bForModule)).2.status ==
  .finished (.return (.int 6))

#guard rLookupModule (runB1 256 (RConfig.initial bGlobalDeclModule)).2.modules
    "__main__" "value" == some (.int 7)

#guard (runB1 32 (RConfig.initial bDictModule)).2.status ==
  .finished (.return (.int 7))

#guard (runB1 64 (RConfig.initial bDictMethodModule)).2.status ==
  .finished (.return (.tuple #[.int 7, .bool false]))

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
      .finished (.raise { errorClass := .type, args := [] }) := by
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
      .finished (.raise { errorClass := .type, args := [] }) := by
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

example : ∃ c₁ c₂,
    Step bAllocationConfig .tau c₁ ∧ Step bAllocationConfig .tau c₂ ∧ c₁ ≠ c₂ := by
  refine ⟨bAllocationConfig.setControl (.allocateList [.int 1] .discardValue),
    bAllocationConfig.setControl (.raising (resourceError .allocation)), ?_, ?_, ?_⟩
  · exact Step.resourceProceed (by rfl)
  · exact Step.resourceRaise (by rfl)
  · simp [bAllocationConfig, RConfig.setControl, resourceError]

#guard (runRelation RImpl.cpython39 3 (RConfig.initial testModule)).1 ==
  [.tau, .tau, .event (.return (.int 7))]

private def choiceConfig : RConfig :=
  (RConfig.initial testModule).withChoice { kind := "identity", allowed := [0, 1] }

#guard (runRelation RImpl.cpython39 1 choiceConfig).1 ==
  [.event (.choice "identity" 0)]

#guard (runB1 1 choiceConfig).1 ==
  [.event (.choice "identity" 0)]

example :
    choiceConfig.chooseToken [] 0 ≠ choiceConfig.chooseToken [] 1 := by
  simp [choiceConfig, RConfig.chooseToken]

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
