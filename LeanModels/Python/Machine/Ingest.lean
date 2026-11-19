import Lean
import LeanModels.Python.Ast
import LeanModels.Python.Machine.Relation

namespace LeanModels.Python.Machine

/-!
The machine-facing envelope keeps the CPython AST node shape.  This schema is
deliberately separate from `Ast.Expr` and from `Json.lean`: absent optional
fields remain absent, assignment target lists remain lists, and every binding
form has its own node.  A later decoder may populate this schema from the
approved extractor envelope without lowering any node.
-/

structure MAlias where
  name : String
  asname : Option String
deriving Repr, Inhabited, BEq

inductive MExpr where
  | constant (value : Const) (span : Span)
  | name (id : String) (span : Span)
  | binOp (left : MExpr) (op : BinOp) (right : MExpr) (span : Span)
  | unaryOp (op : UnaryOp) (operand : MExpr) (span : Span)
  | boolOp (op : BoolOp) (values : Array MExpr) (span : Span)
  | compare (left : MExpr) (ops : Array CmpOp) (comparators : Array MExpr) (span : Span)
  | ifExp (test : MExpr) (body : MExpr) (orelse : MExpr) (span : Span)
  | call (func : MExpr) (args : Array MExpr) (keywords : Array (String × MExpr))
      (starargs : Array MExpr) (kwargs : Array MExpr) (span : Span)
  | attribute (value : MExpr) (attr : String) (span : Span)
  | subscript (value : MExpr) (slice : MExpr) (span : Span)
  | slice (value : MExpr) (lower : Option MExpr) (upper : Option MExpr)
      (step : Option MExpr) (span : Span)
  | list (elts : Array MExpr) (span : Span)
  | tuple (elts : Array MExpr) (span : Span)
  | set (elts : Array MExpr) (span : Span)
  | dict (keys : Array (Option MExpr)) (values : Array MExpr) (span : Span)
  | joinedStr (values : Array MExpr) (span : Span)
  | formattedValue (value : MExpr) (conversion : Int) (formatSpec : Option MExpr)
      (span : Span)
  | listComp (elt : MExpr) (target : MExpr) (iter : MExpr) (ifs : Array MExpr)
      (walrus : Array (String × MExpr)) (span : Span)
  | setComp (elt : MExpr) (target : MExpr) (iter : MExpr) (ifs : Array MExpr)
      (walrus : Array (String × MExpr)) (span : Span)
  | dictComp (key : MExpr) (value : MExpr) (target : MExpr) (iter : MExpr)
      (ifs : Array MExpr) (span : Span)
  | genExp (elt : MExpr) (target : MExpr) (iter : MExpr) (ifs : Array MExpr)
      (walrus : Array (String × MExpr)) (span : Span)
  | namedExpr (target : String) (value : MExpr) (span : Span)
  | starred (value : MExpr) (span : Span)
  | unsupported (kind : String) (span : Span)
deriving Repr, Inhabited, BEq

structure MArg where
  name : String
  annotation : Option MExpr := none
  default : Option MExpr := none
  positionalOnly : Bool := false
  keywordOnly : Bool := false
  variadic : Bool := false
  keywordVariadic : Bool := false
deriving Repr, Inhabited, BEq

structure MArguments where
  positionalOnly : Array MArg
  positional : Array MArg
  vararg : Option MArg
  keywordOnly : Array MArg
  kwDefaults : Array (Option MExpr)
  kwarg : Option MArg
  defaults : Array MExpr
deriving Repr, Inhabited, BEq

inductive MStmt where
  | pass (span : Span)
  | expr (value : MExpr) (span : Span)
  | assign (targets : Array MExpr) (value : MExpr) (span : Span)
  | unpackAssign (before : Array String) (star : String) (after : Array String)
      (value : MExpr) (span : Span)
  | annAssign (target : MExpr) (annotation : MExpr) (value : Option MExpr)
      (simple : Bool) (span : Span)
  | augAssign (target : MExpr) (op : BinOp) (value : MExpr) (span : Span)
  | ret (value : Option MExpr) (span : Span)
  | delete (targets : Array MExpr) (span : Span)
  | deleteSubscript (receiver : MExpr) (index : MExpr) (span : Span)
  | deleteAttribute (receiver : MExpr) (attr : String) (span : Span)
  | ifStmt (test : MExpr) (body : Array MStmt) (orelse : Array MStmt) (span : Span)
  | whileStmt (test : MExpr) (body : Array MStmt) (orelse : Array MStmt) (span : Span)
  | forStmt (target : MExpr) (iter : MExpr) (body : Array MStmt) (orelse : Array MStmt)
      (isAsync : Bool) (span : Span)
  | functionDef (name : String) (args : MArguments) (decorators : Array MExpr)
      (returns : Option MExpr) (body : Array MStmt) (span : Span)
  | classDef (name : String) (bases : Array MExpr) (keywords : Array (String × MExpr))
      (decorators : Array MExpr) (body : Array MStmt) (span : Span)
  | import (names : Array MAlias) (span : Span)
  | importFrom (module : Option String) (names : Array MAlias) (level : Nat) (span : Span)
  | global (names : Array String) (span : Span)
  | nonlocal (names : Array String) (span : Span)
  | raise (exception : Option MExpr) (cause : Option MExpr) (span : Span)
  | assertStmt (test : MExpr) (msg : Option MExpr) (span : Span)
  | yieldStmt (value : Option MExpr) (span : Span)
  | yieldFrom (value : MExpr) (span : Span)
  | tryStmt (body : Array MStmt)
      (handlers : Array (Option MExpr × Option String × Array MStmt)) (orelse : Array MStmt)
      (finalbody : Array MStmt) (span : Span)
  | withStmt (items : Array (MExpr × Option MExpr)) (body : Array MStmt) (isAsync : Bool)
      (span : Span)
  | brk (span : Span)
  | cont (span : Span)
  | unsupported (kind : String) (span : Span)
deriving Repr, Inhabited, BEq

structure MModule where
  body : Array MStmt
deriving Repr, Inhabited, BEq

/-! The machine decoder reads the extractor's AST envelope directly.  It is
kept here instead of calling `Json.lean`: unsupported nodes remain explicit
machine nodes, and no compatibility lowering or census flag is consulted. -/

open Lean (Json)

private def mField (j : Json) (name : String) : Except String Json :=
  j.getObjVal? name

private def mSpan (j : Json) : Except String Span := do
  let getNat := fun name => do (← mField j name).getNat?
  return { lineno := ← getNat "lineno"
           colOffset := ← getNat "col_offset"
           endLineno := ← getNat "end_lineno"
           endColOffset := ← getNat "end_col_offset" }

private def mBinOp : String → Option BinOp
  | "Add" => some .add | "Sub" => some .sub | "Mult" => some .mult
  | "Div" => some .div | "FloorDiv" => some .floorDiv | "Mod" => some .mod
  | "Pow" => some .pow | "LShift" => some .lshift | "RShift" => some .rshift
  | "BitOr" => some .bitOr | "BitXor" => some .bitXor | "BitAnd" => some .bitAnd
  | "MatMult" => some .matMult | _ => none

private def mUnaryOp : String → Option UnaryOp
  | "USub" => some .usub | "Not" => some .not | "UAdd" => some .uadd
  | "Invert" => some .invert | _ => none

private def mBoolOp : String → Option BoolOp
  | "And" => some .and | "Or" => some .or | _ => none

private def mCmpOp : String → Option CmpOp
  | "Eq" => some .eq | "NotEq" => some .notEq
  | "Lt" => some .lt | "LtE" => some .ltE
  | "Gt" => some .gt | "GtE" => some .gtE
  | "Is" => some .is | "IsNot" => some .isNot
  | "In" => some .inOp | "NotIn" => some .notIn
  | _ => none

private def mConst (j : Json) : Except String Const := do
  let ty ← (← mField j "type").getStr?
  match ty with
  | "none" => pure .none
  | "ellipsis" => pure .ellipsis
  | "bool" => pure (.bool (← (← mField j "value").getBool?))
  | "str" => pure (.str (← (← mField j "value").getStr?))
  | "bytes" =>
      let values ← (← mField j "value").getArr?
      let bytes ← values.mapM fun value => do
        let number ← value.getNat?
        if number ≤ 255 then pure (UInt8.ofNat number)
        else throw "invalid machine byte"
      pure (.bytes bytes)
  | "int" =>
      let text ← (← mField j "repr").getStr?
      match text.toInt? with
      | some n => pure (.int n)
      | none => throw s!"invalid machine integer {text}"
  | "float" =>
      let text ← (← mField j "bits").getStr?
      match text.toNat? with
      | some bits => pure (.float (Float64.ofBits bits))
      | none => throw s!"invalid machine float bits {text}"
  | _ => throw s!"unsupported machine constant {ty}"

partial def mExpr (j : Json) : Except String MExpr := do
  let kind ← (← mField j "kind").getStr?
  let span ← mSpan (← mField j "span")
  match kind with
  | "Constant" => pure (.constant (← mConst (← mField j "value")) span)
  | "Name" => pure (.name (← (← mField j "id").getStr?) span)
  | "BinOp" =>
      let opName ← (← mField j "op").getStr?
      match mBinOp opName with
      | some op => pure (.binOp (← mExpr (← mField j "left")) op
          (← mExpr (← mField j "right")) span)
      | none => pure (.unsupported kind span)
  | "UnaryOp" =>
      let opName ← (← mField j "op").getStr?
      match mUnaryOp opName with
      | some op => pure (.unaryOp op (← mExpr (← mField j "operand")) span)
      | none => pure (.unsupported kind span)
  | "JoinedStr" =>
      pure (.joinedStr (← (← (← mField j "values").getArr?).mapM mExpr) span)
  | "FormattedValue" =>
      let conversion ← (← mField j "conversion").getInt?
      let formatSpec ← match j.getObjVal? "format_spec" with
        | .ok .null | .error _ => pure none
        | .ok value => some <$> mExpr value
      pure (.formattedValue (← mExpr (← mField j "value")) conversion formatSpec span)
  | "BoolOp" =>
      let opName ← (← mField j "op").getStr?
      match mBoolOp opName with
      | some op => pure (.boolOp op (← (← (← mField j "values").getArr?).mapM mExpr) span)
      | none => pure (.unsupported kind span)
  | "Call" =>
      let func ← mExpr (← mField j "func")
      let args ← (← (← mField j "args").getArr?).mapM mExpr
      let keywords ← (← (← mField j "keywords").getArr?).mapM fun kw => do
        let name ← (← mField kw "arg").getStr?
        pure (name, ← mExpr (← mField kw "value"))
      pure (.call func args keywords #[] #[] span)
  | "IfExp" => pure (.ifExp (← mExpr (← mField j "test"))
      (← mExpr (← mField j "body")) (← mExpr (← mField j "orelse")) span)
  | "Compare" =>
      let left ← mExpr (← mField j "left")
      let ops ← (← (← mField j "ops").getArr?).mapM fun op => do
        let name ← match op with
          | .str name => pure name
          | _ => (← mField op "kind").getStr?
        match mCmpOp name with
        | some op => pure op
        | none => throw s!"unsupported machine comparison {name}"
      let comparators ← (← (← mField j "comparators").getArr?).mapM mExpr
      pure (.compare left ops comparators span)
  | "List" => pure (.list (← (← (← mField j "elts").getArr?).mapM mExpr) span)
  | "Tuple" => pure (.tuple (← (← (← mField j "elts").getArr?).mapM mExpr) span)
  | "Set" => pure (.set (← (← (← mField j "elts").getArr?).mapM mExpr) span)
  | "Dict" =>
      let keys ← (← (← mField j "keys").getArr?).mapM fun key =>
        match key with | .null => pure none | _ => some <$> mExpr key
      let values ← (← (← mField j "values").getArr?).mapM mExpr
      pure (.dict keys values span)
  | "ListComp" =>
      let ifs ← (← (← mField j "ifs").getArr?).mapM mExpr
      let walrus ← match j.getObjVal? "walrus" with
        | .ok value => (← value.getArr?).mapM (fun item => do
            pure ((← (← mField item "target").getStr?),
              (← mExpr (← mField item "value"))))
        | .error _ => pure #[]
      pure (.listComp (← mExpr (← mField j "elt"))
        (← mExpr (← mField j "target")) (← mExpr (← mField j "iter")) ifs walrus span)
  | "SetComp" =>
      let ifs ← (← (← mField j "ifs").getArr?).mapM mExpr
      let walrus ← match j.getObjVal? "walrus" with
        | .ok value => (← value.getArr?).mapM (fun item => do
            pure ((← (← mField item "target").getStr?),
              (← mExpr (← mField item "value"))))
        | .error _ => pure #[]
      pure (.setComp (← mExpr (← mField j "elt"))
        (← mExpr (← mField j "target")) (← mExpr (← mField j "iter")) ifs walrus span)
  | "DictComp" =>
      let ifs ← (← (← mField j "ifs").getArr?).mapM mExpr
      pure (.dictComp (← mExpr (← mField j "key")) (← mExpr (← mField j "value"))
        (← mExpr (← mField j "target")) (← mExpr (← mField j "iter")) ifs span)
  | "GeneratorExp" =>
      let ifs ← (← (← mField j "ifs").getArr?).mapM mExpr
      let walrus ← match j.getObjVal? "walrus" with
        | .ok value => (← value.getArr?).mapM (fun item => do
            pure ((← (← mField item "target").getStr?),
              (← mExpr (← mField item "value"))))
        | .error _ => pure #[]
      pure (.genExp (← mExpr (← mField j "elt"))
        (← mExpr (← mField j "target")) (← mExpr (← mField j "iter")) ifs walrus span)
  | "Attribute" => pure (.attribute (← mExpr (← mField j "value"))
      (← (← mField j "attr").getStr?) span)
  | "Subscript" => pure (.subscript (← mExpr (← mField j "value"))
      (← mExpr (← mField j "index")) span)
  | "Slice" =>
      let component := fun name => do
        match j.getObjVal? name with
        | .ok .null | .error _ => pure none
        | .ok value => some <$> mExpr value
      pure (.slice (← mExpr (← mField j "value")) (← component "lower")
        (← component "upper") (← component "step") span)
  | "NamedExpr" => pure (.namedExpr (← (← mField j "target").getStr?)
      (← mExpr (← mField j "value")) span)
  | "Starred" => pure (.starred (← mExpr (← mField j "value")) span)
  | _ => pure (.unsupported kind span)

private def mArg (j : Json) : Except String MArg := do
  let annotation ← match j.getObjVal? "annotation" with
    | .ok .null | .error _ => pure none
    | .ok value => some <$> mExpr value
  let default ← match j.getObjVal? "default" with
    | .ok value =>
        let span ← mSpan (← mField j "span")
        some <$> (pure (.constant (← mConst value) span))
    | .error _ => pure none
  let flag := fun name =>
    match j.getObjVal? name with
    | .ok (.bool value) => value
    | _ => false
  pure { name := ← (← mField j "arg").getStr?
         annotation, default
         positionalOnly := flag "positional_only"
         keywordOnly := flag "keyword_only"
         variadic := flag "variadic"
         keywordVariadic := flag "keyword_variadic" }

private def mArguments (j : Json) : Except String MArguments := do
  let positionalOnly ← (← (← mField j "posonlyargs").getArr?).mapM mArg
  let positional ← (← (← mField j "args").getArr?).mapM mArg
  let vararg ← match j.getObjVal? "vararg" with
    | .ok .null | .error _ => pure none
    | .ok value => some <$> mArg value
  let keywordOnly ← (← (← mField j "kwonlyargs").getArr?).mapM mArg
  let kwDefaults ← (← (← mField j "kw_defaults").getArr?).mapM fun value =>
    match value with | .null => pure none | _ => some <$> mExpr value
  let kwarg ← match j.getObjVal? "kwarg" with
    | .ok .null | .error _ => pure none
    | .ok value => some <$> mArg value
  let defaults ← (← (← mField j "defaults").getArr?).mapM mExpr
  pure { positionalOnly, positional, vararg, keywordOnly, kwDefaults, kwarg, defaults }

private def mFunctionArguments (j : Json) : Except String MArguments := do
  match j with
  | .arr values =>
      let all ← values.mapM mArg
      let positionalOnly := all.filter (·.positionalOnly)
      let positional := all.filter (fun arg =>
        !arg.positionalOnly && !arg.keywordOnly && !arg.variadic && !arg.keywordVariadic)
      let vararg := all.find? (·.variadic)
      let keywordOnly := all.filter (·.keywordOnly)
      let kwarg := all.find? (·.keywordVariadic)
      let result : MArguments :=
        { positionalOnly
          positional := positional
          vararg
          keywordOnly
          kwDefaults := keywordOnly.map (·.default)
          kwarg
          defaults := positional.filterMap MArg.default }
      pure result
  | _ => mArguments j

partial def mStmt (j : Json) : Except String MStmt := do
  let kind ← (← mField j "kind").getStr?
  let span ← mSpan (← mField j "span")
  match kind with
  | "Pass" => pure (.pass span)
  | "Expr" => pure (.expr (← mExpr (← mField j "value")) span)
  | "Assign" => pure (.assign (← (← (← mField j "targets").getArr?).mapM mExpr)
      (← mExpr (← mField j "value")) span)
  | "Delete" =>
      let names ← (← mField j "names").getArr?
      let targets ← names.mapM (fun name => do
        return MExpr.name (← name.getStr?) span)
      pure (.delete targets span)
  | "DeleteSubscript" => pure (.deleteSubscript
      (← mExpr (← mField j "recv")) (← mExpr (← mField j "key")) span)
  | "DeleteAttribute" => pure (.deleteAttribute
      (← mExpr (← mField j "recv")) (← (← mField j "attr").getStr?) span)
  | "Raise" =>
      let exception ← match (← mField j "exc") with
        | .null => pure none
        | value => some <$> mExpr value
      let cause ← match j.getObjVal? "cause" with
        | .ok .null => pure none
        | .ok value => some <$> mExpr value
        | .error _ => pure none
      pure (.raise exception cause span)
  | "Assert" =>
      let msg ← match j.getObjVal? "msg" with
        | .ok .null | .error _ => pure none
        | .ok value => some <$> mExpr value
      pure (.assertStmt (← mExpr (← mField j "test")) msg span)
  | "Yield" =>
      let value ← match j.getObjVal? "value" with
        | .ok .null | .error _ => pure none
        | .ok value => some <$> mExpr value
      pure (.yieldStmt value span)
  | "YieldFrom" =>
      pure (.yieldFrom (← mExpr (← mField j "value")) span)
  | "UnpackAssign" => pure (.unpackAssign
      (← (← (← mField j "before").getArr?).mapM (·.getStr?))
      (← (← mField j "star").getStr?)
      (← (← (← mField j "after").getArr?).mapM (·.getStr?))
      (← mExpr (← mField j "value")) span)
  | "AnnAssign" =>
      let value ← match ← mField j "value" with
        | .null => pure none
        | expression => some <$> mExpr expression
      let simple := match j.getObjVal? "simple" with
        | .ok (.bool b) => b
        | _ => false
      pure (.annAssign (← mExpr (← mField j "target"))
        (← mExpr (← mField j "annotation")) value simple span)
  | "AugAssign" =>
      let opName ← (← mField j "op").getStr?
      match mBinOp opName with
      | some op => pure (.augAssign (← mExpr (← mField j "target")) op
          (← mExpr (← mField j "value")) span)
      | none => pure (.unsupported kind span)
  | "Return" =>
      let value ← match ← mField j "value" with
        | .null => pure none
        | expression => some <$> mExpr expression
      pure (.ret value span)
  | "If" => pure (.ifStmt (← mExpr (← mField j "test"))
      (← (← (← mField j "body").getArr?).mapM mStmt)
      (← (← (← mField j "orelse").getArr?).mapM mStmt) span)
  | "While" => pure (.whileStmt (← mExpr (← mField j "test"))
      (← (← (← mField j "body").getArr?).mapM mStmt)
      (← (← (← mField j "orelse").getArr?).mapM mStmt) span)
  | "For" => pure (.forStmt (← mExpr (← mField j "target"))
      (← mExpr (← mField j "iter"))
      (← (← (← mField j "body").getArr?).mapM mStmt)
      (← (← (← mField j "orelse").getArr?).mapM mStmt)
      false span)
  | "FunctionDef" | "NestedDef" =>
      let decorators ← match j.getObjVal? "decorator_list" with
        | .ok value => (← value.getArr?).mapM mExpr
        | .error _ => pure #[]
      let returns ← match j.getObjVal? "returns" with
        | .ok .null | .error _ => pure none
        | .ok value => some <$> mExpr value
      pure (.functionDef (← (← mField j "name").getStr?)
        (← mFunctionArguments (← mField j "args")) decorators returns
        (← (← (← mField j "body").getArr?).mapM mStmt) span)
  | "Global" => pure (.global (← (← (← mField j "names").getArr?).mapM (·.getStr?)) span)
  | "Nonlocal" => pure (.nonlocal (← (← (← mField j "names").getArr?).mapM (·.getStr?)) span)
  | "Break" => pure (.brk span)
  | "Continue" => pure (.cont span)
  | _ => pure (.unsupported kind span)

private def mStmtKind : MStmt → String
  | .pass _ => "Pass"
  | .expr _ _ => "Expr"
  | .assign _ _ _ => "Assign"
  | .unpackAssign _ _ _ _ _ => "UnpackAssign"
  | .annAssign _ _ _ _ _ => "AnnAssign"
  | .augAssign _ _ _ _ => "AugAssign"
  | .ret _ _ => "Return"
  | .delete _ _ => "Delete"
  | .deleteSubscript _ _ _ => "DeleteSubscript"
  | .deleteAttribute _ _ _ => "DeleteAttribute"
  | .ifStmt _ _ _ _ => "If"
  | .whileStmt _ _ _ _ => "While"
  | .forStmt _ _ _ _ isAsync _ => if isAsync then "AsyncFor" else "For"
  | .functionDef _ _ _ _ _ _ => "FunctionDef"
  | .classDef _ _ _ _ _ _ => "ClassDef"
  | .import _ _ => "Import"
  | .importFrom _ _ _ _ => "ImportFrom"
  | .global _ _ => "Global"
  | .nonlocal _ _ => "Nonlocal"
  | .raise _ _ _ => "Raise"
  | .assertStmt _ _ _ => "Assert"
  | .yieldStmt _ _ => "Yield"
  | .yieldFrom _ _ => "YieldFrom"
  | .tryStmt _ _ _ _ _ => "Try"
  | .withStmt _ _ isAsync _ => if isAsync then "AsyncWith" else "With"
  | .brk _ => "Break"
  | .cont _ => "Continue"
  | .unsupported kind _ => kind

private def mStmtSpan : MStmt → Span
  | .pass span | .expr _ span | .assign _ _ span | .unpackAssign _ _ _ _ span
  | .annAssign _ _ _ _ span | .augAssign _ _ _ span | .ret _ span | .delete _ span
  | .deleteSubscript _ _ span | .deleteAttribute _ _ span | .ifStmt _ _ _ span
  | .whileStmt _ _ _ span | .forStmt _ _ _ _ _ span | .functionDef _ _ _ _ _ span
  | .classDef _ _ _ _ _ span | .import _ span | .importFrom _ _ _ span
  | .global _ span | .nonlocal _ span | .raise _ _ span | .assertStmt _ _ span
  | .yieldStmt _ span | .yieldFrom _ span | .tryStmt _ _ _ _ span
  | .withStmt _ _ _ span | .brk span | .cont span | .unsupported _ span => span

def parseMachineModule (j : Json) : Except String MModule := do
  let module ← mField j "module"
  let body ← (← (← mField module "body").getArr?).mapM mStmt
  pure { body }

partial def mExprToExpr : MExpr → Expr
  | .constant value span => .constant value span
  | .name id span => .name id span
  | .binOp left op right span => .binOp (mExprToExpr left) op (mExprToExpr right) span
  | .unaryOp op operand span => .unaryOp op (mExprToExpr operand) span
  | .boolOp op values span => .boolOp op (values.map mExprToExpr) span
  | .compare left ops comparators span => .compare (mExprToExpr left) ops
      (comparators.map mExprToExpr) span
  | .ifExp test body orelse span => .ifExp (mExprToExpr test)
      (mExprToExpr body) (mExprToExpr orelse) span
  | .call func args keywords _ _ span => .call (mExprToExpr func) (args.map mExprToExpr)
      (keywords.map fun (name, value) => (name, mExprToExpr value)) none span
  | .attribute value attr span => .attribute (mExprToExpr value) attr span
  | .subscript value slice span => .subscript (mExprToExpr value) (mExprToExpr slice) span
  | .slice value lower upper step span =>
      let missing := Expr.constant .none span
      .slice (mExprToExpr value) (lower.map mExprToExpr |>.getD missing)
        (upper.map mExprToExpr |>.getD missing) (step.map mExprToExpr |>.getD missing) span
  | .list elts span => .list (elts.map mExprToExpr) span
  | .tuple elts span => .tuple (elts.map mExprToExpr) span
  | .dict keys values span => .dict (keys.map (fun key =>
      key.map mExprToExpr |>.getD (.constant .none span))) (values.map mExprToExpr) span
  | .namedExpr target value span => .namedExpr target (mExprToExpr value) span
  | .starred value span =>
      match value with
      | .name name _ => .unsupported "Starred" name span
      | _ => .unsupported "Starred" "" span
  | .unsupported kind span => .unsupported kind "machine ingestion frontier" span
  | .set _ span | .joinedStr _ span | .formattedValue _ _ _ span
  | .listComp _ _ _ _ _ span | .setComp _ _ _ _ _ span
  | .dictComp _ _ _ _ _ span | .genExp _ _ _ _ _ span =>
      .unsupported "machine node" "" span

partial def mExprToRaw : MExpr → RRawExpr
  | .constant _ span => .node "Constant" #[] span
  | .name _ span => .node "Name" #[] span
  | .binOp left _ right span => .node "BinOp" #[mExprToRaw left, mExprToRaw right] span
  | .unaryOp _ operand span => .node "UnaryOp" #[mExprToRaw operand] span
  | .boolOp _ values span => .node "BoolOp" (values.map mExprToRaw) span
  | .compare left _ comparators span =>
      .node "Compare" ((#[mExprToRaw left]) ++ comparators.map mExprToRaw) span
  | .ifExp test body orelse span =>
      .node "IfExp" #[mExprToRaw test, mExprToRaw body, mExprToRaw orelse] span
  | .call func args keywords starargs kwargs span =>
      .node "Call" ((#[mExprToRaw func]) ++ args.map mExprToRaw ++
        keywords.map (fun pair => mExprToRaw pair.2) ++ starargs.map mExprToRaw ++
        kwargs.map mExprToRaw) span
  | .attribute value _ span => .node "Attribute" #[mExprToRaw value] span
  | .subscript value index span => .node "Subscript" #[mExprToRaw value, mExprToRaw index] span
  | .slice value lower upper step span =>
      let noneRaw : RRawExpr := .node "None" #[] span
      let lowerRaw := lower.map mExprToRaw |>.getD noneRaw
      let upperRaw := upper.map mExprToRaw |>.getD noneRaw
      let stepRaw := step.map mExprToRaw |>.getD noneRaw
      .node "Slice" #[mExprToRaw value, lowerRaw, upperRaw, stepRaw] span
  | .list elts span => .node "List" (elts.map mExprToRaw) span
  | .tuple elts span => .node "Tuple" (elts.map mExprToRaw) span
  | .set elts span => .node "Set" (elts.map mExprToRaw) span
  | .dict keys values span =>
      .node "Dict" ((keys.map (fun key => key.map mExprToRaw |>.getD
        (.node "None" #[] span))) ++ values.map mExprToRaw) span
  | .joinedStr values span => .node "JoinedStr" (values.map mExprToRaw) span
  | .formattedValue value _ formatSpec span =>
      let noneRaw : RRawExpr := .node "None" #[] span
      let specRaw := formatSpec.map mExprToRaw |>.getD noneRaw
      .node "FormattedValue" #[mExprToRaw value, specRaw] span
  | .listComp elt target iter ifs walrus span =>
      .node "ListComp" ((#[mExprToRaw elt, mExprToRaw target, mExprToRaw iter]) ++
        ifs.map mExprToRaw ++ walrus.map (fun pair => mExprToRaw pair.2)) span
  | .setComp elt target iter ifs walrus span =>
      .node "SetComp" ((#[mExprToRaw elt, mExprToRaw target, mExprToRaw iter]) ++
        ifs.map mExprToRaw ++ walrus.map (fun pair => mExprToRaw pair.2)) span
  | .dictComp key value target iter ifs span =>
      .node "DictComp" ((#[mExprToRaw key, mExprToRaw value, mExprToRaw target,
        mExprToRaw iter]) ++ ifs.map mExprToRaw) span
  | .genExp elt target iter ifs walrus span =>
      .node "GeneratorExp" ((#[mExprToRaw elt, mExprToRaw target, mExprToRaw iter]) ++
        ifs.map mExprToRaw ++ walrus.map (fun pair => mExprToRaw pair.2)) span
  | .namedExpr _ value span => .node "NamedExpr" #[mExprToRaw value] span
  | .starred value span => .node "Starred" #[mExprToRaw value] span
  | .unsupported kind span => .node kind #[] span

partial def mExprHasRaw : MExpr → Bool
  | .constant _ _ | .name _ _ => false
  | .unsupported _ _ => true
  | .set _ _ | .joinedStr _ _ | .formattedValue _ _ _ _
  | .listComp _ _ _ _ _ _ | .setComp _ _ _ _ _ _
  | .dictComp _ _ _ _ _ _ | .genExp _ _ _ _ _ _ | .starred _ _ => true
  | .binOp left _ right _ => mExprHasRaw left || mExprHasRaw right
  | .unaryOp _ operand _ => mExprHasRaw operand
  | .boolOp _ values _ => values.any mExprHasRaw
  | .compare left _ comparators _ => mExprHasRaw left || comparators.any mExprHasRaw
  | .ifExp test body orelse _ => mExprHasRaw test || mExprHasRaw body || mExprHasRaw orelse
  | .call func args keywords starargs kwargs _ =>
      mExprHasRaw func || args.any mExprHasRaw || keywords.any (fun pair => mExprHasRaw pair.2) ||
        starargs.any mExprHasRaw || kwargs.any mExprHasRaw
  | .attribute value _ _ => mExprHasRaw value
  | .subscript value index _ => mExprHasRaw value || mExprHasRaw index
  | .slice value lower upper step _ =>
      mExprHasRaw value || lower.any mExprHasRaw || upper.any mExprHasRaw || step.any mExprHasRaw
  | .list elts _ | .tuple elts _ => elts.any mExprHasRaw
  | .dict keys values _ => keys.any (fun key => key.any mExprHasRaw) || values.any mExprHasRaw
  | .namedExpr _ value _ => mExprHasRaw value

private def mStmtExpressions : MStmt → Array MExpr
  | .pass _ | .global _ _ | .nonlocal _ _ | .brk _ | .cont _ | .unsupported _ _ => #[]
  | .expr value _ => #[value]
  | .assign targets value _ => targets ++ #[value]
  | .unpackAssign _ _ _ value _ => #[value]
  | .annAssign target annotation value _ _ =>
      #[target, annotation] ++ value.toArray
  | .augAssign target _ value _ => #[target, value]
  | .ret value _ => value.toArray
  | .delete targets _ => targets
  | .deleteSubscript receiver index _ => #[receiver, index]
  | .deleteAttribute receiver _ _ => #[receiver]
  | .ifStmt test _ _ _ | .whileStmt test _ _ _ => #[test]
  | .forStmt target iter _ _ _ _ => #[target, iter]
  | .functionDef _ args decorators returns _ _ =>
      let argExprs := args.positionalOnly ++ args.positional ++ args.keywordOnly
      let argAnnotations := argExprs.filterMap (·.annotation)
      let argDefaults := argExprs.filterMap (·.default)
      let argPayload := fun arg => arg.annotation.toArray ++ arg.default.toArray
      let vararg := args.vararg.toArray.flatMap argPayload
      let kwarg := args.kwarg.toArray.flatMap argPayload
      decorators ++ returns.toArray ++ args.defaults ++ args.kwDefaults.filterMap id ++
        argAnnotations ++ argDefaults ++ vararg ++ kwarg
  | .classDef _ bases keywords decorators _ _ =>
      bases ++ keywords.map (·.2) ++ decorators
  | .import _ _ | .importFrom _ _ _ _ => #[]
  | .raise exception cause _ => exception.toArray ++ cause.toArray
  | .assertStmt test msg _ => #[test] ++ msg.toArray
  | .yieldStmt value _ => value.toArray
  | .yieldFrom value _ => #[value]
  | .tryStmt _ handlers _ _ _ => handlers.flatMap (·.1.toArray)
  | .withStmt items _ _ _ => items.flatMap (fun item => #[item.1] ++ item.2.toArray)

private def mStmtHasRawDirect (stmt : MStmt) : Bool :=
  (mStmtExpressions stmt).any mExprHasRaw

private def mParam (arg : MArg) (flags : Bool × Bool × Bool) : RParam :=
  { name := arg.name, positionalOnly := flags.1, keywordOnly := flags.2.1,
    variadic := flags.2.2 }

private def mParams (args : MArguments) : Array RParam :=
  let positionalOnly := args.positionalOnly.map (fun arg => mParam arg (true, false, false))
  let positional := args.positional.map (fun arg => mParam arg (false, false, false))
  let vararg := match args.vararg with
    | some arg => #[mParam arg (false, false, true)]
    | none => #[]
  let keywordOnly := args.keywordOnly.map (fun arg => mParam arg (false, true, false))
  let kwarg := match args.kwarg with
    | some arg => #[(
        { name := arg.name, positionalOnly := false, keywordOnly := false,
          variadic := false, keywordVariadic := true } : RParam)]
    | none => #[]
  positionalOnly ++ positional ++ vararg ++ keywordOnly ++ kwarg

mutual
partial def mStmtToStmt : MStmt → RStmt
  | .expr value span =>
      if mExprHasRaw value then .exprRaw (mExprToRaw value) span
      else .expr (mExprToExpr value) span
  | stmt =>
      if mStmtHasRawDirect stmt then
        .raw (mStmtKind stmt) ((mStmtExpressions stmt).map mExprToRaw) (mStmtSpan stmt)
      else
        mStmtToStmtClean stmt

partial def mStmtToStmtClean : MStmt → RStmt
  | .pass span => .pass span
  | .expr value span => .expr (mExprToExpr value) span
  | .assign targets value span =>
      match targets.toList with
      | [target] => .assign (mExprToExpr target) (mExprToExpr value) span
      | _ => .assignMany (targets.map mExprToExpr) (mExprToExpr value) span
  | .unpackAssign before star after value span =>
      .unpackAssign before star after (mExprToExpr value) span
  | .annAssign target annotation value simple span =>
      .annAssign (mExprToExpr target) (mExprToExpr annotation)
        (value.map mExprToExpr) simple span
  | .augAssign target op value span =>
      .augAssign (mExprToExpr target) op (mExprToExpr value) span
  | .delete targets span =>
      match targets.toList with
      | [target] => .delete (mExprToExpr target) span
      | _ => .deleteMany (targets.map mExprToExpr) span
  | .deleteSubscript receiver index span =>
      .delete (.subscript (mExprToExpr receiver) (mExprToExpr index) span) span
  | .deleteAttribute receiver attr span =>
      .delete (.attribute (mExprToExpr receiver) attr span) span
  | .raise exception cause span =>
      .raise (exception.map mExprToExpr) (cause.map mExprToExpr) span
  | .assertStmt test msg span =>
      .assertStmt (mExprToExpr test) (msg.map mExprToExpr) span
  | .yieldStmt value span =>
      .yieldStmt (value.map mExprToExpr) span
  | .yieldFrom value span =>
      .yieldFrom (mExprToExpr value) span
  | .brk span => .brk span
  | .cont span => .cont span
  | .import names span =>
      match names.toList with
      | [name] => .import name.name name.asname span
      | _ => .importMany (names.map (fun name => (name.name, name.asname))) span
  | .importFrom module names level span =>
      .importFrom module (names.map (fun name => (name.name, name.asname))) level span
  | .classDef name bases keywords decorators body span =>
      .classDef name (bases.map mExprToExpr)
        (keywords.map (fun pair => (pair.1, mExprToExpr pair.2)))
        (decorators.map mExprToExpr) (body.map mStmtToStmt) span
  | .withStmt items body isAsync span =>
      RStmt.withStmt (items.map (fun pair => (mExprToExpr pair.1, pair.2.map mExprToExpr)))
        (body.map mStmtToStmt) isAsync span
  | .tryStmt body handlers orelse finalbody span =>
      RStmt.tryStmt (body.map mStmtToStmt)
        (handlers.map (fun handler =>
          (handler.1.map mExprToExpr, handler.2.1, handler.2.2.map mStmtToStmt)))
        (orelse.map mStmtToStmt) (finalbody.map mStmtToStmt) span
  | .ret value span => .ret (mExprToExpr <$> value) span
  | .ifStmt test body orelse span => .ifStmt (mExprToExpr test)
      (body.map mStmtToStmt) (orelse.map mStmtToStmt) span
  | .whileStmt test body orelse span => .whileStmt (mExprToExpr test)
      (body.map mStmtToStmt) (orelse.map mStmtToStmt) span
  | .forStmt target iter body orelse _ span => .forStmt (mExprToExpr target)
      (mExprToExpr iter) (body.map mStmtToStmt) (orelse.map mStmtToStmt) span
  | .functionDef name args decorators returns body span =>
      if !decorators.isEmpty || returns.isSome then
        .functionDefFull name (mParams args) (args.defaults.map mExprToExpr)
          (decorators.map mExprToExpr) (returns.map mExprToExpr)
          (body.map mStmtToStmt) span
      else if args.keywordOnly.isEmpty then
        .functionDef name (mParams args) (args.defaults.map mExprToExpr)
          (body.map mStmtToStmt) span
      else
        .functionDefKw name (mParams args) (args.defaults.map mExprToExpr)
          (args.kwDefaults.map (·.map mExprToExpr)) (body.map mStmtToStmt) span
  | .global names span => .global names span
  | .nonlocal names span => .nonlocal names span
  | .unsupported kind span => .unsupported kind "machine ingestion frontier" span
end

def compileMachineModule (module : MModule) : RModule :=
  { body := module.body.map mStmtToStmt }

private def ingestSpan : Json :=
  Lean.Json.mkObj [("lineno", Lean.toJson (1 : Nat)), ("col_offset", Lean.toJson (0 : Nat)),
    ("end_lineno", Lean.toJson (1 : Nat)), ("end_col_offset", Lean.toJson (1 : Nat))]

private def ingestName (name : String) : Json :=
  Lean.Json.mkObj [("kind", Lean.toJson "Name"), ("span", ingestSpan),
    ("id", Lean.toJson name)]

private def ingestModule : Json :=
  Lean.Json.mkObj [("module", Lean.Json.mkObj [("kind", Lean.toJson "Module"),
    ("body", Lean.toJson #[
      Lean.Json.mkObj [("kind", Lean.toJson "Global"), ("span", ingestSpan),
        ("names", Lean.toJson #[("counter" : String)])],
      Lean.Json.mkObj [("kind", Lean.toJson "Assign"), ("span", ingestSpan),
        ("targets", Lean.toJson #[ingestName "value"]),
        ("value", Lean.Json.mkObj [("kind", Lean.toJson "Constant"), ("span", ingestSpan),
          ("value", Lean.Json.mkObj [("type", Lean.toJson "int"), ("repr", Lean.toJson "1")])])]])])]

private def ingestKwargArguments : Json :=
  Lean.Json.mkObj [
    ("posonlyargs", Lean.Json.arr #[]), ("args", Lean.Json.arr #[]),
    ("vararg", Lean.Json.null), ("kwonlyargs", Lean.Json.arr #[]),
    ("kw_defaults", Lean.Json.arr #[]),
    ("kwarg", Lean.Json.mkObj [("arg", Lean.toJson "items")]),
    ("defaults", Lean.Json.arr #[])]

private def ingestKwargModule : Json :=
  Lean.Json.mkObj [("module", Lean.Json.mkObj [("kind", Lean.toJson "Module"),
    ("body", Lean.toJson #[Lean.Json.mkObj [
      ("kind", Lean.toJson "FunctionDef"), ("span", ingestSpan),
      ("name", Lean.toJson "collectKw"), ("args", ingestKwargArguments),
      ("body", Lean.Json.arr #[])]] )])]

private def ingestGlobalFunction : Json :=
  Lean.Json.mkObj [("module", Lean.Json.mkObj [
    ("kind", Lean.toJson "Module"),
    ("body", Lean.toJson #[Lean.Json.mkObj [
      ("kind", Lean.toJson "FunctionDef"), ("span", ingestSpan),
      ("name", Lean.toJson "update"), ("args", Lean.Json.arr #[]),
      ("body", Lean.toJson #[
        Lean.Json.mkObj [("kind", Lean.toJson "Global"), ("span", ingestSpan),
          ("names", Lean.toJson #[("value" : String)])],
        Lean.Json.mkObj [("kind", Lean.toJson "Assign"), ("span", ingestSpan),
          ("targets", Lean.toJson #[ingestName "value"]),
          ("value", Lean.Json.mkObj [("kind", Lean.toJson "Constant"),
            ("span", ingestSpan), ("value", Lean.Json.mkObj [
              ("type", Lean.toJson "int"), ("repr", Lean.toJson "7")])])]])]])])]

#guard match parseMachineModule ingestModule with
  | .ok { body := #[.global #["counter"] _, .assign #[.name "value" _] _ _] } => true
  | _ => false

#guard match parseMachineModule ingestKwargModule with
  | .ok { body := #[.functionDef _ args _ _ _ _] } => args.kwarg.isSome
  | _ => false

#guard match parseMachineModule ingestGlobalFunction with
  | .ok module =>
      match (compileMachineModule module).body.toList with
      | [.functionDef _ _ _ #[.global #["value"] _, .assign _ _ _] _] => true
      | _ => false
  | _ => false

private def ingestAnnAssignModule : Json :=
  Lean.Json.mkObj [
    ("module", Lean.Json.mkObj [("kind", Lean.toJson "Module"),
      ("body", Lean.Json.arr #[Lean.Json.mkObj [
        ("kind", Lean.toJson "AnnAssign"), ("span", ingestSpan),
        ("target", ingestName "value"), ("annotation", ingestName "int"),
        ("value", Lean.Json.mkObj [("kind", Lean.toJson "Constant"),
          ("span", ingestSpan), ("value", Lean.Json.mkObj [
            ("type", Lean.toJson "int"), ("repr", Lean.toJson "7")])]),
        ("simple", Lean.toJson true)]] )])]

#guard match parseMachineModule ingestAnnAssignModule with
  | .ok module =>
      match (compileMachineModule module).body.toList with
      | [.annAssign (.name "value" _) (.name "int" _) (some (.constant (.int 7) _)) true _] => true
      | _ => false
  | _ => false

private def ingestDefaultArguments : Json :=
  Lean.Json.arr #[Lean.Json.mkObj [("arg", Lean.toJson "left")],
    Lean.Json.mkObj [("arg", Lean.toJson "right"), ("span", ingestSpan),
      ("default", Lean.Json.mkObj [("type", Lean.toJson "int"), ("repr", Lean.toJson "0")])]]

private def ingestDefaultModule : Json :=
  Lean.Json.mkObj [("module", Lean.Json.mkObj [("kind", Lean.toJson "Module"),
    ("body", Lean.Json.arr #[Lean.Json.mkObj [("kind", Lean.toJson "FunctionDef"),
      ("span", ingestSpan), ("name", Lean.toJson "show"), ("args", ingestDefaultArguments),
      ("body", Lean.Json.arr #[])]] )])]

#guard match parseMachineModule ingestDefaultModule with
  | .ok module =>
      match (compileMachineModule module).body.toList with
      | [.functionDef _ _ defaults _ _] => defaults.size == 1
      | _ => false
  | _ => false

private def ingestFunctionMetadata : Json :=
  Lean.Json.mkObj [
    ("module", Lean.Json.mkObj [("kind", Lean.toJson "Module"),
      ("body", Lean.Json.arr #[Lean.Json.mkObj [
        ("kind", Lean.toJson "FunctionDef"), ("span", ingestSpan),
        ("name", Lean.toJson "decorated"), ("args", Lean.Json.arr #[]),
        ("decorator_list", Lean.Json.arr #[ingestName "deco"]),
        ("returns", ingestName "int"), ("body", Lean.Json.arr #[])]] )])]

#guard match parseMachineModule ingestFunctionMetadata with
  | .ok module =>
      match (compileMachineModule module).body.toList with
      | [.functionDefFull "decorated" #[] #[] #[.name "deco" _]
          (some (.name "int" _)) #[] _] => true
      | _ => false
  | _ => false

#guard match parseMachineModule ingestKwargModule with
  | .ok module =>
      match (compileMachineModule module).body.toList with
      | [.functionDef _ #[parameter] _ _ _] => parameter.keywordVariadic
      | _ => false
  | _ => false

end LeanModels.Python.Machine
