import LeanModels.Python.Ast

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
  | call (func : MExpr) (args : Array MExpr) (keywords : Array (String × MExpr))
      (starargs : Array MExpr) (kwargs : Array MExpr) (span : Span)
  | attribute (value : MExpr) (attr : String) (span : Span)
  | subscript (value : MExpr) (slice : MExpr) (span : Span)
  | slice (lower : Option MExpr) (upper : Option MExpr) (step : Option MExpr) (span : Span)
  | list (elts : Array MExpr) (span : Span)
  | tuple (elts : Array MExpr) (span : Span)
  | set (elts : Array MExpr) (span : Span)
  | dict (keys : Array (Option MExpr)) (values : Array MExpr) (span : Span)
  | joinedStr (values : Array MExpr) (span : Span)
  | formattedValue (value : MExpr) (conversion : Option Nat) (formatSpec : Option MExpr)
      (span : Span)
  | listComp (elt : MExpr) (generators : Array MExpr) (span : Span)
  | setComp (elt : MExpr) (generators : Array MExpr) (span : Span)
  | dictComp (key : MExpr) (value : MExpr) (generators : Array MExpr) (span : Span)
  | genExp (elt : MExpr) (generators : Array MExpr) (span : Span)
  | namedExpr (target : String) (value : MExpr) (span : Span)
  | unsupported (kind : String) (span : Span)
deriving Repr, Inhabited, BEq

structure MArg where
  name : String
  annotation : Option MExpr := none
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
  | augAssign (target : MExpr) (op : BinOp) (value : MExpr) (span : Span)
  | ret (value : Option MExpr) (span : Span)
  | delete (targets : Array MExpr) (span : Span)
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

end LeanModels.Python.Machine
