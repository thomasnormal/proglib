import Lean.ToExpr

namespace LeanModels.Rust

/-! The first MIR slice keeps the compiler's structured envelope visible.  The
loader below admits the node families needed by the assignment/storage rows
and turns every other MIR constructor into an explicit refusal. -/

structure Place where
  localId : Nat
  projection : List String
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

inductive Operand where
  | copy (place : Place)
  | move (place : Place)
  | constant (id : Nat) (bytes : List Nat)
  | unsupported (kind : String)
deriving Repr, Inhabited, BEq, Lean.ToExpr

inductive Rvalue where
  | use (operand : Operand)
  | binaryEq (left right : Operand)
  | binaryBitAnd (left right : Operand)
  | binaryDiv (left right : Operand)
  | unsupported (kind : String)
deriving Repr, Inhabited, BEq, Lean.ToExpr

inductive Statement where
  | assign (place : Place) (value : Rvalue)
  | storageLive (localId : Nat)
  | storageDead (localId : Nat)
  | placeMention (place : Place)
  | unsupported (kind : String)
deriving Repr, Inhabited, BEq, Lean.ToExpr

inductive Terminator where
  | ret
  | goto (target : Nat)
  | switchInt (discr : Operand) (branches : List (Int × Nat)) (otherwise : Nat)
  | assert (cond : Operand) (expected : Bool) (target : Nat)
  | call (func : Operand) (args : List Operand) (destination : Place) (target : Nat)
  | unreachable
  | unsupported (kind : String)
deriving Repr, Inhabited, BEq, Lean.ToExpr

structure Block where
  statements : List Statement
  terminator : Terminator
deriving Repr, Inhabited, BEq, Lean.ToExpr

structure Body where
  instanceId : String
  blocks : List Block
deriving Repr, Inhabited, BEq, Lean.ToExpr

structure CallEdge where
  caller : String
  block : Nat
  callee : String
  resolved : Bool
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

structure Envelope where
  schema : String
  entry : String
  bodies : List Body
  calls : List CallEdge := []
deriving Repr, Inhabited, BEq, Lean.ToExpr

end LeanModels.Rust
