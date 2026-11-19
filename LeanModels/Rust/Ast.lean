import Lean.ToExpr

namespace LeanModels.Rust

/-! The first MIR slice keeps the compiler's structured envelope visible.  The
loader below admits the node families needed by the assignment/storage rows
and turns every other MIR constructor into an explicit refusal. -/

inductive Projection where
  | deref
  | field (index width : Nat)
  | downcast (variant : Nat)
  | unsupported (kind : String)
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

structure Place where
  localId : Nat
  projection : List Projection
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

inductive Operand where
  | copy (place : Place)
  | move (place : Place)
  | constant (id : Nat) (bytes : List Nat) (ty : Nat) (provenance : Option Nat := none)
      (zeroSized : Bool := false)
  | unsupported (kind : String)
deriving Repr, Inhabited, BEq, Lean.ToExpr

inductive CastKind where
  | intToInt
  | ptrToPtr
  | transmute
  | pointerCoercion (name : String)
  | pointerWithExposedProvenance
  | unsupported (name : String)
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

inductive Rvalue where
  | use (operand : Operand)
  | binaryEq (left right : Operand)
  | binaryNe (left right : Operand)
  | binaryLe (left right : Operand)
  | binaryLt (left right : Operand)
  | binaryBitAnd (left right : Operand)
  | binaryBitXor (left right : Operand)
  | binaryDiv (left right : Operand)
  | binaryRem (left right : Operand)
  | cast (kind : CastKind) (operand : Operand) (target : Nat)
  | checkedBinary (op : String) (left right : Operand)
  | ref (place : Place)
  | addressOf (mutable : Bool) (place : Place)
  | aggregate (tag : String) (fields : List Operand)
  | adtAggregate (variant : Nat) (fields : List Operand)
  | repeat (operand : Operand) (count : Nat)
  | discriminant (place : Place)
  | zstAggregate
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
  | assert (cond : Operand) (expected : Bool) (target : Nat) (cleanup : Option Nat := none)
  | call (func : Operand) (args : List Operand) (destination : Place) (target : Option Nat)
      (cleanup : Option Nat := none)
  | drop (place : Place) (target cleanup : Nat)
  | resume
  | unreachable
  | unsupported (kind : String)
deriving Repr, Inhabited, BEq, Lean.ToExpr

structure Block where
  statements : List Statement
  terminator : Terminator
deriving Repr, Inhabited, BEq, Lean.ToExpr

structure LocalInfo where
  localId : Nat
  ty : Nat
deriving Repr, Inhabited, BEq, Lean.ToExpr

structure Body where
  instanceId : String
  blocks : List Block
  locals : List LocalInfo := []
deriving Repr, Inhabited, BEq, Lean.ToExpr

structure CallEdge where
  caller : String
  block : Nat
  callee : Option String
  resolved : Bool
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

structure TypeLayout where
  id : String
  sourceId : Option Nat := none
  kind : String
  pointee : Option Nat := none
  fieldOffsets : List Nat := []
  sizeBits : Option Nat
  align : Option Nat
  signed : Option Bool := none
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

structure Allocation where
  id : String
  bytes : List Nat
  bytesValid : Bool := true
  provenance : List (Nat × Nat)
  align : Nat
  address : Option Nat := none
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

structure Envelope where
  schema : String
  entry : String
  bodies : List Body
  calls : List CallEdge := []
  types : List TypeLayout := []
  allocations : List Allocation := []
  provenance : List (Nat × Nat) := []
deriving Repr, Inhabited, BEq, Lean.ToExpr

end LeanModels.Rust
