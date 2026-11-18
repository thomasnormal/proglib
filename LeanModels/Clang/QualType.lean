import LeanModels.Cpp.Types
import Lean.ToExpr

/-!
# Shared clang `QualType` representation

This module is the common identity/type layer for the C and C++ lanes.  The
constructors are structural observations of clang's `QualType`; declaration
handles remain frontend identities and are never recovered from a spelling.
The C++ evidence reader is the first consumer.  C's envelope migration adds
the remaining C-only scalar, array, and aggregate constructors in the next F1
slices.
-/

namespace LeanModels.Clang

structure DeclarationHandle where
  value : String
  deriving Repr, BEq, Inhabited, Lean.ToExpr

inductive QualType where
  | builtin (type : LeanModels.Cpp.CppIntType)
  /-- A C frontend builtin whose signedness/width is a parser fact that the
  C profile has not normalized into the C++ integer taxonomy yet. -/
  | cBuiltin (name : String)
  | void
  | pointer (pointee : QualType)
  | array (element : QualType) (extent : Option Nat)
  | lvalueReference (referent : QualType)
  | rvalueReference (referent : QualType)
  | qualified (isConst : Bool) (isVolatile : Bool) (base : QualType)
  | function (result : QualType) (parameters : List QualType) (variadic : Bool)
  | record (declaration : DeclarationHandle)
  | enumeration (declaration : DeclarationHandle)
  | typedefRef (declaration : DeclarationHandle)
  deriving Repr, Inhabited, Lean.ToExpr

mutual
  def QualType.beq (left right : QualType) : Bool :=
    match left, right with
    | .void, .void => true
    | .builtin left, .builtin right => left == right
    | .cBuiltin left, .cBuiltin right => left == right
    | .pointer left, .pointer right => QualType.beq left right
    | .array left le, .array right re =>
        QualType.beq left right && le == re
    | .lvalueReference left, .lvalueReference right
    | .rvalueReference left, .rvalueReference right => QualType.beq left right
    | .qualified lc lv left, .qualified rc rv right =>
        lc == rc && lv == rv && QualType.beq left right
    | .function left lp lv, .function right rp rv =>
        QualType.beq left right && QualType.beqList lp rp && lv == rv
    | .record left, .record right
    | .enumeration left, .enumeration right
    | .typedefRef left, .typedefRef right => left == right
    | _, _ => false
  termination_by structural left

  def QualType.beqList (left right : List QualType) : Bool :=
    match left, right with
    | [], [] => true
    | left :: ls, right :: rs => QualType.beq left right && QualType.beqList ls rs
    | _, _ => false
  termination_by structural left
end

instance : BEq QualType := ⟨QualType.beq⟩

/-- Whether clang's structured type denotes an object with record members.
This follows the parser tree through qualifiers and one or more pointer layers
without interpreting a flat type spelling. -/
def QualType.recordLike : QualType → Bool
  | .record _ => true
  | .pointer pointee => pointee.recordLike
  | .qualified _ _ base => base.recordLike
  | _ => false

/-- Whether the declared object itself is an aggregate. Pointer layers are
objects with scalar pointer representation, even when their pointee is a
record. -/
def QualType.aggregateObject : QualType → Bool
  | .record _ => true
  | .qualified _ _ base => base.aggregateObject
  | _ => false

/-- Whether a parser-native type can be the base of C subscripting. -/
def QualType.indexable : QualType → Bool
  | .pointer _ | .array _ _ => true
  | .qualified _ _ base => base.indexable
  | _ => false

end LeanModels.Clang
