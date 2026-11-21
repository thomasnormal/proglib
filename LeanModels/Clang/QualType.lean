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

inductive CBuiltin where
  | bool
  | char
  | signedChar
  | unsignedChar
  | short
  | unsignedShort
  | int
  | unsignedInt
  | long
  | unsignedLong
  | longLong
  | unsignedLongLong
  | float
  | double
  | longDouble
  | wchar
  | int128
  | uint128
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def CBuiltin.ofName : String → Option CBuiltin
  | "_Bool" | "bool" => some .bool
  | "char" => some .char
  | "signed char" => some .signedChar
  | "unsigned char" => some .unsignedChar
  | "short" | "short int" => some .short
  | "unsigned short" | "unsigned short int" => some .unsignedShort
  | "int" | "signed int" => some .int
  | "unsigned" | "unsigned int" => some .unsignedInt
  | "long" | "long int" => some .long
  | "unsigned long" | "unsigned long int" => some .unsignedLong
  | "long long" | "long long int" => some .longLong
  | "unsigned long long" | "unsigned long long int" => some .unsignedLongLong
  | "int8_t" => some .signedChar
  | "uint8_t" => some .unsignedChar
  | "int16_t" => some .short
  | "uint16_t" => some .unsignedShort
  | "int32_t" => some .int
  | "uint32_t" => some .unsignedInt
  | "int64_t" | "intptr_t" => some .long
  | "uint64_t" | "uintptr_t" => some .unsignedLong
  | "float" => some .float
  | "double" => some .double
  | "long double" => some .longDouble
  | "wchar_t" => some .wchar
  | "__int128" => some .int128
  | "unsigned __int128" | "__uint128_t" => some .uint128
  | _ => none

inductive QualType where
  | builtin (type : LeanModels.Cpp.CppIntType)
  /-- A C frontend builtin whose signedness/width is a parser fact that the
  C profile has not normalized into the C++ integer taxonomy yet. -/
  | cBuiltin (name : String)
  | cBuiltinKind (kind : CBuiltin)
  /-- Clang's placeholder type for a builtin varargs callee. -/
  | builtinFunction
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
    | .cBuiltinKind left, .cBuiltinKind right => left == right
    | .builtinFunction, .builtinFunction => true
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

/-- Remove parser-provided cv-qualification without inspecting a type
spelling.  C and C++ use the same representation and both preserve the
qualification node emitted by clang. -/
def QualType.unqualified (type : QualType) : QualType :=
  match type with
  | .qualified _ _ base => base.unqualified
  | _ => type
termination_by structural type

/-- Resolve parser-emitted typedef references through the declaration table.
The lookup is supplied by the envelope, so this follows clang's declaration
identity and never interprets a display spelling.  A fuel argument makes a
malformed cyclic frontend table a loud absence rather than an unbounded
reduction. -/
def QualType.resolveTypedefs
    (lookup : DeclarationHandle → Option QualType) : Nat → QualType → Option QualType
  | 0, _ => none
  | fuel + 1, type =>
      match type with
      | .typedefRef declaration =>
          (lookup declaration).bind (resolveTypedefs lookup fuel)
      | .pointer pointee =>
          (resolveTypedefs lookup fuel pointee).map QualType.pointer
      | .array element extent =>
          (resolveTypedefs lookup fuel element).map (fun element => .array element extent)
      | .lvalueReference referent =>
          (resolveTypedefs lookup fuel referent).map QualType.lvalueReference
      | .rvalueReference referent =>
          (resolveTypedefs lookup fuel referent).map QualType.rvalueReference
      | .qualified isConst isVolatile base =>
          (resolveTypedefs lookup fuel base).map
            (fun base => .qualified isConst isVolatile base)
      | .function result parameters variadic => do
          let result ← resolveTypedefs lookup fuel result
          let parameters ← parameters.mapM (resolveTypedefs lookup fuel)
          pure (.function result parameters variadic)
      | _ => some type
termination_by fuel => fuel

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
  | .array _ _ => true
  | .qualified _ _ base => base.aggregateObject
  | _ => false

/-- Whether a parser-native type can be the base of C subscripting. -/
def QualType.indexable : QualType → Bool
  | .pointer _ | .array _ _ => true
  | .qualified _ _ base => base.indexable
  | _ => false

/-- Whether the declared object is an array.  Arrays remain distinct from
pointer objects because C's array-to-pointer conversion is a separate AST
node. -/
def QualType.arrayObject : QualType → Bool
  | .array _ _ => true
  | .qualified _ _ base => base.arrayObject
  | _ => false

/-- Whether a parser-native type can provide pointer or array indexing. -/
def QualType.pointerOrArray : QualType → Bool
  | .pointer _ | .array _ _ => true
  | .qualified _ _ base => base.pointerOrArray
  | _ => false

/-- Whether the object value itself is a pointer. Arrays remain distinct because
array-to-pointer decay is a separate C conversion. -/
def QualType.pointerObject : QualType → Bool
  | .pointer _ => true
  | .qualified _ _ base => base.pointerObject
  | _ => false

/-- Peel one parser-native pointer layer.  Qualification is transparent for
the object type, while arrays remain distinct from pointers. -/
def QualType.pointee : QualType → Option QualType
  | .pointer pointee => some pointee
  | .qualified _ _ base => base.pointee
  | _ => none

end LeanModels.Clang
