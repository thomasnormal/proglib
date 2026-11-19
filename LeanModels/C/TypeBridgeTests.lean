import LeanModels.C.Ast
import LeanModels.C.C23.Expr

namespace LeanModels.C

/-! Parser-native bridge checks for the first C consumer of the shared clang
`QualType` layer.  These terms are deliberately built from `TypeNode`, never
from a source spelling parser. -/

private def scalar : TypeNode := .builtin "unsigned short"

private def pointerToScalar : TypeNode := .pointer scalar

private def functionType : TypeNode :=
  .funcProto (.builtin "int") [pointerToScalar, .builtin "_Bool"] true

private def arrayType : TypeNode := .array (.builtin "int") (some 4)

private def qualifiedRecord : TypeNode :=
  .qualified true false (.record (some ⟨"record-1"⟩) "struct S")

private def same (left right : Except String LeanModels.Clang.QualType) : Bool :=
  match left, right with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def isError : Except String α → Bool
  | .error _ => true
  | .ok _ => false

#guard same scalar.toQualType (.ok (.cBuiltinKind .unsignedShort))
#guard same pointerToScalar.toQualType
  (.ok (.pointer (.cBuiltinKind .unsignedShort)))
#guard same functionType.toQualType
  (.ok (.function (.cBuiltinKind .int)
    [.pointer (.cBuiltinKind .unsignedShort), .cBuiltinKind .bool] true))
#guard same arrayType.toQualType
  (.ok (.array (.cBuiltinKind .int) (some 4)))
#guard same qualifiedRecord.toQualType
  (.ok (.qualified true false (.record {value := "record-1"})))
#guard (LeanModels.Clang.QualType.aggregateObject
  (.array (.cBuiltinKind .int) (some 4)))
#guard !(LeanModels.Clang.QualType.aggregateObject
  (.pointer (.record {value := "record-1"})))
#guard LeanModels.Clang.QualType.pointerObject
  (.qualified true false (.pointer (.cBuiltinKind .int)))
#guard LeanModels.Clang.QualType.pointee
  (.qualified true false (.pointer (.cBuiltinKind .int))) ==
    some (.cBuiltinKind .int)
#guard LeanModels.Clang.QualType.pointee (.cBuiltinKind .int) == none
#guard LeanModels.Clang.QualType.arrayObject
  (.qualified false true (.array (.cBuiltinKind .int) (some 4)))
#guard LeanModels.Clang.QualType.pointerOrArray
  (.qualified true false (.array (.cBuiltinKind .int) (some 4)))
#guard LeanModels.C.C23.structuredPointerObject
  (some (.qualified true false (.pointer (.cBuiltinKind .int)))) "not-a-pointer"
#guard LeanModels.C.C23.structuredIndexable
  (some (.qualified false true (.array (.cBuiltinKind .int) (some 4)))) "not-an-array"
#guard LeanModels.C.C23.intTyOfStructured
  (.qualified true false (.cBuiltinKind .unsignedShort)) == some LeanModels.C.C23.IntTy.ushort
#guard LeanModels.C.C23.floatBitsOfStructured (.cBuiltinKind .double) == some 64
#guard LeanModels.C.C23.intTyOfStructured
  (.cBuiltinKind .unsignedShort) == some LeanModels.C.C23.IntTy.ushort
#guard LeanModels.C.C23.floatBitsOfStructured (.cBuiltinKind .double) == some 64
#guard LeanModels.Clang.QualType.resolveTypedefs
  (fun h => if h.value == "P" then some (.pointer (.cBuiltinKind .int)) else none) 8
  (.typedefRef {value := "P"}) == some (.pointer (.cBuiltinKind .int))
#guard LeanModels.Clang.QualType.resolveTypedefs
  (fun h => if h.value == "P" then some (.pointer (.cBuiltinKind .int)) else none) 8
  (.qualified true false (.typedefRef {value := "P"})) ==
    some (.qualified true false (.pointer (.cBuiltinKind .int)))
#guard LeanModels.C.C23.functionPointerBitCast
  (.cast "BitCast" (.unsupported "Opaque" "" default) "opaque" default)
#guard isError (TypeNode.typedefRef none "T" |>.toQualType)
#guard isError (TypeNode.enumeration none "enum E" |>.toQualType)

end LeanModels.C
