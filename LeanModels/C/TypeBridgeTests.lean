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

#guard same scalar.toQualType (.ok (.cBuiltin "unsigned short"))
#guard same pointerToScalar.toQualType
  (.ok (.pointer (.cBuiltin "unsigned short")))
#guard same functionType.toQualType
  (.ok (.function (.cBuiltin "int")
    [.pointer (.cBuiltin "unsigned short"), .cBuiltin "_Bool"] true))
#guard same arrayType.toQualType
  (.ok (.array (.cBuiltin "int") (some 4)))
#guard same qualifiedRecord.toQualType
  (.ok (.qualified true false (.record {value := "record-1"})))
#guard (LeanModels.Clang.QualType.aggregateObject
  (.array (.cBuiltin "int") (some 4)))
#guard !(LeanModels.Clang.QualType.aggregateObject
  (.pointer (.record {value := "record-1"})))
#guard LeanModels.Clang.QualType.pointerObject
  (.qualified true false (.pointer (.cBuiltin "int")))
#guard LeanModels.Clang.QualType.arrayObject
  (.qualified false true (.array (.cBuiltin "int") (some 4)))
#guard LeanModels.Clang.QualType.pointerOrArray
  (.qualified true false (.array (.cBuiltin "int") (some 4)))
#guard LeanModels.C.C23.structuredPointerObject
  (some (.qualified true false (.pointer (.cBuiltin "int")))) "not-a-pointer"
#guard LeanModels.C.C23.structuredIndexable
  (some (.qualified false true (.array (.cBuiltin "int") (some 4)))) "not-an-array"
#guard LeanModels.C.C23.functionPointerBitCast
  (.cast "BitCast" (.unsupported "Opaque" "" default) "opaque" default)
#guard isError (TypeNode.typedefRef none "T" |>.toQualType)
#guard isError (TypeNode.enumeration none "enum E" |>.toQualType)

end LeanModels.C
