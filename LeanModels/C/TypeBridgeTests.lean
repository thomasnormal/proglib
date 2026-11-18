import LeanModels.C.Ast

namespace LeanModels.C

/-! Parser-native bridge checks for the first C consumer of the shared clang
`QualType` layer.  These terms are deliberately built from `TypeNode`, never
from a source spelling parser. -/

private def scalar : TypeNode := .builtin "unsigned short"

private def pointerToScalar : TypeNode := .pointer scalar

private def functionType : TypeNode :=
  .funcProto (.builtin "int") [pointerToScalar, .builtin "_Bool"]

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
    [.pointer (.cBuiltin "unsigned short"), .cBuiltin "_Bool"] false))
#guard isError (TypeNode.typedefRef none "T" |>.toQualType)

end LeanModels.C
