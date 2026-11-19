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
#guard same (TypeNode.builtin "int8_t").toQualType (.ok (.cBuiltinKind .signedChar))
#guard same (TypeNode.builtin "uintptr_t").toQualType (.ok (.cBuiltinKind .unsignedLong))
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
#guard LeanModels.C.C23.floatBitsOfStructured (.cBuiltin "double") == none
#guard LeanModels.C.C23.intTyOfStructured
  (.cBuiltinKind .unsignedShort) == some LeanModels.C.C23.IntTy.ushort
#guard LeanModels.C.C23.floatBitsOfStructured (.cBuiltinKind .double) == some 64
#guard LeanModels.C.C23.isPtrIntType "not-a-spelling"
  (some (.qualified true false (.cBuiltinKind .unsignedLong)))
#guard LeanModels.C.C23.intTyOfStructured
  (.enumeration {value := "enum-1"}) == some LeanModels.C.C23.IntTy.int_
#guard LeanModels.C.C23.intTyOf? "enum E" == none
#guard ({ LeanModels.C.C23.Layout.unknown with
  size := fun _ => some 4
  declSize := fun id => if id.value == "object-1" then some 8 else none } :
  LeanModels.C.C23.Layout).sizeAt (some {value := "object-1"}) "int" == some 8
#guard ({ LeanModels.C.C23.Layout.unknown with
  structuredType := fun id =>
    if id.value == "array-1" then some (.array (.cBuiltinKind .int) (some 2)) else none } :
  LeanModels.C.C23.Layout).storageTypeAt (some {value := "array-1"}) "int[2]" == none
#guard ({ LeanModels.C.C23.Layout.unknown with
  elementSizeDecl := fun id => if id.value == "array-1" then some 4 else none } :
  LeanModels.C.C23.Layout).elementSizeAt
    (.declRef (some {value := "array-1"}) "a" "VarDecl" "int[2]" default) "int" == some 4
#guard ({ LeanModels.C.C23.Layout.unknown with
  fieldOffDecl := fun id field =>
    if id.value == "record-1" && field == "x" then some 8 else none } :
  LeanModels.C.C23.Layout).fieldOffAt
    (.declRef (some {value := "record-1"}) "r" "VarDecl" "struct R" default) "x" == some 8
#guard LeanModels.C.C23.Mem.isCharacterType
  (.qualified true false (.cBuiltinKind .unsignedChar))
#guard !LeanModels.C.C23.Mem.isCharacterType (.cBuiltin "unsigned char")
#guard !LeanModels.C.C23.Mem.cAliasCompatible "int" "volatile int"
#guard LeanModels.C.C23.Mem.cAliasModel.compatibleUsed
  (some (.cBuiltinKind .unsignedChar)) "short" "int"
#guard (({ LeanModels.C.C23.Layout.unknown with
  isUnion := fun ty => ty == "union U" } : LeanModels.C.C23.Layout).isUnion "union U")
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
