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
#guard LeanModels.C.C23.isPtrType "not-a-pointer"
  (some (.qualified true false (.pointer (.cBuiltinKind .int))))
#guard !LeanModels.C.C23.isPtrType "int"
  (some (.qualified true false (.array (.cBuiltinKind .int) (some 2))))
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
    if id.value == "scalar-1" then some (.qualified true false (.cBuiltinKind .int)) else none
  size := fun _ => none } :
  LeanModels.C.C23.Layout).sizeAt (some {value := "scalar-1"}) "const int" == some 4
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
#guard ({ LeanModels.C.C23.Layout.unknown with
  fieldOffDecl := fun id field =>
    if id.value == "record-1" && field == "x" then some 8 else none } :
  LeanModels.C.C23.Layout).fieldOffDeclAt (some {value := "record-1"})
    "struct R" "x" == some 8
#guard ({ LeanModels.C.C23.Layout.unknown with
  fieldOffTypeDecl := fun id ty =>
    if id.value == "record-1" && ty == "int" then some 8 else none } :
  LeanModels.C.C23.Layout).fieldOffTypeDeclAt (some {value := "record-1"})
    "struct R" "int" == some 8
#guard ({ LeanModels.C.C23.Layout.unknown with
  fieldSizeDecl := fun id field =>
    if id.value == "record-1" && field == "x" then some 4 else none } :
  LeanModels.C.C23.Layout).fieldExtentAt
    (.declRef (some {value := "record-1"}) "r" "VarDecl" "struct R" default) "x" "int" true == some 4
#guard ({ LeanModels.C.C23.Layout.unknown with
  fieldBitsDecl := fun id field =>
    if id.value == "record-1" && field == "x" then some (8, 3) else none } :
  LeanModels.C.C23.Layout).fieldBitsDeclAt (some {value := "record-1"})
    "struct R" "x" == some (8, 3)
#guard ({ LeanModels.C.C23.Layout.unknown with
  flexibleFieldDecl := fun id field => id.value == "record-1" && field == "tail" } :
  LeanModels.C.C23.Layout).flexibleFieldDeclAt (some {value := "record-1"})
    "struct R" "tail"
#guard ({ LeanModels.C.C23.Layout.unknown with
  membersDecl := fun id => if id.value == "record-1" then some [("x", "int")] else none } :
  LeanModels.C.C23.Layout).membersDeclAt (some {value := "record-1"})
    "struct R" == some [("x", "int")]
#guard ({ LeanModels.C.C23.Layout.unknown with
  declSize := fun id => if id.value == "record-1" then some 8 else none } :
  LeanModels.C.C23.Layout).bitFieldStorageSizeAt
    (some (.declRef (some {value := "record-1"}) "r" "VarDecl" "struct R" default)) "struct R" == some 8
#guard ({ LeanModels.C.C23.Layout.unknown with
  elementSizeDecl := fun id => if id.value == "array-1" then some 4 else none } :
  LeanModels.C.C23.Layout).arrayElementSizeDeclAt (some {value := "array-1"}) "int[2]" "int" == some 4
#guard ({ LeanModels.C.C23.Layout.unknown with
  structuredType := fun id =>
    if id.value == "array-1" then some (.array (.cBuiltinKind .int) (some 2)) else none
  size := fun _ => some 4 } :
  LeanModels.C.C23.Layout).arrayElementSizeDeclAt (some {value := "array-1"})
    "int[2]" "int" == some 4
#guard ({ LeanModels.C.C23.Layout.unknown with
  structuredType := fun id =>
    if id.value == "array-1" then some (.array (.cBuiltinKind .int) (some 3)) else none
  arrayElementType := fun _ => some "int"
  elem := fun ty => if ty == "int[3]" then some ("int", 2) else none } :
  LeanModels.C.C23.Layout).elemDeclAt (some {value := "array-1"}) "int[3]" == some ("int", 3)
#guard ({ LeanModels.C.C23.Layout.unknown with
  structuredExprType := fun offset =>
    if offset == 12 then some (.pointer (.cBuiltinKind .int)) else none } :
  LeanModels.C.C23.Layout).structuredTypeAt
    (.declRef none "p" "VarDecl" "int *"
      (CSpan.mk 1 (some 12) (some 1) 1 (some 13) (some 2) none none)) ==
    some (.pointer (.cBuiltinKind .int))
#guard ({ LeanModels.C.C23.Layout.unknown with
  structuredType := fun id =>
    if id.value == "vla-1" then some (.array (.cBuiltinKind .int) none) else none
  arrayElementType := fun _ => some "int"
  elem := fun _ => some ("int", 4) } :
  LeanModels.C.C23.Layout).elemDeclAt (some {value := "vla-1"}) "int[n]" == none
#guard ({ LeanModels.C.C23.Layout.unknown with
  structuredType := fun id =>
    if id.value == "scalar-1" then some (.cBuiltinKind .int) else none
  elem := fun _ => some ("int", 4) } :
  LeanModels.C.C23.Layout).elemDeclAt (some {value := "scalar-1"}) "int" == none
#guard LeanModels.C.C23.Mem.isCharacterType
  (.qualified true false (.cBuiltinKind .unsignedChar))
#guard !LeanModels.C.C23.Mem.isCharacterType (.cBuiltin "unsigned char")
#guard LeanModels.C.C23.Mem.cAliasCompatible "int" "volatile int"
#guard LeanModels.C.C23.Mem.cAliasModel.compatibleUsed
  (some (.cBuiltinKind .unsignedChar)) "short" "int"
#guard (({ LeanModels.C.C23.Layout.unknown with
  isUnion := fun ty => ty == "union U" } : LeanModels.C.C23.Layout).isUnion "union U")
#guard (({ LeanModels.C.C23.Layout.unknown with
  isUnionDecl := fun id => id.value == "union-1" } : LeanModels.C.C23.Layout).isUnionDeclAt
    (some {value := "union-1"}) "union U")
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
