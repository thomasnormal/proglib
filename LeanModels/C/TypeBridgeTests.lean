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

private def structuredEnvelope : Envelope :=
  { schemaVersion := "c-0.1"
    language := "c"
    frontendVersion := pinnedFrontendVersion
    profileId := "test"
    profileFlags := []
    sourceFile := "bridge.c"
    sourceSha256 := ""
    unit := { items := [] }
    externals := []
    structuredTypes := [{ declaration := { value := "decl-1" }
                          type := .qualified true false (.cBuiltinKind .int) }] }

#guard structuredEnvelope.structuredTypeFor {value := "decl-1"} ==
  some (.qualified true false (.cBuiltinKind .int))
#guard structuredEnvelope.structuredTypeFor {value := "missing"} == none
#guard (({ structuredEnvelope with
    structuredTypes := structuredEnvelope.structuredTypes ++
      [{ declaration := { value := "decl-1" }
         type := .cBuiltinKind .unsignedInt }] } : Envelope).structuredTypeFor
    {value := "decl-1"} == none)

#guard LeanModels.C.C23.Mem.cAliasCompatibleStructured
  (.cBuiltinKind .int) (.qualified true false (.cBuiltinKind .int))
#guard LeanModels.C.C23.Mem.cAliasCompatibleStructured
  (.cBuiltinKind .char) (.pointer (.cBuiltinKind .int))
#guard !LeanModels.C.C23.Mem.cAliasCompatibleStructured
  (.cBuiltinKind .int) (.cBuiltinKind .unsignedInt)
private def structuredAllocCheck : Bool :=
  let result := LeanModels.C.C23.Mem.empty.allocStructured
    LeanModels.C.C23.Duration.automatic 4 (some "int") (some (.cBuiltinKind .int))
  result.1.structuredType? result.2 == some (.cBuiltinKind .int)

#guard structuredAllocCheck

private def structuredAtAllocCheck : Bool :=
  let m := LeanModels.C.C23.Mem.empty
  (m.allocAtStructured LeanModels.C.C23.Duration.automatic 4 (some "int")
    (some (.cBuiltinKind .int)) 128).1.structuredType?
      (m.allocStructured LeanModels.C.C23.Duration.automatic 4 (some "int")
        (some (.cBuiltinKind .int))).2 == some (.cBuiltinKind .int)

#guard structuredAtAllocCheck

private def structuredCopyCheck : Bool :=
  let m := LeanModels.C.C23.Mem.empty
  let allocated := m.allocStructured LeanModels.C.C23.Duration.allocated 4
    (some "int") (some (.cBuiltinKind .int))
  let copied := allocated.1.copyStructuredType allocated.2 9
  copied.structuredType? 9 == some (.cBuiltinKind .int)

#guard structuredCopyCheck

private def structuredReallocCheck : Bool :=
  let m := LeanModels.C.C23.Mem.empty
  let allocated := m.allocStructured LeanModels.C.C23.Duration.allocated 4
    (some "int") (some (.cBuiltinKind .int))
  let p := LeanModels.C.C23.Ptr.toObjectBound allocated.2 4
  match allocated.1.reallocAt p 8 256 with
  | .error _ => false
  | .ok (m', q) =>
      match q.obj with
      | some fresh => m'.structuredType? fresh == some (.cBuiltinKind .int)
      | none => false

#guard structuredReallocCheck

private def structuredStoreCheck : Bool :=
  let m := LeanModels.C.C23.Mem.empty
  let allocated := m.allocStructured LeanModels.C.C23.Duration.allocated 4
    (some "int") (some (.cBuiltinKind .int))
  let p := LeanModels.C.C23.Ptr.toObjectBound allocated.2 4
  match allocated.1.storeInt p LeanModels.C.C23.IntTy.int_ 7 with
  | .error _ => false
  | .ok m' =>
      m'.structuredType? allocated.2 == some (.cBuiltinKind .int)

#guard structuredStoreCheck

private def allocatedEffectiveTypeCheck : Bool :=
  let m := LeanModels.C.C23.Mem.empty
  let allocated := m.alloc LeanModels.C.C23.Duration.allocated 4 none
  let p := LeanModels.C.C23.Ptr.toObjectBound allocated.2 4
  match allocated.1.storeIntChecked LeanModels.C.C23.Mem.cAliasModel p
      LeanModels.C.C23.IntTy.int_ "int" 7 with
  | .error _ => false
  | .ok m' =>
      match m'.get? allocated.2 with
      | some c => c.effTy == some "int"
      | none => false

#guard allocatedEffectiveTypeCheck

private def allocatedStructuredLookupCheck : Bool :=
  let m := LeanModels.C.C23.Mem.empty
  let allocated := m.alloc LeanModels.C.C23.Duration.allocated 4 none
  let p := LeanModels.C.C23.Ptr.toObjectBound allocated.2 4
  match allocated.1.storeIntChecked LeanModels.C.C23.Mem.cAliasModel p
      LeanModels.C.C23.IntTy.int_ "int" 7 with
  | .error _ => false
  | .ok m' => m'.structuredType? allocated.2 == m.structuredType? allocated.2

#guard allocatedStructuredLookupCheck

private def compoundRegistryCheck : Bool :=
  let m := LeanModels.C.C23.Mem.empty
  let span : LeanModels.C.CSpan := default
  (m.rememberCompound span 7).structuredType? 7 == none

#guard compoundRegistryCheck

#guard LeanModels.C.C23.Ptr.fromExposedAddress 1 == none
#guard LeanModels.C.C23.Ptr.fromExposedAddress 0 == some LeanModels.C.C23.Ptr.null

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
#guard LeanModels.C.C23.pointerTypeOfNode
  (some (.qualified true false (.pointer (.cBuiltinKind .int))))
#guard !LeanModels.C.C23.pointerTypeOfNode
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
#guard LeanModels.C.C23.pointerIntegerTypeOfNode
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
    (.declRef (some {value := "array-1"}) "a" "VarDecl" "int[2]" default none) "int" == some 4
#guard ({ LeanModels.C.C23.Layout.unknown with
  fieldOffDecl := fun id field =>
    if id.value == "record-1" && field == "x" then some 8 else none } :
  LeanModels.C.C23.Layout).fieldOffAt
    (.declRef (some {value := "record-1"}) "r" "VarDecl" "struct R" default none) "x" == some 8
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
    (.declRef (some {value := "record-1"}) "r" "VarDecl" "struct R" default none) "x" "int" true == some 4
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
    (some (.declRef (some {value := "record-1"}) "r" "VarDecl" "struct R" default none)) "struct R" == some 8
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
      (CSpan.mk 1 (some 12) (some 1) 1 (some 13) (some 2) none none) none) ==
    some (LeanModels.Clang.QualType.pointer (.cBuiltinKind .int))
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
#guard LeanModels.C.C23.Mem.cAliasCompatibleStructured
  (.cBuiltinKind .unsignedChar) (.cBuiltinKind .int)
#guard !LeanModels.C.C23.Mem.cAliasModel.compatibleUsed
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
  (.cast "BitCast" (.unsupported "Opaque" "" default) "opaque" default none)
#guard isError (TypeNode.typedefRef none "T" |>.toQualType)
#guard isError (TypeNode.enumeration none "enum E" |>.toQualType)

end LeanModels.C
