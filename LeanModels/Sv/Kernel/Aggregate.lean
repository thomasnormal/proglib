import LeanModels.Sv.Kernel.Core0E

/-!
# Source-shaped aggregate values for E

IEEE 1800-2023 §§6.8, 6.18 and 11.8 make a struct or fixed unpacked array a
single declared value with named or indexed subobjects. This module keeps that
shape in the E value relation. A member path is data, and a read or write walks
the corresponding source-shaped value. No field name is reconstructed from a
display string and no aggregate is flattened into scalar declarations.

The parser-facing `PType`/`PDecl` bridge is intentionally a later layer. The
relation here is the shared semantic target for that bridge.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

inductive AggType where
  | scalar (ty : VType)
  | struct (fields : List (String × AggType))
  | array (msb lsb : Int) (elem : AggType)
deriving Repr, Inhabited

inductive AggStep where
  | field (name : String)
  | index (value : Int)
deriving Repr, DecidableEq, Inhabited

abbrev AggPath := List AggStep

def AggType.inRange (msb lsb value : Int) : Prop :=
  (lsb ≤ msb ∧ lsb ≤ value ∧ value ≤ msb) ∨
    (msb < lsb ∧ msb ≤ value ∧ value ≤ lsb)

instance aggTypeDecidableInRange (msb lsb value : Int) :
    Decidable (AggType.inRange msb lsb value) := by
  unfold AggType.inRange
  infer_instance

def AggType.resolve? : AggType → AggPath → Option VType
  | .scalar ty, [] => some ty
  | .scalar _, _ :: _ => none
  | .struct fields, .field name :: rest =>
      (fields.find? (fun p => p.1 == name)).bind fun p => p.2.resolve? rest
  | .struct _, .index _ :: _ => none
  | .struct _, [] => none
  | .array msb lsb elem, .index value :: rest =>
      if AggType.inRange msb lsb value then elem.resolve? rest else none
  | .array _ _ _, .field _ :: _ => none
  | .array _ _ _, [] => none

inductive AggValue where
  | scalar (value : Val)
  | struct (fields : List (String × AggValue))
  | array (cells : List (Int × AggValue))
  /-- An aggregate whose bits have not been written.  Keeping its type lets a
  read return the exact-width four-state x value without flattening cells. -/
  | unknown (ty : AggType)
deriving Inhabited

/-! An untouched aggregate is represented compactly as `.unknown ty`.  A
member write materializes that type-shaped value so the write preserves the
unknown value of every sibling field.  The source-shaped aggregate remains a
single cell throughout this operation. -/

def AggType.rangeValues (msb lsb : Int) : List Int :=
  if lsb ≤ msb then
    (List.range ((msb - lsb + 1).toNat)).map (fun (n : Nat) => lsb + (n : Int))
  else
    (List.range ((lsb - msb + 1).toNat)).map (fun (n : Nat) => lsb - (n : Int))

def AggValue.read? : AggValue → AggPath → Option Val
  | .scalar value, [] => some value
  | .unknown ty, path => (ty.resolve? path).map fun valueTy =>
      Val.ofLVec valueTy (LVec.xVec valueTy.width)
  | .scalar _, _ :: _ => none
  | .struct fields, .field name :: rest =>
      (fields.find? (fun p => p.1 == name)).bind fun p => p.2.read? rest
  | .struct _, .index _ :: _ => none
  | .struct _, [] => none
  | .array cells, .index value :: rest =>
      (cells.find? (fun p => p.1 == value)).bind fun p => p.2.read? rest
  | .array _, .field _ :: _ => none
  | .array _, [] => none

def AggValue.replaceField (name : String) (value : AggValue) :
    List (String × AggValue) → Option (List (String × AggValue))
  | [] => none
  | (field, old) :: rest =>
      if field == name then some ((field, value) :: rest)
      else replaceField name value rest |>.map fun tail => (field, old) :: tail

def AggValue.replaceCell (index : Int) (value : AggValue) :
    List (Int × AggValue) → Option (List (Int × AggValue))
  | [] => none
  | (label, old) :: rest =>
      if label == index then some ((label, value) :: rest)
      else replaceCell index value rest |>.map fun tail => (label, old) :: tail

def AggValue.writeUnknown : AggType → AggPath → Val → Option AggValue
  | .scalar _, [], value => some (.scalar value)
  | .scalar _, _ :: _, _ => none
  | .struct fields, .field name :: rest, value => do
      let (_, fieldTy) ← fields.find? (fun p => p.1 == name)
      let updated ← AggValue.writeUnknown fieldTy rest value
      let unknowns := fields.map fun (field, ty) => (field, AggValue.unknown ty)
      return .struct (← AggValue.replaceField name updated unknowns)
  | .struct _, _ :: _, _ => none
  | .struct _, [], _ => none
  | .array msb lsb elem, .index index :: rest, value => do
      if !AggType.inRange msb lsb index then none
      else
        let updated ← AggValue.writeUnknown elem rest value
        let unknowns := (AggType.rangeValues msb lsb).map
          (fun cell => (cell, AggValue.unknown elem))
        return .array (← AggValue.replaceCell index updated unknowns)
  | .array _ _ _, _ :: _, _ => none
  | .array _ _ _, [], _ => none

def AggValue.write? : AggValue → AggPath → Val → Option AggValue
  | .scalar _, [], value => some (.scalar value)
  | .unknown ty, path, value => AggValue.writeUnknown ty path value
  | .scalar _, _ :: _, _ => none
  | .struct fields, .field name :: rest, value => do
      let (field, old) ← fields.find? (fun p => p.1 == name)
      let updated ← old.write? rest value
      let fields' ← replaceField field updated fields
      return .struct fields'
  | .struct _, .index _ :: _, _ => none
  | .struct _, [], _ => none
  | .array cells, .index index :: rest, value => do
      let (label, old) ← cells.find? (fun p => p.1 == index)
      let updated ← old.write? rest value
      let cells' ← replaceCell label updated cells
      return .array cells'
  | .array _, .field _ :: _, _ => none
  | .array _, [], _ => none

def AggValue.root (value : Val) : AggValue := .scalar value

/-! ## Aggregate cells in the E store

An aggregate declaration occupies one source-shaped cell identified by the
same `VarId` used by E's scalar store.  The value is kept as an `AggValue`
alongside its `AggType`, so a member path never becomes a fabricated scalar
name.  This relation is deliberately independent of the scheduler until the
member-expression admission adds its parser-shaped node. -/

structure AggCell where
  ty : AggType
  value : AggValue

structure AggStore where
  cells : VarId → Option AggCell

def AggStore.empty : AggStore := { cells := fun _ => none }

def AggStore.ofCells (cells : List (VarId × AggCell)) : AggStore :=
  { cells := fun id => cells.find? (fun p => p.1 == id) |>.map (·.2) }

def AggStore.read? (s : AggStore) (id : VarId) (path : AggPath) : Option Val := do
  let cell ← s.cells id
  cell.value.read? path

def AggStore.write? (s : AggStore) (id : VarId) (path : AggPath) (value : Val) : Option AggStore := do
  let cell ← s.cells id
  let updated ← cell.value.write? path value
  return { cells := fun id' => if id' = id then some { cell with value := updated } else s.cells id' }

theorem AggStore.read_write_root {s : AggStore} {id : VarId}
    {new : Val} {s' : AggStore}
    (hw : s.write? id [] new = some s') :
    s'.read? id [] = some new := by
  generalize hc : s.cells id = oc at hw
  cases oc with
  | none => simp [AggStore.write?, hc] at hw
  | some cell =>
      generalize hu : cell.value.write? [] new = ou at hw
      cases ou with
      | none => simp [AggStore.write?, hc, hu] at hw
      | some updated =>
          simp [AggStore.write?, hc, hu] at hw
          cases hw
          cases hv : cell.value with
          | scalar old =>
              simp [AggValue.write?, hv] at hu
              cases hu
              simp [AggStore.read?, AggValue.read?]
          | struct fields => simp [AggValue.write?, hv] at hu
          | array cells => simp [AggValue.write?, hv] at hu
          | unknown ty =>
              cases ty with
              | scalar scalarTy =>
                  simp [AggValue.write?, AggValue.writeUnknown, hv] at hu
                  cases hu
                  simp [AggStore.read?, AggValue.read?]
              | struct fields => simp [AggValue.write?, AggValue.writeUnknown, hv] at hu
              | array msb lsb elem => simp [AggValue.write?, AggValue.writeUnknown, hv] at hu

theorem AggStore.read_write_other {s : AggStore} {id other : VarId} {path : AggPath}
    {new : Val} {s' : AggStore} (hne : other ≠ id)
    (hw : s.write? id path new = some s') :
    s'.read? other path = s.read? other path := by
  generalize hc : s.cells id = oc at hw
  cases oc with
  | none => simp [AggStore.write?, hc] at hw
  | some cell =>
      generalize hu : cell.value.write? path new = ou at hw
      cases ou with
      | none => simp [AggStore.write?, hc, hu] at hw
      | some updated =>
          simp [AggStore.write?, hc, hu] at hw
          cases hw
          simp [AggStore.read?, hne]

theorem AggStore.write_cell_preserves_type {s : AggStore} {id : VarId} {path : AggPath}
    {new : Val} {s' : AggStore} {cell : AggCell}
    (hc : s.cells id = some cell)
    (hw : s.write? id path new = some s') :
    ∃ cell', s'.cells id = some cell' ∧ cell'.ty = cell.ty := by
  generalize hu : cell.value.write? path new = ou at hw
  cases ou with
  | none => simp [AggStore.write?, hc, hu] at hw
  | some updated =>
      simp [AggStore.write?, hc, hu] at hw
      cases hw
      refine ⟨{ ty := cell.ty, value := updated }, ?_, rfl⟩
      simp [AggStore.write?, hc, hu]

theorem AggValue.read_root (value : Val) : (AggValue.root value).read? [] = some value := by
  rfl

theorem AggValue.write_root (old value : Val) :
    (AggValue.root old).write? [] value = some (AggValue.root value) := by
  rfl

private def wordTy : VType := { width := 4, signed := false, fourState := true }

private def wordVal (n : Nat) : Val := Val.ofLVec wordTy (LVec.ofNat 4 n)

private def pairValue : AggValue :=
  .struct [("value", .scalar (wordVal 10)), ("valid", .scalar (wordVal 1))]

private def bundleValue : AggValue :=
  .struct [("words", .array [(0, pairValue), (1, pairValue)])]

#guard (bundleValue.read? [.field "words", .index 0, .field "value"]).map
    (fun v => v.bits.toBinString) == some "1010"
#guard match bundleValue.write? [.field "words", .index 1, .field "value"] (wordVal 3) with
  | some updated => (updated.read? [.field "words", .index 1, .field "value"]).map
      (fun v => v.bits.toBinString) == some "0011"
  | none => false
#guard match bundleValue.read? [.field "words", .index 9, .field "value"] with
  | none => true
  | some _ => false

private def aggregateStore : AggStore :=
  { cells := fun id => if id.decl == 0 then some { ty := .struct [("value", .scalar wordTy)],
                                                     value := .struct [("value", .scalar (wordVal 7))] }
                                    else none }

#guard (aggregateStore.read? { decl := 0 } [.field "value"] |>.map
    (fun v => v.bits.toBinString)) == some "0111"
#guard match aggregateStore.write? { decl := 0 } [.field "value"] (wordVal 2) with
  | some updated => (updated.read? { decl := 0 } [.field "value"] |>.map
      (fun v => v.bits.toBinString)) == some "0010"
  | none => false

end LeanModels.Sv.Kernel
