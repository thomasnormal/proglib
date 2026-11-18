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
deriving Inhabited

def AggValue.read? : AggValue → AggPath → Option Val
  | .scalar value, [] => some value
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

def AggValue.write? : AggValue → AggPath → Val → Option AggValue
  | .scalar _, [], value => some (.scalar value)
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

end LeanModels.Sv.Kernel
