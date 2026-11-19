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

/-! An assignment pattern is kept as a value-level node until its destination
type is known.  This is the correspondence rule of IEEE 1800-2023 §10.9.
The evaluator below deliberately handles only source-shaped positional,
keyed/default, and replicated patterns.  A missing field or cell receives the
destination type's four-state unknown value, while duplicate or out-of-range
keys refuse loudly. -/

inductive AggPattern where
  | value (value : Val)
  | positional (elements : List AggPattern)
  | keyed (fields : List (String × AggPattern)) (default : Option AggPattern)
  | indexed (cells : List (Int × AggPattern)) (default : Option AggPattern)
  | replicated (count : Nat) (element : AggPattern)
deriving Inhabited

def AggPattern.coerce (ty : VType) (value : Val) : AggValue :=
  .scalar (Val.ofLVec ty value.bits)

def AggPattern.unknown (ty : AggType) : AggValue :=
  .unknown ty

def AggPattern.lookupKey (name : String) : List (String × AggPattern) → Option AggPattern
  | [] => none
  | (key, pat) :: rest => if key == name then some pat else lookupKey name rest

def AggPattern.hasKey (name : String) : List (String × AggPattern) → Bool
  | [] => false
  | (key, _) :: rest => key == name || hasKey name rest

def AggPattern.keysUnique : List (String × AggPattern) → Bool
  | [] => true
  | (key, _) :: rest => !hasKey key rest && keysUnique rest

def AggPattern.lookupIndex (index : Int) : List (Int × AggPattern) → Option AggPattern
  | [] => none
  | (key, pat) :: rest => if key == index then some pat else lookupIndex index rest

def AggPattern.hasIndex (index : Int) : List (Int × AggPattern) → Bool
  | [] => false
  | (key, _) :: rest => key == index || hasIndex index rest

def AggPattern.indicesUnique : List (Int × AggPattern) → Bool
  | [] => true
  | (index, _) :: rest => !hasIndex index rest && indicesUnique rest

def AggType.rangeValues (msb lsb : Int) : List Int :=
  if lsb ≤ msb then
    (List.range ((msb - lsb + 1).toNat)).map (fun (n : Nat) => lsb + (n : Int))
  else
    (List.range ((lsb - msb + 1).toNat)).map (fun (n : Nat) => lsb - (n : Int))

def AggPattern.keysInFields : List (String × AggType) → List (String × AggPattern) → Bool
  | _, [] => true
  | fields, (key, _) :: rest =>
      fields.any (fun p => p.1 == key) && keysInFields fields rest

def AggPattern.indicesInRange (msb lsb : Int) : List (Int × AggPattern) → Bool
  | [] => true
  | (index, _) :: rest =>
      AggType.inRange msb lsb index && indicesInRange msb lsb rest

@[simp] def AggPattern.scalarValues : List AggPattern → Option (List Val)
  | [] => some []
  | .value val :: rest => scalarValues rest |>.map (fun values => val :: values)
  | _ :: _ => none

def materializeArrayScalarValues : AggType → List Int → List Val → Except String AggValue
  | .scalar _, [], [] => .ok (.array [])
  | .scalar ty, index :: indices, value :: values => do
      let tail ← materializeArrayScalarValues (.scalar ty) indices values
      match tail with
      | .array cells => .ok (.array ((index, AggPattern.coerce ty value) :: cells))
      | _ => .error "assignment pattern internal scalar array shape mismatch"
  | _, _, _ => .error "assignment pattern replication requires scalar array elements"

def materializeArrayValues (elem : AggType) (indices : List Int) (patterns : List AggPattern) :
    Except String AggValue :=
  match elem with
  | .scalar ty =>
      match AggPattern.scalarValues patterns with
      | some values => materializeArrayScalarValues (.scalar ty) indices values
      | none => .error "assignment pattern array elements must be scalar values"
  | _ => .error "assignment pattern nested array or struct element is outside the admitted fragment"

def materializeArrayKeyedValues (indices : List Int) (elem : AggType)
    (setters : List (Int × AggPattern)) (default? : Option AggPattern) : Except String AggValue :=
  match elem with
  | .scalar ty =>
      match indices with
      | [] => .ok (.array [])
      | index :: rest =>
          let pattern := (AggPattern.lookupIndex index setters).orElse (fun _ => default?)
          let value := match pattern with
            | some (.value value) => some (AggPattern.coerce ty value)
            | some _ => none
            | none => some (AggPattern.unknown (.scalar ty))
          match value with
          | none => .error "assignment pattern array elements must be scalar values"
          | some value => do
              let tail ← materializeArrayKeyedValues rest (.scalar ty) setters default?
              match tail with
              | .array values => .ok (.array ((index, value) :: values))
              | _ => .error "assignment pattern internal keyed array shape mismatch"
  | _ => .error "assignment pattern nested array or struct element is outside the admitted fragment"

mutual
  def AggPattern.materialize : AggType → AggPattern → Except String AggValue
    | .scalar ty, .value value => .ok (AggPattern.coerce ty value)
    | .scalar ty, .keyed [] (some default) =>
        AggPattern.materialize (.scalar ty) default
    | .scalar _, _ => .error "assignment pattern does not match a scalar destination"
    | .struct fields, .positional elements =>
        if elements.length != fields.length then
          .error "assignment pattern positional field count mismatch"
        else materializeStruct fields elements
    | .struct fields, .keyed setters default? =>
        if !AggPattern.keysUnique setters then
          .error "assignment pattern contains a duplicate field key"
        else if !AggPattern.keysInFields fields setters then
          .error "assignment pattern contains an unknown field key"
        else materializeStructKeyed fields setters default?
    | .struct _, .indexed _ _ => .error "indexed assignment pattern requires an array destination"
    | .struct _, .value _ => .error "assignment pattern value does not match a struct destination"
    | .struct _, .replicated _ _ => .error "assignment pattern replication requires an array destination"
    | .array msb lsb elem, .positional elements =>
        let indices := AggType.rangeValues msb lsb
        if elements.length != indices.length then
          .error "assignment pattern positional array count mismatch"
        else materializeArrayValues elem indices elements
    | .array msb lsb elem, .indexed setters default? =>
        if !AggPattern.indicesUnique setters then
          .error "assignment pattern contains a duplicate array key"
        else if !AggPattern.indicesInRange msb lsb setters then
          .error "assignment pattern contains an out-of-range array key"
        else materializeArrayKeyedValues (AggType.rangeValues msb lsb) elem setters default?
    | .array _ _ _, .value _ => .error "assignment pattern value does not match an array destination"
    | .array _ _ _, .keyed _ _ => .error "named assignment pattern requires a struct destination"
    | .array msb lsb elem, .replicated count pattern =>
        let indices := AggType.rangeValues msb lsb
        if count == 0 || indices.length % count != 0 then
          .error "assignment pattern replication does not cover the array"
        else
          let groupSize := indices.length / count
          match pattern with
          | .value value => materializeArrayScalarValues elem indices (List.replicate indices.length value)
          | .positional elements =>
              if elements.length != groupSize then
                .error "assignment pattern replicated group count mismatch"
              else
                match AggPattern.scalarValues elements with
                | some values => materializeArrayScalarValues elem indices
                    (List.flatten (List.replicate count values))
                | none => .error "assignment pattern replication requires scalar elements"
          | _ => .error "assignment pattern replicated element is not positional"
  termination_by ty pattern => sizeOf ty + sizeOf pattern

  def materializeStruct : List (String × AggType) → List AggPattern → Except String AggValue
    | [], [] => .ok (.struct [])
    | (name, ty) :: fields, pattern :: patterns => do
        let value ← AggPattern.materialize ty pattern
        let tail ← materializeStruct fields patterns
        match tail with
        | .struct values => .ok (.struct ((name, value) :: values))
        | _ => .error "assignment pattern internal struct shape mismatch"
    | _, _ => .error "assignment pattern internal struct arity mismatch"
  termination_by fields patterns => sizeOf fields + sizeOf patterns

  def materializeStructKeyed : List (String × AggType) → List (String × AggPattern) →
      Option AggPattern → Except String AggValue
    | [], _, _ => .ok (.struct [])
    | (name, ty) :: fields, setters, default? => do
        let pattern := (AggPattern.lookupKey name setters).orElse (fun _ => default?)
        let value ← match pattern, ty with
          | none, _ => .ok (AggPattern.unknown ty)
          | some (.value raw), .scalar scalarTy => .ok (AggPattern.coerce scalarTy raw)
          | some _, _ => .error "assignment pattern keyed field is not a scalar value"
        let tail ← materializeStructKeyed fields setters default?
        match tail with
        | .struct values => .ok (.struct ((name, value) :: values))
        | _ => .error "assignment pattern internal keyed struct shape mismatch"
  termination_by fields setters default => sizeOf fields + sizeOf setters + sizeOf default
end

/-! An untouched aggregate is represented compactly as `.unknown ty`.  A
member write materializes that type-shaped value so the write preserves the
unknown value of every sibling field.  The source-shaped aggregate remains a
single cell throughout this operation. -/

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

private def patternPairTy : AggType :=
  .struct [("a", .scalar wordTy), ("b", .scalar wordTy), ("c", .scalar wordTy)]

private def patternArrayTy : AggType := .array 0 3 (.scalar wordTy)

private def patternXz : Val := Val.ofLVec wordTy (LVec.lit "xz01")

private def aggregateBits? (value : AggValue) (path : AggPath) : Option String :=
  (value.read? path).map (fun v => v.bits.toBinString)

#guard match AggPattern.materialize patternPairTy
    (.keyed [("b", .value (wordVal 2)), ("a", .value (wordVal 1))] none) with
  | .ok value =>
      aggregateBits? value [.field "a"] == some "0001" &&
      aggregateBits? value [.field "b"] == some "0010"
  | .error _ => false

#guard match AggPattern.materialize patternPairTy
    (.keyed [("a", .value (wordVal 1))] none) with
  | .ok value => aggregateBits? value [.field "c"] == some "xxxx"
  | .error _ => false

#guard match AggPattern.materialize patternPairTy
    (.keyed [("a", .value (wordVal 1))] (some (.value (wordVal 9)))) with
  | .ok value => aggregateBits? value [.field "b"] == some "1001"
  | .error _ => false

#guard match AggPattern.materialize patternArrayTy
    (.replicated 2 (.value (wordVal 5))) with
  | .ok value =>
      aggregateBits? value [.index 0] == some "0101" &&
      aggregateBits? value [.index 3] == some "0101"
  | .error _ => false

#guard match AggPattern.materialize patternPairTy
    (.keyed [("a", .value (wordVal 1)), ("a", .value (wordVal 2))] none) with
  | .error _ => true
  | .ok _ => false

#guard match AggPattern.materialize (.scalar wordTy) (.value patternXz) with
  | .ok value => aggregateBits? value [] == some "xz01"
  | .error _ => false

end LeanModels.Sv.Kernel
