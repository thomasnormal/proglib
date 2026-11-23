import LeanModels.C.Ast

/-!
# F2 shared byte store

This is the first S2 slice. Storage is parameterised by the language's tag,
allocation metadata, effective-type state, hook choice, and fault type. The
operations expose byte footprints and return a refusal when a request is
outside the current store. C23/Memory remains the legacy evaluator store
until the language instance and its replay rows are complete.
-/

namespace LeanModels.C.F2

abbrev AllocId := Nat

structure Provenance (Tag : Type) where
  allocation : AllocId
  tag : Tag
deriving Repr, BEq

inductive Byte (Tag : Type) where
  | uninitialized
  | value (bits : UInt8) (provenance : Option (Provenance Tag))
      (fragment : Option Nat)
deriving Repr, BEq

structure Allocation (Tag State : Type) where
  live : Bool
  bytes : List (Byte Tag)
  state : State
deriving Repr

structure Store (Tag State : Type) where
  allocations : List (AllocId × Allocation Tag State)
  nextId : AllocId
deriving Repr

structure Region where
  allocation : AllocId
  offset : Nat
  width : Nat
deriving Repr, BEq

inductive AccessKind where
  | read | write | metadata
deriving Repr, BEq

structure Footprint where
  accesses : List (AccessKind × Region)
deriving Repr

structure Fault (F : Type) where
  value : F
deriving Repr

inductive Result (Tag State F A : Type) where
  | ok (value : A) (store : Store Tag State) (footprint : Footprint)
  | fault (error : Fault F) (store : Store Tag State) (footprint : Footprint)
  | refused (reason : String) (store : Store Tag State) (footprint : Footprint)
deriving Repr

def lookup (store : Store Tag State) (id : AllocId) : Option (Allocation Tag State) :=
  store.allocations.find? (fun entry => entry.1 == id) |>.map (·.2)

def bytesWf (id : AllocId) : List (Byte Tag) → Prop
  | [] => True
  | .uninitialized :: rest => bytesWf id rest
  | .value _ none _ :: rest => bytesWf id rest
  | .value _ (some provenance) _ :: rest =>
      provenance.allocation == id ∧ bytesWf id rest

def allocationsWf : List (AllocId × Allocation Tag State) → Prop
  | [] => True
  | (id, allocation) :: rest =>
      bytesWf id allocation.bytes ∧
      allocationsWf rest ∧
      ∀ other, (other, _) ∈ rest → id ≠ other

def WellFormed (store : Store Tag State) : Prop :=
  allocationsWf store.allocations

def footprint (kind : AccessKind) (region : Region) : Footprint :=
  { accesses := [(kind, region)] }

def storeByte (store : Store Tag State) (id offset : Nat)
    (byte : Byte Tag) : Option (Store Tag State × Footprint) := do
  let allocation ← lookup store id
  if !allocation.live then none
  else if offset ≥ allocation.bytes.length then none
  else
    let bytes := allocation.bytes.set! offset byte
    let updated := { allocation with bytes := bytes }
    let allocations := store.allocations.map (fun entry =>
      if entry.1 == id then (id, updated) else entry)
    some ({ store with allocations := allocations }, footprint .write
      { allocation := id, offset := offset, width := 1 })

def loadByte (store : Store Tag State) (id offset : Nat) :
    Option (Byte Tag × Footprint) := do
  let allocation ← lookup store id
  if !allocation.live then none
  else
    let byte ← allocation.bytes[offset]?
    some (byte, footprint .read { allocation := id, offset := offset, width := 1 })

theorem storeByte_wf {Tag State : Type} (store : Store Tag State)
    (hstore : WellFormed store) (id offset : Nat) (byte : Byte Tag)
    (result : Store Tag State × Footprint)
    (hresult : storeByte store id offset byte = some result) :
    WellFormed result.1 := by
  simp [storeByte] at hresult
  split at hresult <;> simp_all [WellFormed, allocationsWf, bytesWf]

theorem loadByte_wf {Tag State : Type} (store : Store Tag State)
    (hstore : WellFormed store) (id offset : Nat)
    (result : Byte Tag × Footprint)
    (hresult : loadByte store id offset = some result) :
    WellFormed store := hstore

#guard (bytesWf 3 [Byte.uninitialized] : Prop) = True
#guard (footprint .read { allocation := 1, offset := 0, width := 1 }).accesses.length == 1

end LeanModels.C.F2
