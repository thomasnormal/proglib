import LeanModels.Sv.Kernel.Aggregate
import LeanModels.Sv.Param2

/-!
# Parser-facing aggregate shape bridge

`PDecl` retains packed type metadata and source unpacked bounds.  This bridge
turns those fields into the shared `AggType` relation at an instantiated
parameter point.  It handles scalar declarations and every finite fixed
unpacked rank.  A declaration with an unrecoverable width remains a loud
error, and no aggregate is flattened into scalar names.

Struct and union type definitions need their own parser-retained field table
before they can use this bridge.  They therefore remain outside this function
until ingestion carries those fields explicitly.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

def PType.aggregateScalar? (env : IEnv) (pd : PDecl) : Except String AggType := do
  let width ← pd.type.width env
  if width == 0 then
    throw s!"decl '{pd.name}': zero-width aggregate element"
  return .scalar { width, signed := pd.isSigned, fourState := !pd.twoState }

partial def PAggType.toAggType? (env : IEnv) : PAggType → Except String AggType
  | .scalar ty signed twoState => do
      let width ← ty.width env
      if width == 0 then throw "zero-width aggregate element"
      return .scalar { width, signed, fourState := !twoState }
  | .struct fields => do
      let fields ← fields.mapM fun (name, ty) => do
        return (name, ← PAggType.toAggType? env ty)
      return .struct fields
  | .array msb lsb elem => do
      let msb ← evalInt env msb
      let lsb ← evalInt env lsb
      return .array msb lsb (← PAggType.toAggType? env elem)

def PDecl.aggregateType? (env : IEnv) (pd : PDecl) : Except String AggType := do
  match pd.aggregate? with
  | some aggregate => return ← PAggType.toAggType? env aggregate
  | none => pure ()
  let scalar ← PType.aggregateScalar? env pd
  let rec wrap : List PDim → AggType → Except String AggType
    | [], current => .ok current
    | dim :: rest, current => do
        let msb ← evalInt env dim.msb
        let lsb ← evalInt env dim.lsb
        let nested ← wrap rest current
        return .array msb lsb nested
  wrap pd.unpackedDims scalar

private def bridgeEnv : IEnv := { vals := [("N", 2)] }

private def bridgeDecl : PDecl :=
  { name := "mem", type := .packed [⟨.int 7, .int 0⟩] (some 8),
    unpackedDims := [⟨.int 0, .binary (.m0 .sub) (.paramRef "N" none) (.int 1)⟩] }

#guard match PDecl.aggregateType? bridgeEnv bridgeDecl with
  | .ok (.array 0 1 (.scalar ty)) => ty.width == 8 && ty.fourState
  | _ => false

private def nestedBridgeDecl : PDecl :=
  { name := "grid", type := .packed [] (some 1),
    unpackedDims := [⟨.int 0, .int 1⟩, ⟨.int 3, .int 0⟩] }

#guard match PDecl.aggregateType? bridgeEnv nestedBridgeDecl with
  | .ok (.array 0 1 (.array 3 0 (.scalar ty))) => ty.width == 1
  | _ => false

end LeanModels.Sv.Kernel
