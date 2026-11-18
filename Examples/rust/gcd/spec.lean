import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.gcd

load_rust_program gcd from "Examples/rust/gcd/gcd.json"

def gcdBody : LeanModels.Rust.Body :=
  (gcd.bodies.drop 1).head?.getD
    { instanceId := "missing", blocks := [] }

def gcdType : LeanModels.Rust.TypeLayout :=
  { id := Nat.repr 1, kind := "RigidTy(Uint(U32))", sizeBits := some 32,
    align := some 4, signed := some false }

def gcdInput (a b : Nat) : LeanModels.Rust.State :=
  { locals := [(1, .value a), (2, .value b)], types := [gcdType] }

#guard gcd.schema == LeanModels.Rust.acceptedSchema
#guard (LeanModels.Rust.cfgRunOutcome 4096 gcdBody 0 (gcdInput 48 18)).isReturned

end Examples.rust.gcd
