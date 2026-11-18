import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.gcd

load_rust_program gcd from "Examples/rust/gcd/gcd.json"

def gcdBody : LeanModels.Rust.Body :=
  (gcd.bodies.find? (fun body => body.instanceId.endsWith "3gcd")).getD
    { instanceId := "missing", blocks := [] }

def gcdInput (a b : Nat) : LeanModels.Rust.State :=
  { locals := [(1, .value a), (2, .value b)], types := gcd.types }

#guard gcd.schema == LeanModels.Rust.acceptedSchema
#guard (LeanModels.Rust.cfgRunOutcome 4096 gcdBody 0 (gcdInput 48 18)).isReturned

end Examples.rust.gcd
