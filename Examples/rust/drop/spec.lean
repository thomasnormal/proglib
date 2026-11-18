import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.drop

load_rust_program drop from "Examples/rust/drop/drop.json"

#guard drop.schema == LeanModels.Rust.acceptedSchema
#guard (match LeanModels.Rust.runOutcome drop with
  | .refused (.unsupported "assignment") => true
  | _ => false)

end Examples.rust.drop
