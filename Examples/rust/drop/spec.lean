import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.drop

load_rust_program drop from "Examples/rust/drop/drop.json"

#guard drop.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.Outcome.isReturned (LeanModels.Rust.runOutcome drop)

end Examples.rust.drop
