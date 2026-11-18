import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.assign

load_rust_program assign from "Examples/rust/assign/assign.json"

#guard assign.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run assign |>.isSome

end Examples.rust.assign
