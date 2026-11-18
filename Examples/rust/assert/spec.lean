import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.assert

load_rust_program assert from "Examples/rust/assert/assert.json"

#guard assert.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run assert |>.isSome

end Examples.rust.assert
