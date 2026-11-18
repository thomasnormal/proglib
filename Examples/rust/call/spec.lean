import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.call

load_rust_program call from "Examples/rust/call/call.json"

#guard call.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run call |>.isNone

end Examples.rust.call
