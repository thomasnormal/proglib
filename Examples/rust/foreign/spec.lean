import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.foreign

load_rust_program foreign from "Examples/rust/foreign/foreign.json"

#guard foreign.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run foreign |>.isNone

end Examples.rust.foreign
