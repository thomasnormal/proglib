import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.control

load_rust_program control from "Examples/rust/control/control.json"

#guard control.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run control |>.isSome

end Examples.rust.control
