import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.loop

load_rust_program loop from "Examples/rust/loop/loop.json"

#guard loop.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run loop |>.isSome

end Examples.rust.loop
