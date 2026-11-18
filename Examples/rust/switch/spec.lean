import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.switch

load_rust_program switch from "Examples/rust/switch/switch.json"

#guard switch.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run switch |>.isSome

end Examples.rust.switch
