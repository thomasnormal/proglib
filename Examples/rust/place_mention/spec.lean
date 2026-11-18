import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.placeMention

load_rust_program placeMention from "Examples/rust/place_mention/place_mention.json"

#guard placeMention.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run placeMention |>.isSome

end Examples.rust.placeMention
