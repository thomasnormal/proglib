import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.storage

load_rust_program storage from "Examples/rust/storage/storage.json"

#guard storage.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run storage |>.isSome

end Examples.rust.storage
