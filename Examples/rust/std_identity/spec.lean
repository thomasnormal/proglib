import LeanModels.Rust.Load
import LeanModels.Rust.Semantics
namespace Examples.rust.stdIdentity
load_rust_program stdIdentity from "Examples/rust/std_identity/std_identity.json"
#guard stdIdentity.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run stdIdentity |>.isSome
end Examples.rust.stdIdentity
