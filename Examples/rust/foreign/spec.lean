import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.foreign

load_rust_program foreign from "Examples/rust/foreign/foreign.json"

#guard foreign.schema == LeanModels.Rust.acceptedSchema
#guard LeanModels.Rust.run foreign |>.isNone
#guard LeanModels.Rust.Outcome.label (LeanModels.Rust.runOutcome foreign) ==
  "refused:unsupported:call target has no MIR body: _RNvNtCsadZFJLPwbP2_3std7process4exit"

end Examples.rust.foreign
