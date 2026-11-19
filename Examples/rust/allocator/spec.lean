import LeanModels.Rust.Load
import LeanModels.Rust.Semantics

namespace Examples.rust.allocator

load_rust_program allocator from "Examples/rust/allocator/allocator.json"

#guard allocator.schema == LeanModels.Rust.acceptedSchema
#guard allocator.bodies.length > 0
#guard allocator.calls.any (fun edge =>
  edge.callee.map (·.contains "__rust_alloc") |>.getD false)
#guard allocator.calls.any (fun edge =>
  edge.callee.map (·.contains "__rust_alloc_zeroed") |>.getD false)
#guard LeanModels.Rust.Outcome.label (LeanModels.Rust.runOutcome allocator) |>.startsWith "refused:"
#guard LeanModels.Rust.allocatorForeignSpec
  "_RNvCseLJZi906U4A_7___rustc12___rust_alloc" ==
  some (.allocator false 2)
#guard LeanModels.Rust.allocatorForeignSpec
  "_RNvCseLJZi906U4A_7___rustc19___rust_alloc_zeroed" ==
  some (.allocator true 2)

end Examples.rust.allocator
