import Examples.rust.call.spec

namespace Examples.rust.call

theorem call_refused : (LeanModels.Rust.run call).isNone := by decide

end Examples.rust.call
