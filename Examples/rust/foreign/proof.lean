import Examples.rust.foreign.spec

namespace Examples.rust.foreign

theorem foreign_refused : (LeanModels.Rust.run foreign).isNone := by decide

end Examples.rust.foreign
