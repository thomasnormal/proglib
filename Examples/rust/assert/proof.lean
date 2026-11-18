import Examples.rust.assert.spec

namespace Examples.rust.assert

theorem assert_runs : (LeanModels.Rust.run assert).isSome := by decide

end Examples.rust.assert
