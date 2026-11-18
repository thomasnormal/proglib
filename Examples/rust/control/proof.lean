import Examples.rust.control.spec

namespace Examples.rust.control

theorem control_runs : (LeanModels.Rust.run control).isSome := by decide

end Examples.rust.control
