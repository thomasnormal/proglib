import Examples.rust.call.spec

namespace Examples.rust.call

theorem call_runs : (LeanModels.Rust.run call).isSome := by decide

theorem call_in_steps {trace : LeanModels.Rust.Trace}
    (h : LeanModels.Rust.run call = some trace) :
    LeanModels.Rust.ProgramInSteps call trace := by
  exact LeanModels.Rust.run_in_steps h

end Examples.rust.call
