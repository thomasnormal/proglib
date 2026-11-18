import Examples.rust.drop.spec

namespace Examples.rust.drop

theorem drop_runs : (LeanModels.Rust.run drop).isSome := by decide

theorem drop_in_steps {trace : LeanModels.Rust.Trace}
    (h : LeanModels.Rust.run drop = some trace) :
    LeanModels.Rust.ProgramInSteps drop trace := by
  exact LeanModels.Rust.run_in_steps h

end Examples.rust.drop
