import Examples.rust.drop.spec

namespace Examples.rust.drop

theorem drop_runs : (LeanModels.Rust.run drop).isSome := by decide

theorem drop_in_steps {trace : LeanModels.Rust.Trace}
    (h : LeanModels.Rust.run drop = some trace) :
    LeanModels.Rust.ProgramInSteps drop trace := by
  exact LeanModels.Rust.run_in_steps h

theorem drop_trace_in_steps :
    LeanModels.Rust.ProgramInSteps drop {
      state := { locals := [(1, .uninit), (0, .value 0)] },
      events := [
        .storageLive 1, .assign 1 0, .assign 0 0,
        .drop 1, .storageDead 1] } := by
  apply LeanModels.Rust.run_in_steps
  decide

end Examples.rust.drop
