import Examples.rust.assign.spec

namespace Examples.rust.assign

theorem assign_runs : (LeanModels.Rust.run assign).isSome := by decide

theorem assign_trace :
    LeanModels.Rust.run assign = some {
      state := { locals := [(1, .uninit), (0, .value 0)] },
      events := [.storageLive 1, .assign 1 1, .assign 1 2,
        .placeMention 1, .assign 0 0, .storageDead 1] } := by
  decide

theorem assign_trace_in_steps :
    LeanModels.Rust.ProgramInSteps assign {
      state := { locals := [(1, .uninit), (0, .value 0)] },
      events := [.storageLive 1, .assign 1 1, .assign 1 2,
        .placeMention 1, .assign 0 0, .storageDead 1] } := by
  exact LeanModels.Rust.run_in_steps assign_trace

end Examples.rust.assign
