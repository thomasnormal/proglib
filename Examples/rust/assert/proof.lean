import Examples.rust.assert.spec

namespace Examples.rust.assert

theorem assert_runs : (LeanModels.Rust.run assert).isSome := by decide

theorem assert_trace_in_steps :
    LeanModels.Rust.ProgramInSteps assert {
      state := {
        locals := [
          (1, .uninit), (2, .uninit), (0, .value 0), (3, .uninit),
          (4, .uninit), (5, .uninit), (9, .value 0), (8, .value 0),
          (7, .value 0), (6, .value 0)] },
      events := [
        .storageLive 1, .assign 1 8, .storageLive 2,
        .assign 2 2, .storageLive 3, .storageLive 4,
        .assign 4 8, .storageLive 5, .assign 5 2,
        .assign 6 0, .assign 7 0, .assign 8 0,
        .assign 9 0, .assign 3 4, .storageDead 5,
        .storageDead 4, .placeMention 3, .storageDead 3,
        .assign 0 0, .storageDead 2, .storageDead 1] } := by
  apply LeanModels.Rust.run_in_steps
  rfl

end Examples.rust.assert
