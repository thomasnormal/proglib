import Examples.rust.loop.spec

namespace Examples.rust.loop

theorem loop_runs : (LeanModels.Rust.run loop).isSome := by decide

theorem loop_trace :
    LeanModels.Rust.run loop = some {
      state := { locals := [(0, .value 0), (1, .uninit)] },
      events := [
        .storageLive 1,
        .call "_RNvCs0ynxh6IOg33_4loop9countdown",
        .storageLive 1, .assign 1 2, .storageLive 3, .storageLive 4,
        .assign 4 2, .assign 3 1, .storageDead 4, .assign 1 0,
        .assign 2 0, .storageDead 3, .storageLive 3, .storageLive 4,
        .assign 4 0, .assign 3 0, .storageDead 4, .storageLive 6,
        .assign 0 0, .storageDead 6, .storageDead 3, .storageDead 1,
        .storageDead 1, .assign 0 0] } := by
  rfl

theorem loop_trace_in_steps :
    LeanModels.Rust.ProgramInSteps loop {
      state := { locals := [(0, .value 0), (1, .uninit)] },
      events := [
        .storageLive 1,
        .call "_RNvCs0ynxh6IOg33_4loop9countdown",
        .storageLive 1, .assign 1 2, .storageLive 3, .storageLive 4,
        .assign 4 2, .assign 3 1, .storageDead 4, .assign 1 0,
        .assign 2 0, .storageDead 3, .storageLive 3, .storageLive 4,
        .assign 4 0, .assign 3 0, .storageDead 4, .storageLive 6,
        .assign 0 0, .storageDead 6, .storageDead 3, .storageDead 1,
        .storageDead 1, .assign 0 0] } := by
  exact LeanModels.Rust.run_in_steps loop_trace

end Examples.rust.loop
