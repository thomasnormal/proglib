import Examples.rust.call.spec

namespace Examples.rust.call

theorem call_runs : (LeanModels.Rust.run call).isSome := by decide

theorem call_trace :
    LeanModels.Rust.run call = some {
      state := { locals := [(0, .value 0), (1, .uninit)] },
      events := [.storageLive 1,
        .call "_RNvCs05yil4iL4cj_4call6answer", .assign 0 7,
        .placeMention 1, .storageDead 1, .assign 0 0] } := by
  rfl

theorem call_trace_in_steps :
    LeanModels.Rust.ProgramInSteps call {
      state := { locals := [(0, .value 0), (1, .uninit)] },
      events := [.storageLive 1,
        .call "_RNvCs05yil4iL4cj_4call6answer", .assign 0 7,
        .placeMention 1, .storageDead 1, .assign 0 0] } := by
  exact LeanModels.Rust.run_in_steps call_trace

end Examples.rust.call
