import Examples.rust.place_mention.spec

namespace Examples.rust.placeMention

theorem place_mention_runs : (LeanModels.Rust.run placeMention).isSome := by decide

theorem place_mention_trace :
    LeanModels.Rust.run placeMention = some {
      state := { locals := [(1, .uninit), (0, .value 0)] },
      events := [.storageLive 1, .assign 1 3, .placeMention 1,
        .assign 0 0, .storageDead 1] } := by
  rfl

theorem place_mention_trace_in_steps :
    LeanModels.Rust.ProgramInSteps placeMention {
      state := { locals := [(1, .uninit), (0, .value 0)] },
      events := [.storageLive 1, .assign 1 3, .placeMention 1,
        .assign 0 0, .storageDead 1] } := by
  exact LeanModels.Rust.run_in_steps place_mention_trace

end Examples.rust.placeMention
