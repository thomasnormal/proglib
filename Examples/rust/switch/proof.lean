import Examples.rust.switch.spec

namespace Examples.rust.switch

theorem switch_runs : (LeanModels.Rust.run switch).isSome := by decide

theorem switch_trace_in_steps :
    LeanModels.Rust.ProgramInSteps switch {
      state := { locals := [(1, .uninit), (0, .value 0), (3, .uninit)] },
      events := [
        .storageLive 1, .assign 1 2, .placeMention 1,
        .storageLive 3, .assign 3 20, .placeMention 3,
        .storageDead 3, .assign 0 0, .storageDead 1] } := by
  apply LeanModels.Rust.run_in_steps
  decide

end Examples.rust.switch
