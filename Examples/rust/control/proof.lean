import Examples.rust.control.spec

namespace Examples.rust.control

theorem control_runs : (LeanModels.Rust.run control).isSome := by decide

theorem control_trace_in_steps :
    LeanModels.Rust.ProgramInSteps control {
      state := { locals := [(1, .uninit), (0, .value 0), (2, .uninit)] },
      events := [
        .storageLive 1, .assign 1 1, .storageLive 2,
        .assign 2 10, .placeMention 2, .storageDead 2,
        .assign 0 0, .storageDead 1] } := by
  apply LeanModels.Rust.run_in_steps
  decide

end Examples.rust.control
