import Examples.rust.storage.spec

namespace Examples.rust.storage

theorem storage_runs : (LeanModels.Rust.run storage).isSome := by decide

theorem storage_trace :
    LeanModels.Rust.run storage = some {
      state := { locals := [(1, .uninit), (0, .value 0)] },
      events := [.storageLive 1, .assign 1 7, .placeMention 1,
        .assign 0 0, .storageDead 1] } := by
  decide

theorem storage_trace_in_steps :
    LeanModels.Rust.ProgramInSteps storage {
      state := { locals := [(1, .uninit), (0, .value 0)] },
      events := [.storageLive 1, .assign 1 7, .placeMention 1,
        .assign 0 0, .storageDead 1] } := by
  exact LeanModels.Rust.run_in_steps storage_trace

end Examples.rust.storage
