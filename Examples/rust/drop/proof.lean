import Examples.rust.drop.spec

namespace Examples.rust.drop

theorem drop_refused :
    LeanModels.Rust.runOutcome drop =
      .refused (.unsupported "zst aggregate assignment") := by
  decide

end Examples.rust.drop
