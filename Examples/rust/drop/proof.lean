import Examples.rust.drop.spec

namespace Examples.rust.drop

theorem drop_refused :
    LeanModels.Rust.runOutcome drop =
      .refused (.unsupported "assignment") := by
  decide

end Examples.rust.drop
