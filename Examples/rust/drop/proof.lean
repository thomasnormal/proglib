import Examples.rust.drop.spec

namespace Examples.rust.drop

theorem drop_returns :
    LeanModels.Rust.Outcome.isReturned (LeanModels.Rust.runOutcome drop) = true := by
  decide

end Examples.rust.drop
