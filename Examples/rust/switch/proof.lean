import Examples.rust.switch.spec

namespace Examples.rust.switch

theorem switch_runs : (LeanModels.Rust.run switch).isSome := by decide

end Examples.rust.switch
