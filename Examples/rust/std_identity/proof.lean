import Examples.rust.std_identity.spec
namespace Examples.rust.stdIdentity
theorem identity_runs : (LeanModels.Rust.run stdIdentity).isSome := by decide

theorem identity_trace :
    LeanModels.Rust.run stdIdentity = some {
      state := { locals := [(0, .value 0), (1, .uninit)] },
      events := [
        .storageLive 1,
        .call "_RINvNtCs9xW7P2vDFDD_4core7convert8identitylECsgoMeLM4tH1m_12std_identity",
        .assign 0 7, .placeMention 1, .storageDead 1, .assign 0 0] } := by
  decide
theorem identity_in_steps {trace : LeanModels.Rust.Trace}
    (h : LeanModels.Rust.run stdIdentity = some trace) :
    LeanModels.Rust.ProgramInSteps stdIdentity trace := by
  exact LeanModels.Rust.run_in_steps h
end Examples.rust.stdIdentity
