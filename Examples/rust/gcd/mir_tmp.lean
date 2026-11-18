import Examples.rust.gcd.spec
namespace Examples.rust.gcd
open LeanModels.Rust
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def retGcd (a b : Nat) (fuel : Nat) : Prop :=
  ∃ t, cfgRunOutcome fuel gcdBody 0 (gcdInput a b) = .returned t ∧
    returnValue t = some (Int.ofNat (Nat.gcd a b))

example (a : Nat) : retGcd a 0 4 := by
  unfold retGcd
  simp [cfgRunOutcome, gcdBody, gcd, gcdInput, blockAt, statementsRun,
    statementStep, terminatorStep, operandValue, operandCell, readCell,
    localSlot, slotCell, rvalueCell, setSlot, typedBytesValue,
    returnValue]

end Examples.rust.gcd
