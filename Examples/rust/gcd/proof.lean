import Examples.rust.gcd.spec

namespace Examples.rust.gcd

open LeanModels.Rust

def gcdLoop : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => gcdLoop (b + 1) (a % (b + 1))
decreasing_by exact Nat.mod_lt _ (by omega)

theorem gcdLoop_spec (a b : Nat) : gcdLoop a b = Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
      cases b with
      | zero => simp [gcdLoop]
      | succ b =>
          rw [gcdLoop]
          have hlt : a % (b + 1) < b + 1 := Nat.mod_lt _ (by omega)
          rw [ih (a := b + 1) (a % (b + 1)) hlt]
          calc
            Nat.gcd (b + 1) (a % (b + 1)) = Nat.gcd (a % (b + 1)) (b + 1) := Nat.gcd_comm _ _
            _ = Nat.gcd (b + 1) a := by rw [← Nat.gcd_rec]
            _ = Nat.gcd a (b + 1) := Nat.gcd_comm _ _

end Examples.rust.gcd
