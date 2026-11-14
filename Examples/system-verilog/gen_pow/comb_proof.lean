import Examples.«system-verilog».gen_pow.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on shift and power atoms of the genvars (`Examples/system-verilog/gen_pow`)

`1 << l` is read as the atom `2 ^ l` (`XAt.pow 2 "l"`): the obligations hold `2 ^ l.toNat`, which `omega` reads as an
opaque atom, and `sv_pow_omega` adds what it needs about it (its bounds from those of `l`, the monotonicity of the
power, the `$clog2` facts of `L`). The atom's range (`0 ≤ l < 32`, `2 ^ l < 2^31`, `Summary.XObl`) is owed at every
level and closed by the tactic from `l < L = $clog2(N)` and `N < 2^31 - 1`. The node's read `x[l][i - (1 << l)]` is in
range under its arm's guard `2 ^ l ≤ i`; the two arms of `g_node` write the same cell under complementary guards (the
congruence of the two atoms `2 ^ l1`, `2 ^ l2` at equal levels, `pow_le_pow_or`); the triangle's row `l` stops at
`2 ^ l ≤ 2 ^ (L - 1) < N` (`two_pow_clog2_lt_int`).

Build: `lake build Examples.«system-verilog».gen_pow.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_pow.gen

namespace Examples.«system-verilog».gen_pow.comb_proof

/-- The structure of `gen_pow`, at every `N`: one driver per bit, every window in range. -/
theorem gen_pow_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (gen_pow.sem N) := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- The rank: the inputs' level 0 first, level `l + 1` after level `l` (both arms), the outputs last. -/
theorem gen_pow_acyclic (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : Acyclic (gen_pow.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_node" _ [l, _] => (l.toNat + 1, 0, 0)
    | .fam "g_out" _ [_] => (40, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/--
info: 'Examples.«system-verilog».gen_pow.comb_proof.gen_pow_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_pow_comb

/--
info: 'Examples.«system-verilog».gen_pow.comb_proof.gen_pow_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_pow_acyclic

end Examples.«system-verilog».gen_pow.comb_proof
