import Examples.«system-verilog».gen_bit.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on the bit test of two genvars (`Examples/system-verilog/gen_bit`)

The condition `((i >> l) & 1) == 1` is the guard `i / 2 ^ l % 2 = 1`, which `omega` reads through the atom
`i / 2 ^ l` (its remainder modulo 2 is linear); the read `x[l][((i >> l) << l) - 1]` holds the atom
`i / 2 ^ l * 2 ^ l`, which `sv_pow_omega` relates to `i` and `2 ^ l` (`shl_shr_facts`: at most `i`, at least `2 ^ l`
where bit `l` of `i` is set), so the read is in range under its arm's guard. The two arms of `g_node` write the same
cell under complementary guards (the congruence of the two quotients at equal operands, `div_pow_congr_or`). The atoms'
ranges (`0 ≤ i < 2^31`, `0 ≤ l < 32`) are closed by the tactic.

Build: `lake build Examples.«system-verilog».gen_bit.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_bit.gen

namespace Examples.«system-verilog».gen_bit.comb_proof

/-- The structure of `gen_bit`, at every `N`: one driver per bit, every window in range. -/
theorem gen_bit_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (gen_bit.sem N) := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- The rank: the inputs' level 0 first, level `l + 1` after level `l` (both arms), the outputs last. -/
theorem gen_bit_acyclic (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : Acyclic (gen_bit.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_node" _ [l, _] => (l.toNat + 1, 0, 0)
    | .fam "g_out" _ [_] => (40, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/--
info: 'Examples.«system-verilog».gen_bit.comb_proof.gen_bit_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_bit_comb

/--
info: 'Examples.«system-verilog».gen_bit.comb_proof.gen_bit_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_bit_acyclic

end Examples.«system-verilog».gen_bit.comb_proof
