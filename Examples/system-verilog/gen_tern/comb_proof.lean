import Examples.«system-verilog».gen_tern.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on a power of a genvar in a loop bound (`Examples/system-verilog/gen_tern`)

The node loop of level `l` runs over `t < 3 ^ l`; its reads `v[l+1][3*t + k]` are in range because `3 * 3 ^ l ≤ 3 ^ N`
at `l < N` (the strict monotonicity of the power, `pow_lt_pow_or`, which `sv_pow_omega` states for the two atoms
`3 ^ l` and `3 ^ N`, the latter `T`'s value); the atom's range (`3 ^ l < 2^31`) follows from `l < N`.

The premise `N ≤ 4` is the GENERATE FUEL, not the atom: `X.sem N` instantiates with `PDesign.surfaceFuel [N] =
(N + 2)² + 64` iterations per loop, and the leaves' loop runs `3 ^ N` times, within the fuel only up to `N = 4` (at
`N = 5` the instantiation itself runs out of fuel, `gen.lean`). The comb tactics owe exactly that fuel (`AutoObl`: a
count at most `fuelSq N + 4 N + 67`; the linear `4 N + 60` they owed before held the leaves only up
to `N = 3`). Here the parameter is the exponent, so the leaves' count against the square is a statement about four
values of `N`, decided case by case (`gen_tern_fuel`). Where the exponent stays below a `$clog2` of the parameter (a tree
of `$clog2` depth, `kara_lv`'s shape) `sv_pow_facts` relates the power to the square itself (`ktree_count`).

Build: `lake build Examples.«system-verilog».gen_tern.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_tern.gen

namespace Examples.«system-verilog».gen_tern.comb_proof

/-- The leaves' count within the generate fuel, at the four values of `N` the instantiation admits. -/
private theorem gen_tern_fuel (N : Nat) (hN : 1 ≤ N) (hR : N ≤ 4) : (3 : Int) ^ N ≤ ↑(fuelSq N) + 4 * ↑N + 67 := by
  obtain rfl | rfl | rfl | rfl : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 := by omega
  all_goals decide

/-- The structure of `gen_tern`, at every `N ≤ 4`: one driver per bit, every window in range. -/
theorem gen_tern_comb (N : Nat) (hN : 1 ≤ N) (hR : N ≤ 4) : CombDesign (gen_tern.sem N) := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega))
    | exact gen_tern_fuel N hN hR)

/-- The rank: the leaves first, then the levels from `N - 1` down to the root. -/
theorem gen_tern_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N ≤ 4) : Acyclic (gen_tern.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_node" _ [l, _] => (40 - l.toNat, 0, 0)
    | .plain _ => (41, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega))
    | exact gen_tern_fuel N hN hR)

/-- A level of `3 ^ l` nodes below a `$clog2` depth (`l < clog2 ((N + 3) / 4)`, `kara_lv`'s levels) is within the exact
generate fuel at every `N`: `sv_pow_facts` relates the power to the square (`pow_le_sq_of_two_pow_le`, from
`2 ^ l ≤ N`, the bounds of the `$clog2` and the monotonicity of the powers of two). -/
theorem ktree_count (N l : Nat) (hN : 1 ≤ N) (hl : l < clog2 ((N + 3) / 4)) :
    (3 : Int) ^ l ≤ ↑(fuelSq N) + 4 * ↑N + 67 := by
  sv_pow_omega

/--
info: 'Examples.«system-verilog».gen_tern.comb_proof.gen_tern_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_tern_comb

/--
info: 'Examples.«system-verilog».gen_tern.comb_proof.gen_tern_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_tern_acyclic

/--
info: 'Examples.«system-verilog».gen_tern.comb_proof.ktree_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ktree_count

/--
error: sv_structure: outside the supported fragment — generate bound is not affine in the parameters and the enclosing genvars
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : N ≤ 3) : CombDesign (gen_tern_sum.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_tern.comb_proof
