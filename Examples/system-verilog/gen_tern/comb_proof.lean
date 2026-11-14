import Examples.«system-verilog».gen_tern.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on a power of a genvar in a loop bound (`Examples/system-verilog/gen_tern`)

The node loop of level `l` runs over `t < 3 ^ l`; its reads `v[l+1][3*t + k]` are in range because `3 * 3 ^ l ≤ 3 ^ N`
at `l < N` (the strict monotonicity of the power, `pow_lt_pow_or`, which `sv_pow_omega` states for the two atoms
`3 ^ l` and `3 ^ N`, the latter `T`'s value); the atom's range (`3 ^ l < 2^31`) follows from `l < N`.

The premise `N ≤ 3` is the GENERATE FUEL, not the atom: `X.sem N` instantiates with `PDesign.surfaceFuel [N] =
(N + 2)² + 64` iterations per loop, and the comb tactics owe each loop's count below its linear sufficient bound
`4 N + 60` (`AutoObl`); the leaves' loop runs `3 ^ N` times, within that bound only up to `N = 3` (and within the fuel
itself only up to `N = 4`: at `N = 5` the instantiation runs out of fuel, `gen.lean`).

Build: `lake build Examples.«system-verilog».gen_tern.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_tern.gen

namespace Examples.«system-verilog».gen_tern.comb_proof

/-- The structure of `gen_tern`, at every `N ≤ 3`: one driver per bit, every window in range. -/
theorem gen_tern_comb (N : Nat) (hN : 1 ≤ N) (hR : N ≤ 3) : CombDesign (gen_tern.sem N) := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- The rank: the leaves first, then the levels from `N - 1` down to the root. -/
theorem gen_tern_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N ≤ 3) : Acyclic (gen_tern.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_node" _ [l, _] => (40 - l.toNat, 0, 0)
    | .plain _ => (41, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

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
error: sv_structure: outside the supported fragment — generate bound is not affine in the parameters and the enclosing genvars
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : N ≤ 3) : CombDesign (gen_tern_sum.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_tern.comb_proof
