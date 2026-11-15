import Examples.«system-verilog».gen_fuelsq.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` with a loop count above the linear part of the generate fuel (`Examples/system-verilog/gen_fuelsq`)

The fuel obligation of `g_w` (`P - 0 ≤ fuelSq N + 4N + 67`, `P = 4 · 2^$clog2(N + 1)`) closes by `sv_pow_omega`: the
`$clog2` facts bound `2^L < 2(N + 1)`, and the tangent `2·2·N ≤ fuelSq N + 4` (`fuelSq_tangent`) covers the rest.

Build: `lake build Examples.«system-verilog».gen_fuelsq.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_fuelsq.gen

namespace Examples.«system-verilog».gen_fuelsq.comb_proof

/-- The structure of `gen_fuelsq`, at every `1 ≤ N < 2^28` (`P ≤ 2^31`: the localparams stay 32-bit `int`s). -/
theorem gen_fuelsq_comb (N : Nat) (hN : 1 ≤ N) (h28 : N < 2 ^ 28) : CombDesign (gen_fuelsq.sem N) := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/--
info: 'Examples.«system-verilog».gen_fuelsq.comb_proof.gen_fuelsq_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_fuelsq_comb

end Examples.«system-verilog».gen_fuelsq.comb_proof
