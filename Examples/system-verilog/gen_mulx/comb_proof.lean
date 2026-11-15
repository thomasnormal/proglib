import Examples.«system-verilog».gen_mulx.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on products of a genvar and a shift by an affine amount (`Examples/system-verilog/gen_mulx`)

The slot bases `t*(P >> (l+1))`, `(1-t)*(P >> (l+1))` and `(2*t)*(P >> (l+2))` are the product atoms `t · (P / 2^(l+1))`,
… (`XAt.mul`, `affMul`); `P >> (l + 1)`, `N >> (l + 1)` (in the generate condition) and `P >> (j - 1)` the affine-amount
atom `shrA`. The obligations (the atoms' ranges, the slots inside `y`, `z` and `a`, the two writers of each half
disjoint, the condition's operands 32-bit values) close by `omega` with the facts `sv_pow_omega` states: the products'
signs, their bounds from the literal bounds of `t` and their monotonicity in `t` (`addMulFacts`), and the bounds of a
quotient by a power from the bounds of its exponent (`addPowFacts`).

Build: `lake build Examples.«system-verilog».gen_mulx.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_mulx.gen

namespace Examples.«system-verilog».gen_mulx.comb_proof

set_option maxHeartbeats 1000000 in
/-- The structure of `gen_mulx`, at every `1 ≤ N < 2^30` (`P = 2N` a 32-bit `int`). -/
theorem gen_mulx_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) :
    CombDesign (gen_mulx.sem N) ∧ SharedObl gen_mulx.pdesign [N] := by
  sv_structure
  all_goals (intros; first | omega | sv_pow_omega)

/-- Every site reads inputs only: any rank. -/
theorem gen_mulx_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) (hc : CombDesign (gen_mulx.sem N))
    (hso : SharedObl gen_mulx.pdesign [N]) : Acyclic (gen_mulx.sem N) := by
  sv_structure (lexRank := fun _ => (0, 0, 0)) using hc
  all_goals (intros; first | omega | sv_pow_omega)

/--
info: 'Examples.«system-verilog».gen_mulx.comb_proof.gen_mulx_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_mulx_comb

end Examples.«system-verilog».gen_mulx.comb_proof
