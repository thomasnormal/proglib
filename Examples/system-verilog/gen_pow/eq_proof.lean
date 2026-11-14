import Examples.«system-verilog».gen_pow.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# `sv_equations` on shift and power atoms of the genvars (`Examples/system-verilog/gen_pow`)

In a settled state each site's equation holds at every instance; `sv_equations` states it with the atom `2 ^ l` where
the source has `1 << l`: the triangle's cell `t[l][i]` for every level `l < clog2 N` and every `i < 2 ^ l`
(`eq_t_g_tri_0`, the loop bound read at the level), and the prefix node `x[l+1][i]` under its arm's guard `2 ^ l ≤ i`,
reading `x[l][i - 2 ^ l]` (`eq_x_g_node_0`). The inputs are known (`hA`, `hB`); the cover obligations, a read of `x`
at a column shifted by the atom among them, are the sites' own (`sv_cover`, which puts the sign of the power,
`0 < 2 ^ l`, in context for the shifted read).

Build: `lake build Examples.«system-verilog».gen_pow.eq_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».gen_pow.gen

namespace Examples.«system-verilog».gen_pow.eq_proof

/-- The triangle of `gen_pow` in a settled state: row `l` holds the first `2 ^ l` bits of `b`. -/
theorem gen_pow_t (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647)
    (hc : CombDesign (gen_pow.sem N)) (ha : Acyclic (gen_pow.sem N))
    (st : SvState) (heqs : CombEqs (gen_pow.sem N) st) (hsh : StateShape (gen_pow.sem N) st)
    (x y : BitVec N)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    ∀ l, l < clog2 N → ∀ i, i < 2 ^ l → st.boolAt "t" (l * N + i) = st.boolAt "b" i := by
  sv_equations
  · intro l hl i hi
    have hi' : (i : Int) < 2 ^ l := by exact_mod_cast hi
    rw [← eq_t_g_tri_0 l hl i hi']
    simp [rmN]
  all_goals first
    | (intros; omega)
    | sv_cover
    | sv_pow_omega
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/--
info: 'Examples.«system-verilog».gen_pow.eq_proof.gen_pow_t' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_pow_t

end Examples.«system-verilog».gen_pow.eq_proof
