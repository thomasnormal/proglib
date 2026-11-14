import Examples.«system-verilog».gen_pow.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# `sv_equations` on shift and power atoms of the genvars (`Examples/system-verilog/gen_pow`)

In a settled state each site's equation holds at every instance; `sv_equations` states it with the atom `2 ^ l` where
the source has `1 << l`: the triangle's cell `t[l][i]` for every level `l < clog2 N` and every `i < 2 ^ l`
(`eq_t_g_tri_0`, the loop bound read at the level), and the prefix node `x[l+1][i]` under its arm's guard `2 ^ l ≤ i`,
reading `x[l][i - 2 ^ l]` (`eq_x_g_node_0`). The inputs are known (`hA`, `hB`); the cover obligations, a read of `x`
at a column shifted by the atom among them, are the sites' own (`sv_cover`).

Build: `lake build Examples.«system-verilog».gen_pow.eq_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».gen_pow.gen

namespace Examples.«system-verilog».gen_pow.eq_proof

/-- A cell of row `i < clog2 N` of `x` at a column `0 ≤ C < N` has a writer: `g_in` on row `0`, else one of the two arms
of `g_node` one row below (the cover obligation of the node's reads, `cover_2`, one read at `C = j` and one at the
column shifted by the atom, `C = j - 2 ^ i`; the witnesses are the read's own row and column). -/
private theorem x_cell_cover (N : Nat) (i C : Int) (h0 : 0 ≤ i) (h1 : i < ↑(clog2 N)) (hC0 : 0 ≤ C)
    (hC1 : C < ↑N) :
    (∃ i_2, i_2 < N ∧ rmN (↑N) 0 ↑i_2 ≤ rmN (↑N) i C ∧ rmN (↑N) i C < rmN (↑N) 0 ↑i_2 + 1) ∨
    (∃ i_2, i_2 < clog2 N ∧ ∃ i_3, i_3 < N ∧ (2 : Int) ^ i_2 ≤ ↑i_3 ∧
      rmN (↑N) (↑i_2 + 1) ↑i_3 ≤ rmN (↑N) i C ∧ rmN (↑N) i C < rmN (↑N) (↑i_2 + 1) ↑i_3 + 1) ∨
    (∃ i_2, i_2 < clog2 N ∧ ∃ i_3, i_3 < N ∧ (↑i_3 : Int) < 2 ^ i_2 ∧
      rmN (↑N) (↑i_2 + 1) ↑i_3 ≤ rmN (↑N) i C ∧ rmN (↑N) i C < rmN (↑N) (↑i_2 + 1) ↑i_3 + 1) := by
  by_cases hi0 : i = 0
  · left
    refine ⟨C.toNat, by omega, ?_⟩
    rw [Int.toNat_of_nonneg hC0, hi0]
    exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  · have e1 : (((i - 1).toNat : Nat) : Int) + 1 = i := by omega
    by_cases hgw : (2 : Int) ^ (i - 1).toNat ≤ ((C.toNat : Nat) : Int)
    · right; left
      refine ⟨(i - 1).toNat, by omega, C.toNat, by omega, hgw, ?_⟩
      rw [e1, Int.toNat_of_nonneg hC0]
      exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
    · right; right
      refine ⟨(i - 1).toNat, by omega, C.toNat, by omega, by omega, ?_⟩
      rw [e1, Int.toNat_of_nonneg hC0]
      exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩

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
  case cover_2 =>
    -- `sv_cover` does not take the reads of the node (a follow-up: its 2-D rule recurses without end on them)
    intro i h0 h1 j h2 h3 hg
    have hp : (0 : Int) < 2 ^ i.toNat := Int.pow_pos (by decide)
    exact ⟨x_cell_cover N i j h0 h1 h2 h3, x_cell_cover N i (j + -2 ^ i.toNat) h0 h1 (by omega) (by omega)⟩
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
