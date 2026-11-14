import Examples.«system-verilog».gen_bit.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# `sv_equations` on the bit test of two genvars (`Examples/system-verilog/gen_bit`)

In a settled state each site's equation holds at every instance. `sv_equations` states the node of level `l` under its
arm's guard, the bit test `((i >> l) & 1) == 1` read as `i / 2 ^ l % 2 = 1` (`eq_x_g_node_0`), with the read
`x[l][((i >> l) << l) - 1]` at the column `-1 + i / 2 ^ l * 2 ^ l` (the atom `XAt.shl`). The input is known (`hA`). The
cover obligations are the sites' own: `sv_cover`, after `sv_pow_facts` where a read needs a fact of the atoms. The node's
two reads (`cover_2`) are closed by naming their writers (`x_cell_cover`): on the read at the shifted column, `sv_cover`'s
last `omega` call exhausts the recursion limit even with the facts in context; the rule then splits it per writer (tac5),
and `omega` still does not show the first condition of the last writer, the column's bound
`(-1 + i / 2 ^ l * 2 ^ l).toNat < N`, in that context (a follow-up); that range, `(i >> l) << l` at least `2 ^ l` where
bit `l` of `i` is set and at most `i`, is `sv_pow_omega`'s.

Build: `lake build Examples.«system-verilog».gen_bit.eq_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».gen_bit.gen

namespace Examples.«system-verilog».gen_bit.eq_proof

/-- A cell of row `i < clog2 N` of `x` at a column `0 ≤ C < N` has a writer: `g_in` on row `0`, else one of the two arms
of `g_node` one row below, by the bit test at that level (the witnesses are the read's own row and column). -/
private theorem x_cell_cover (N : Nat) (i C : Int) (h0 : 0 ≤ i) (h1 : i < ↑(clog2 N)) (hC0 : 0 ≤ C)
    (hC1 : C < ↑N) :
    (∃ i_2, i_2 < N ∧ rmN (↑N) 0 ↑i_2 ≤ rmN (↑N) i C ∧ rmN (↑N) i C < rmN (↑N) 0 ↑i_2 + 1) ∨
    (∃ i_2, i_2 < clog2 N ∧ ∃ i_3, i_3 < N ∧ (↑i_3 : Int) / 2 ^ i_2 % 2 = 1 ∧
      rmN (↑N) (↑i_2 + 1) ↑i_3 ≤ rmN (↑N) i C ∧ rmN (↑N) i C < rmN (↑N) (↑i_2 + 1) ↑i_3 + 1) ∨
    (∃ i_2, i_2 < clog2 N ∧ ∃ i_3, i_3 < N ∧ ¬ (↑i_3 : Int) / 2 ^ i_2 % 2 = 1 ∧
      rmN (↑N) (↑i_2 + 1) ↑i_3 ≤ rmN (↑N) i C ∧ rmN (↑N) i C < rmN (↑N) (↑i_2 + 1) ↑i_3 + 1) := by
  by_cases hi0 : i = 0
  · left
    refine ⟨C.toNat, by omega, ?_⟩
    rw [Int.toNat_of_nonneg hC0, hi0]
    exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  · have e1 : (((i - 1).toNat : Nat) : Int) + 1 = i := by omega
    by_cases hb : ((C.toNat : Nat) : Int) / 2 ^ (i - 1).toNat % 2 = 1
    · right; left
      refine ⟨(i - 1).toNat, by omega, C.toNat, by omega, hb, ?_⟩
      rw [e1, Int.toNat_of_nonneg hC0]
      exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
    · right; right
      refine ⟨(i - 1).toNat, by omega, C.toNat, by omega, hb, ?_⟩
      rw [e1, Int.toNat_of_nonneg hC0]
      exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩

/-- The node of `gen_bit` in a settled state: where bit `l` of `i` is set, cell `i` of level `l + 1` is the OR of cell
`i` of level `l` and the top cell of the block below it, `i / 2 ^ l * 2 ^ l - 1`. -/
theorem gen_bit_node (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647)
    (hc : CombDesign (gen_bit.sem N)) (ha : Acyclic (gen_bit.sem N))
    (st : SvState) (heqs : CombEqs (gen_bit.sem N) st) (hsh : StateShape (gen_bit.sem N) st)
    (x : BitVec N) (hA : SvState.lookup st "a" = some (LVec.ofBitVec x)) :
    ∀ l, l < clog2 N → ∀ i, i < N → i / 2 ^ l % 2 = 1 →
      st.boolAt "x" ((l + 1) * N + i) =
        (st.boolAt "x" (l * N + i) || st.boolAt "x" (l * N + (i / 2 ^ l * 2 ^ l - 1))) := by
  sv_equations
  · intro l hl i hi hb
    have hb' : (i : Int) / 2 ^ l % 2 = 1 := by exact_mod_cast hb
    have h := eq_x_g_node_0 l hl i hi hb'
    have hq : (i : Int) / 2 ^ l * 2 ^ l = ((i / 2 ^ l * 2 ^ l : Nat) : Int) := by
      rw [Int.natCast_mul, Int.natCast_ediv, Int.natCast_pow]; rfl
    have e1 : ((l : Int) + 1).toNat = l + 1 := by omega
    have e3 : ∀ m : Nat, (-1 + (m : Int)).toNat = m - 1 := fun m => by omega
    rw [hq] at h
    simp only [rmN, e1, e3, Int.toNat_natCast] at h
    exact h
  case cover_2 =>
    intro i h0 h1 j h2 h3 hg
    have hlo : 0 ≤ -1 + j / 2 ^ i.toNat * 2 ^ i.toNat := by sv_pow_omega
    have hhi : -1 + j / 2 ^ i.toNat * 2 ^ i.toNat < ↑N := by sv_pow_omega
    exact ⟨x_cell_cover N i j h0 h1 h2 h3, x_cell_cover N i _ h0 h1 hlo hhi⟩
  all_goals first
    | (intros; omega)
    | sv_cover
    | (sv_pow_facts <;> sv_cover)
    | sv_pow_omega
    | (refine inKnown_ofBitVec hA ?_; omega)

/--
info: 'Examples.«system-verilog».gen_bit.eq_proof.gen_bit_node' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_bit_node

end Examples.«system-verilog».gen_bit.eq_proof
