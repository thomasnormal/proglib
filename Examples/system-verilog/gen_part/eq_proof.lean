import Examples.«system-verilog».gen_part.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# `sv_equations` on indexed part selects (`Examples/system-verilog/gen_part`)

A site that writes `g[l][2*i +: 2]` gets one equation per bit of its window (`∀ k < 2`, the window's width
`(2i + 1) - 2i + 1` as `partRange` gives it), the bit `k` of the concatenation `{a[i], b[i]}` on the right; the reads
`g[1][2*i +: 2]` and `w[i*2 +: 2]` are bit `k` of their windows. `z[i] = a[i] ^ b[i]` follows from three of them. The
cover obligations (every bit a read observes has a writer) close by `sv_cover` as for range part selects.

Build: `lake build Examples.«system-verilog».gen_part.eq_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».gen_part.gen

namespace Examples.«system-verilog».gen_part.eq_proof

/-- `gen_part` in a settled state: `z[i] = a[i] ^ b[i]`, through the `+:` windows of `g` and `w`. -/
theorem gen_part_z (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30)
    (hc : CombDesign (gen_part.sem N)) (ha : Acyclic (gen_part.sem N))
    (st : SvState) (heqs : CombEqs (gen_part.sem N) st) (hsh : StateShape (gen_part.sem N) st)
    (x y : BitVec N)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    ∀ i, i < N → st.boolAt "z" i = (st.boolAt "a" i ^^ st.boolAt "b" i) := by
  sv_equations
  · intro i hi
    have g0 := eq_g_g_node_0 0 (by omega) i hi 1 (by omega)
    have g1 := eq_g_g_node_0 1 (by omega) i hi 0 (by omega)
    have w0 := eq_w_g_out_0 i hi 0 (by omega)
    have i1 : rmN (2 * (N : Int)) ((0 : Nat) : Int) (2 * (i : Int)) + 1 = (2 * (i : Int) + 1).toNat := by
      simp [rmN]; omega
    have i2 : rmN (2 * (N : Int)) ((1 : Nat) : Int) (2 * (i : Int)) + 0 = rmN (2 * (N : Int)) 1 (2 * (i : Int)) + 0 := by
      simp
    rw [i1] at g0
    rw [i2] at g1
    rw [Nat.add_zero] at w0
    rw [eq_z_g_out_2 i hi, g0, w0, g1]
    simp
  all_goals first
    | (intros; omega)
    | sv_cover
    | (intros; refine ⟨?_, ?_⟩ <;> first | sv_cover | (intro k hk; sv_cover))
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/--
info: 'Examples.«system-verilog».gen_part.eq_proof.gen_part_z' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_part_z

end Examples.«system-verilog».gen_part.eq_proof
