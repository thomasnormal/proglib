import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombTask
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Theorem A (the honest baseline), the deterministic half, for EVERY N in range

`noisy_mul_flat.sem N` with the fault input `f = 0` computes `p = a * b`, for every
`1 ≤ N < 2^28`, through the library's symbolic-parameter route (`sv_structure`,
`sv_equations`, `sv_bridge`, `CombLib.ideal_mul_view`). Nothing about probability here.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq

namespace NoisyMul

load_design_sv2 noisy_mul_flat from "Examples/system-verilog/sem2/noisy_mul_generate/noisy_mul_flat.sv.json"

/-- The number of gates (fault bits) of the array: `N^2` AND gates and `3 N (N-1)` full-adder gates. -/
def G (N : Nat) : Nat := (4 * N - 3) * N

/-- The rank of svgolf's `mul_n` reference, unchanged (same netlist, same site labels). -/
def mulKey (N : Nat) : SiteId → Key
  | .plain 0 => (0, 0, 1)
  | .plain 1 => (0, 0, 0)
  | .plain 2 => (0, 0, 0)
  | .plain _ => (N, 0, 1)
  | .fam "g_pp_j" _ _ => (0, 0, 0)
  | .fam "g_row" 0 [i] => (i.toNat, 0, 0)
  | .fam "g_row" _ [i] => (i.toNat, N, 0)
  | .fam "g_bit" 0 [i, j] => (i.toNat, j.toNat, 1)
  | .fam "g_bit" 1 [i, j] => (i.toNat, j.toNat, 3)
  | .fam "g_bit" _ [i, j] => (i.toNat, j.toNat, 2)
  | .fam _ _ _ => (N, 0, 0)

set_option maxHeartbeats 400000 in
/-- Structure: comb profile, rank certificate, shared obligations, for every `1 ≤ N < 2^28`. -/
theorem flat_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 28) :
    CombDesign (noisy_mul_flat.sem N) ∧ Acyclic (noisy_mul_flat.sem N) ∧
      SharedObl noisy_mul_flat.pdesign [N] := by
  sv_structure (lexRank := mulKey N)
  all_goals (intros; sv_rowmajor; omega)

/-- A read of the fault port stays inside its `(4N-3) · N` bits (the nonlinear width the tactics leave). -/
theorem frange_true (N : Nat) (r c : Int) (hr0 : 0 ≤ r) (hr : r ≤ 4 * (N : Int) - 4) (hc0 : 0 ≤ c)
    (hc : c < (N : Int)) :
    (rmN (N : Int) r c < ((4 * (N : Int) + -4).natAbs + 1) * (((N : Int) + -1).natAbs + 1)) = True := by
  have h1 : (4 * (N : Int) + -4).natAbs + 1 = r.toNat + ((4 * (N : Int) + -4).natAbs - r.toNat) + 1 := by omega
  have h2 : ((N : Int) + -1).natAbs + 1 = N := by omega
  rw [h1, h2]
  apply eq_true
  unfold rmN
  have hN : (N : Int).toNat = N := by omega
  rw [hN, Nat.add_assoc, Nat.add_mul, Nat.add_mul]
  have : c.toNat < N := by omega
  have : N ≤ ((4 * (N : Int) + -4).natAbs - r.toNat + 1) * N := Nat.le_mul_of_pos_left N (by omega)
  omega

/-- The fault-free input: every bit of `f` reads `0`. -/
theorem boolAt_zero {st : SvState} {n : String} {w : Nat}
    (h : SvState.lookup st n = some (LVec.ofBitVec (0#w))) (k : Nat) : st.boolAt n k = false := by
  by_cases hk : k < w
  · rw [SvState.boolAt_ofBitVec h hk]; simp
  · unfold SvState.boolAt; rw [h]
    have hsz : (LVec.ofBitVec (0#w)).bits.size = w := by
      have := LVec.width_ofBitVec (0#w); simpa [LVec.width] using this
    show ((LVec.ofBitVec (0#w)).bits[k]?.getD Logic.lx == Logic.l1) = false
    rw [Array.getElem?_eq_none (by omega)]
    rfl

/-- The carry gate is a majority gate; with the propagate `t = x ^^ y` it is the carry of `MulNetlistView`. -/
theorem maj_carry (x y z : Bool) : (x && y || x && z || y && z) = (x && y || z && (x ^^ y)) := by
  cases x <;> cases y <;> cases z <;> rfl

set_option maxHeartbeats 1000000 in
/-- **Fault-free correctness, every N**: in every settled state where `a`, `b` hold known `x`, `y` and the fault
port holds `0`, the output port holds `x * y` on `2N` bits. -/
theorem flat_faultfree (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 28) (st : SvState)
    (heqs : CombEqs (noisy_mul_flat.sem N) st) (hs : StateShape (noisy_mul_flat.sem N) st)
    (x y : BitVec N)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hF : SvState.lookup st "f" = some (LVec.ofBitVec (0#(G N)))) :
    SvState.lookup st "p" = some (LVec.ofBitVec (BitVec.ofNat (2 * N) (x.toNat * y.toNat))) := by
  obtain ⟨hc, ha, hso⟩ := flat_struct N hN hR
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_g_out_0 0 (by omega)
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    have hf0 : ∀ k, st.boolAt "f" k = false := boolAt_zero hF
    have hkp : ∀ k, k < 2 * N → KnownBit st "p" k := by
      intro k hk
      by_cases h : k < N
      · exact (known_p_g_out_0 k h).2
      · obtain ⟨j, rfl⟩ : ∃ j, k = N + j := ⟨k - N, by omega⟩
        exact (known_p_plain_3 j (by omega)).2
    rw [hvp, SvState.lookup_eq_ofBitVec_bv (W := 2 * N) hvp (by omega) hkp]
    congr 2
    have ht : ∀ i, 1 ≤ i → i < N → ∀ j, j < N →
        st.cell "t" N i j = (st.cell "s" ((N : Int) + 1) (i - 1) (j + 1) ^^ st.cell "pp" N i j) := by
      sv_bridge eq_t_g_bit_0 with hf0, Bool.xor_false
    have hm : ∀ i, 1 ≤ i → i < N → ∀ j, j < N →
        st.cell "c" ((N : Int) + 1) i (j + 1) =
          (st.cell "s" ((N : Int) + 1) (i - 1) (j + 1) && st.cell "pp" N i j ||
            st.cell "s" ((N : Int) + 1) (i - 1) (j + 1) && st.cell "c" ((N : Int) + 1) i j ||
            st.cell "pp" N i j && st.cell "c" ((N : Int) + 1) i j) := by
      sv_bridge eq_c_g_bit_2 with hf0, Bool.xor_false
    refine ideal_mul_view hN (pp := st.cell "pp" N) (t := st.cell "t" N)
      (s := st.cell "s" ((N : Int) + 1)) (c := st.cell "c" ((N : Int) + 1))
      { pp_def := ?_, s0 := ?_, s0_top := ?_, c0 := ?_, t0 := ?_, ci0 := ?_, t_def := ht, s_def := ?_,
        c_def := ?_, s_top := ?_, p_low := ?_, p_high := ?_ }
    · sv_bridge eq_pp_g_pp_j_0 with ba, bb, hf0, Bool.xor_false
    · sv_bridge eq_s_plain_0 with if_pos
    · sv_bridge (eq_s_plain_0 N (by omega)) with if_neg
    · sv_bridge eq_c_plain_1
    · sv_bridge eq_t_plain_2
    · sv_bridge eq_c_g_row_0
    · sv_bridge eq_s_g_bit_1 with hf0, Bool.xor_false
    · intro i h1 h2 j hj
      rw [hm i h1 h2 j hj, ht i h1 h2 j hj, maj_carry]
    · sv_bridge eq_s_g_row_2
    · sv_bridge eq_p_g_out_0 with XF.getLsbD_bv
    · sv_bridge eq_p_plain_3 with XF.getLsbD_bv
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  case inputsKnown_3 =>
    refine inKnown_ofBitVec hF ?_
    have h1 : (4 * (N : Int) + -4).natAbs + 1 = 4 * N - 3 := by omega
    have h2 : ((N : Int) + -1).natAbs + 1 = N := by omega
    rw [h1, h2]; rfl
  all_goals first
    | (intros; omega)
    | sv_cover
    | (simp (config := { contextual := true }) (disch := omega) only [frange_true N, and_true]; sv_cover)

/--
info: 'NoisyMul.flat_faultfree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms flat_faultfree

end NoisyMul
