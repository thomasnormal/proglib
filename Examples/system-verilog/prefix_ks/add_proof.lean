import Examples.«system-verilog».prefix_ks.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombTask
import LeanModels.Sv.Lib.Prefix

/-!
# The Kogge-Stone adder meets the svGolf `add` statement, for every `N` in range, by the `sv_comb` tactics

`prefix_ks_add : AddStatement prefix_ks.sem` (`statement.lean`: the svGolf `add` task's statement over ls-sv), from

* `sv_structure`: `CombDesign` with the shared obligations (`SharedObl`), then `Acyclic` from them, of
  `prefix_ks.sem N` at every `N < 2^20`, each in a theorem of its own (the rank is the round);
* `sv_interface`: the ports;
* `CombTask.lean`: the generic conjuncts (no clocked process, the design is its own lowering, termination) and the
  stimulus form of the function from the settled-state form;
* `sv_equations`: the settled-state equations of the netlist over `Bool`, derived from the real semantics, with the
  atom `2 ^ r` where the source has `1 << r`, and the knownness of every driven bit; its obligations close by the
  standard closers;
* the prefix mathematics: after round `r` column `k` holds the generate/propagate pair of the block
  `[k + 1 - 2^r, k]` of the adder's columns (`ksRec_block`, on `LeanModels.Sv.Lib.Prefix`), so the last round holds
  the carry into each bit, and `CombLib.add_spec` turns the ripple carries into the task's sum.

No `sorry`, `native_decide` or `bv_decide`; the axioms are pinned at the end.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq LeanModels.Sv.Lib
open Examples.«system-verilog».prefix_ks.gen Examples.«system-verilog».prefix_ks.statement

namespace Examples.«system-verilog».prefix_ks.add_proof

/-! ## 1. The prefix mathematics (plain `Bool`/`Nat`) -/

/-- The Kogge-Stone recurrence as the design denotes it: round `0` is the columns `pos`; round `r + 1` at column `k`
joins `(r, k)` with `(r, k - 2^r)` where `2^r ≤ k`, and copies `(r, k)` otherwise. -/
def ksRec (pos : Nat → Bool × Bool) : Nat → Nat → Bool × Bool
  | 0, k => pos k
  | r + 1, k => if 2 ^ r ≤ k then pgOp (ksRec pos r k) (ksRec pos r (k - 2 ^ r)) else ksRec pos r k

/-- After round `r`, column `k` holds the pair of the block `[k + 1 - 2^r, k]` (natural subtraction). -/
theorem ksRec_block (pos : Nat → Bool × Bool) : ∀ r k, ksRec pos r k = pgBlock pos (k + 1 - 2 ^ r) k
  | 0, k => by rw [ksRec, Nat.pow_zero, Nat.add_sub_cancel, pgBlock_self]
  | r + 1, k => by
    have hP : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [ksRec, hP]
    split
    · rw [ksRec_block pos r k, ksRec_block pos r (k - 2 ^ r)]
      generalize 2 ^ r = Q at *
      have hc := pgBlock_combine pos (j := k + 1 - 2 * Q) (m := k - Q) (k := k) (by omega) (by omega)
      rw [show k - Q + 1 = k + 1 - Q by omega] at hc
      rw [show k - Q + 1 - Q = k + 1 - 2 * Q by omega]
      exact hc
    · rw [ksRec_block pos r k]
      generalize 2 ^ r = Q at *
      rw [show k + 1 - Q = 0 by omega, show k + 1 - 2 * Q = 0 by omega]

/-! ## 2. Structure and ports -/

/-- `CombDesign` for every `N` in range, and the shared obligations (`auto`, `inRange`) that the rank and the equations
read from the context instead of normalizing them again. -/
theorem ks_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (prefix_ks.sem N) ∧ SharedObl prefix_ks.pdesign [N] := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- `Acyclic` for every `N` in range: the rank of round `r + 1` is `r + 1`, the sum and the carry out come last. -/
theorem ks_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (prefix_ks.sem N))
    (hso : SharedObl prefix_ks.pdesign [N]) : Acyclic (prefix_ks.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_node" _ [r, _] => (r.toNat + 1, 0, 0)
    | .fam "g_sum" _ _ => (40, 0, 0)
    | .plain 2 => (40, 0, 0)
    | _ => (0, 0, 0)) using hc
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- The ports: `a`, `b`, `cin` in, `s`, `cout` out, with the task's widths. -/
theorem ks_ports (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (prefix_ks.sem N)) :
    (prefix_ks.sem N).inputPorts = [("a", N), ("b", N), ("cin", 1)] ∧
      (prefix_ks.sem N).outputPorts = [("s", N), ("cout", 1)] := by
  sv_interface

/-! ## 3. The statement -/

/-- **The Kogge-Stone adder meets the svGolf `add` statement**, at every `N` with `1 ≤ N < 2^20`. -/
theorem prefix_ks_add : AddStatement prefix_ks.sem := by
  intro N ⟨hN, hR⟩
  obtain ⟨hc, hso⟩ := ks_comb N hN hR
  have ha := ks_acyclic N hN hR hc hso
  have hports := ks_ports N hN hR hc
  refine ⟨hports, ⟨hc.unclocked, ⟨_, hc.lowerComb_eq, ha⟩, Terminates2.of_acyclic hc ha⟩,
    Models2.of_comb_ports hc fun inputs st heqs hsh hin => ?_⟩
  intro x y ci hAi hBi hCi'
  rw [hports.1] at hin
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 :=
    ⟨ci.getLsbD 0, BitVec.eq_of_getLsbD_eq fun i hi => by obtain rfl : i = 0 := (by omega); simp⟩
  have hA := hin "a" (by simp) _ hAi
  have hB := hin "b" (by simp) _ hBi
  have hCi := hin "cin" (by simp) _ hCi'
  rw [BitVec.toNat_ofBool]
  sv_equations
  · -- the round count `R` is read as a 32-bit `int`; below `2^20` it is `clog2 (N + 1)` itself
    have hRv : canonInt 32 true ↑(clog2 (N + 1)) = ↑(clog2 (N + 1)) :=
      canonInt32_of_range ⟨by omega, by have := clog2_le (N + 1); omega⟩
    have hrm : ∀ i j : Int, rmN (↑N + 1) i j = i.toNat * (N + 1) + j.toNat := fun i j => by
      simp only [rmN]; congr 2
    have hl1 : ∀ l : Nat, ((l : Int) + 1).toNat = l + 1 := fun l => by omega
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    have bci : st.boolAt "cin" 0 = c0 := by rw [SvState.boolAt_ofBitVec hCi (by omega)]; simp
    -- every round holds the Kogge-Stone recurrence
    have hlev : ∀ l, l ≤ clog2 (N + 1) → ∀ k, k ≤ N →
        (st.boolAt "G" (l * (N + 1) + k), st.boolAt "P" (l * (N + 1) + k)) =
          ksRec (addPos x.getLsbD y.getLsbD c0) l k := by
      intro l
      induction l with
      | zero =>
        intro _ k hk
        rcases k with _ | i
        · simp [ksRec, eq_G_plain_0, eq_P_plain_1, bci]
        · simp [ksRec, eq_G_g_col_0 i (by omega), eq_P_g_col_1 i (by omega), ba i (by omega), bb i (by omega)]
      | succ l ih =>
        intro hl k hk
        have hl' : (l : Int) < canonInt 32 true ↑(clog2 (N + 1)) := by rw [hRv]; omega
        rw [ksRec]
        split
        · next hg =>
          have hg' : (2 : Int) ^ l ≤ ↑k := by exact_mod_cast hg
          have hi : ((k : Int) + -1 * 2 ^ l).toNat = k - 2 ^ l := by
            have : ((2 : Int) ^ l) = ((2 ^ l : Nat) : Int) := by norm_cast
            omega
          have e1 := eq_G_g_node_0 l hl' k (by omega) hg'
          have e2 := eq_P_g_node_1 l hl' k (by omega) hg'
          simp only [hrm, hi, hl1, Int.toNat_natCast] at e1 e2
          rw [← ih (by omega) k hk, ← ih (by omega) (k - 2 ^ l) (Nat.le_trans (Nat.sub_le _ _) hk), e1, e2]
          rfl
        · next hg =>
          have hg' : ¬ (2 : Int) ^ l ≤ ↑k := by exact_mod_cast hg
          have e1 := eq_G_g_node_2 l hl' k (by omega) hg'
          have e2 := eq_P_g_node_3 l hl' k (by omega) hg'
          simp only [hrm, hl1, Int.toNat_natCast] at e1 e2
          rw [← ih (by omega) k hk, e1, e2]
    -- the last round holds the carry into every bit
    have hcarry : ∀ k, k ≤ N →
        st.boolAt "G" (clog2 (N + 1) * (N + 1) + k) = rippleCarry x.getLsbD y.getLsbD c0 k := by
      intro k hk
      have h := hlev _ (Nat.le_refl _) k hk
      rw [ksRec_block, show k + 1 - 2 ^ clog2 (N + 1) = 0 by have := le_two_pow_clog2 (N + 1); omega,
        pgBlock_addPos_zero] at h
      exact (Prod.mk.inj h).1
    -- the ports, from their bits
    obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_g_sum_0 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_plain_2
    have hs := SvState.lookup_eq_ofBitVec_bv hvs (by omega : vs.width = N) fun k hk => (known_s_g_sum_0 k hk).2
    have hco := SvState.lookup_eq_ofBitVec_bv hvc hvcw fun k hk => by obtain rfl : k = 0 := (by omega); exact hkc
    rw [hs] at hvs
    rw [hco] at hvc
    have hv : AddView N x y c0 (rippleCarry x.getLsbD y.getLsbD c0) (XF.bv N (st.boolAt "s")).getLsbD
        (st.boolAt "cout" 0) := by
      refine ⟨rfl, fun i _ => rfl, fun i hi => ?_, ?_⟩
      · rw [XF.getLsbD_bv hi, eq_s_g_sum_0 i hi, eq_P_g_col_1 i hi, ba i hi, bb i hi]
        simp only [hRv, hrm, Int.toNat_natCast]
        rw [hcarry i (by omega)]
      · rw [eq_cout_plain_2]
        simp only [hRv, hrm, Int.toNat_natCast]
        rw [hcarry N (Nat.le_refl N)]
    obtain ⟨h1, h2⟩ := add_spec hv
    have hxb : XF.bv 1 (st.boolAt "cout") = BitVec.ofBool (st.boolAt "cout" 0) :=
      BitVec.eq_of_getLsbD_eq fun i hi => by obtain rfl : i = 0 := (by omega); rw [XF.getLsbD_bv hi]; simp
    rw [hvs, h1, hvc, hxb, h2]
    exact ⟨rfl, rfl⟩
  all_goals first
    | (intros; omega)
    | sv_pow_omega
    | sv_cover
    | (sv_pow_facts <;> sv_cover)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-! ## Axioms -/

/--
info: 'Examples.«system-verilog».prefix_ks.add_proof.prefix_ks_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prefix_ks_add

end Examples.«system-verilog».prefix_ks.add_proof
