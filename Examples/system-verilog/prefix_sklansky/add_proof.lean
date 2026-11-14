import Examples.«system-verilog».prefix_sklansky.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombTask
import LeanModels.Sv.CombTaskTactic
import LeanModels.Sv.Lib.Prefix

/-!
# The Sklansky adder meets the svGolf `add` statement, for every `N` in range, by the `sv_comb` tactics

`prefix_sklansky_add : AddStatement prefix_sklansky.sem` (`prefix_ks/statement.lean`: the svGolf `add` task's statement
over ls-sv), by the route of `prefix_ks/add_proof.lean`:

* `sv_structure`: `CombDesign` with the shared obligations (`SharedObl`), then `Acyclic` from them, of
  `prefix_sklansky.sem N` at every `N < 2^20`, each in a theorem of its own (the rank is the round);
* `sv_interface`: the ports;
* `CombTask.of_comb` and `sv_inputs`: the generic conjuncts, the stimulus form, the ports' bits;
* `sv_equations`: the settled-state equations over `Bool`, the bit test `((k >> r) & 1) == 1` read as
  `k / 2 ^ r % 2 = 1` and the read `G[r][((k >> r) << r) - 1]` at the column `k / 2 ^ r * 2 ^ r - 1` (`sv_eq_nat`,
  `Nat` indices); its obligations close by `sv_obligations`;
* the prefix mathematics: after round `r` column `k` holds the generate/propagate pair of the block
  `[k / 2^r * 2^r, k]`, from the start of its aligned block of `2^r` columns (`sklRec_block`, on
  `LeanModels.Sv.Lib.Prefix`), so the last round holds the carry into each bit, and `CombLib.add_spec` turns the
  ripple carries into the task's sum.

No `sorry`, `native_decide` or `bv_decide`; the axioms are pinned at the end.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq LeanModels.Sv.Lib
open Examples.«system-verilog».prefix_sklansky.gen Examples.«system-verilog».prefix_ks.statement

namespace Examples.«system-verilog».prefix_sklansky.add_proof

/-! ## 1. The prefix mathematics (plain `Bool`/`Nat`) -/

/-- The Sklansky recurrence as the design denotes it: round `0` is the columns `pos`; round `r + 1` at column `k` joins
`(r, k)` with `(r, k / 2^r * 2^r - 1)` where bit `r` of `k` is set, and copies `(r, k)` otherwise. -/
def sklRec (pos : Nat → Bool × Bool) : Nat → Nat → Bool × Bool
  | 0, k => pos k
  | r + 1, k =>
    if k / 2 ^ r % 2 = 1 then pgOp (sklRec pos r k) (sklRec pos r (k / 2 ^ r * 2 ^ r - 1)) else sklRec pos r k

/-- After round `r`, column `k` holds the pair of the block `[k / 2^r * 2^r, k]`. -/
theorem sklRec_block (pos : Nat → Bool × Bool) : ∀ r k, sklRec pos r k = pgBlock pos (k / 2 ^ r * 2 ^ r) k
  | 0, k => by rw [sklRec, Nat.pow_zero, Nat.div_one, Nat.mul_one, pgBlock_self]
  | r + 1, k => by
    have hk : k / 2 ^ r * 2 ^ r ≤ k := Nat.div_mul_le_self k _
    have hP : 0 < 2 ^ r := Nat.two_pow_pos r
    rw [sklRec]
    split
    · next hb =>
      rw [sklRec_block pos r k, sklRec_block pos r (k / 2 ^ r * 2 ^ r - 1), Nat.pow_succ,
        ← Nat.div_div_eq_div_mul]
      generalize k / 2 ^ r = Q at *
      generalize 2 ^ r = P at *
      obtain ⟨h, rfl⟩ : ∃ h, Q = 2 * h + 1 := ⟨Q / 2, by omega⟩
      have e1 : (2 * h + 1) * P = 2 * (h * P) + P := by rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
      have e2 : (2 * (h * P) + P - 1) / P = 2 * h :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_assoc]; omega) (by rw [Nat.add_mul, Nat.mul_assoc]; omega)
      have e3 : (2 * h + 1) / 2 * (P * 2) = 2 * (h * P) := by
        rw [show (2 * h + 1) / 2 = h by omega, Nat.mul_comm P 2, ← Nat.mul_assoc, Nat.mul_comm h 2,
          Nat.mul_assoc]
      rw [e1] at hk ⊢
      have hc := pgBlock_combine pos (j := 2 * (h * P)) (m := 2 * (h * P) + P - 1) (k := k) (by omega) (by omega)
      rw [show 2 * (h * P) + P - 1 + 1 = 2 * (h * P) + P by omega] at hc
      rw [e2, e3, Nat.mul_assoc]
      exact hc
    · next hb =>
      rw [sklRec_block pos r k, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      generalize k / 2 ^ r = Q at *
      generalize 2 ^ r = P at *
      obtain ⟨h, rfl⟩ : ∃ h, Q = 2 * h := ⟨Q / 2, by omega⟩
      rw [show 2 * h / 2 = h by omega, Nat.mul_comm P 2, ← Nat.mul_assoc, Nat.mul_comm h 2]

/-! ## 2. Structure and ports -/

/-- `CombDesign` for every `N` in range, and the shared obligations (`auto`, `inRange`) that the rank and the equations
read from the context instead of normalizing them again. -/
theorem skl_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (prefix_sklansky.sem N) ∧ SharedObl prefix_sklansky.pdesign [N] := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- `Acyclic` for every `N` in range: the rank of round `r + 1` is `r + 1`, the sum and the carry out come last. -/
theorem skl_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (prefix_sklansky.sem N))
    (hso : SharedObl prefix_sklansky.pdesign [N]) : Acyclic (prefix_sklansky.sem N) := by
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
theorem skl_ports (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (prefix_sklansky.sem N)) :
    (prefix_sklansky.sem N).inputPorts = [("a", N), ("b", N), ("cin", 1)] ∧
      (prefix_sklansky.sem N).outputPorts = [("s", N), ("cout", 1)] := by
  sv_interface

/-! ## 3. The statement -/

/-- **The Sklansky adder meets the svGolf `add` statement**, at every `N` with `1 ≤ N < 2^20`. -/
theorem prefix_sklansky_add : AddStatement prefix_sklansky.sem := by
  intro N ⟨hN, hR⟩
  obtain ⟨hc, hso⟩ := skl_comb N hN hR
  have ha := skl_acyclic N hN hR hc hso
  refine CombTask.of_comb hc ha (skl_ports N hN hR hc) fun inputs st heqs hsh hin => ?_
  intro x y c0 hA hB hC
  sv_inputs
  sv_equations
  · sv_eq_nat
    -- every round holds the Sklansky recurrence
    have hlev : ∀ l, l ≤ clog2 (N + 1) → ∀ k, k ≤ N →
        (st.boolAt "G" (l * (N + 1) + k), st.boolAt "P" (l * (N + 1) + k)) =
          sklRec (addPos x.getLsbD y.getLsbD c0) l k := by
      intro l
      induction l with
      | zero =>
        intro _ k hk
        rcases k with _ | i
        · simp [sklRec, eq_G_plain_0, eq_P_plain_1, bit_cin]
        · simp [sklRec, eq_G_g_col_0 i (by omega), eq_P_g_col_1 i (by omega), bit_a i (by omega), bit_b i (by omega)]
      | succ l ih =>
        intro hl k hk
        rw [sklRec]
        split
        · next hg =>
          rw [eq_G_g_node_0 l (by omega) k (by omega) hg, eq_P_g_node_1 l (by omega) k (by omega) hg,
            ← ih (by omega) k hk,
            ← ih (by omega) (k / 2 ^ l * 2 ^ l - 1)
              (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.div_mul_le_self _ _) hk))]
          rfl
        · next hg =>
          rw [eq_G_g_node_2 l (by omega) k (by omega) hg, eq_P_g_node_3 l (by omega) k (by omega) hg,
            ← ih (by omega) k hk]
    -- the last round holds the carry into every bit
    have hcarry : ∀ k, k ≤ N →
        st.boolAt "G" (clog2 (N + 1) * (N + 1) + k) = rippleCarry x.getLsbD y.getLsbD c0 k := by
      intro k hk
      have h := hlev _ (Nat.le_refl _) k hk
      rw [sklRec_block, Nat.div_eq_of_lt (by have := le_two_pow_clog2 (N + 1); omega), Nat.zero_mul,
        pgBlock_addPos_zero] at h
      exact (Prod.mk.inj h).1
    -- the sum and the carry out, as `CombLib.add_spec` reads them, then the ports from their bits
    have hv : AddView N x y c0 (rippleCarry x.getLsbD y.getLsbD c0) (XF.bv N (st.boolAt "s")).getLsbD
        (st.boolAt "cout" 0) := by
      refine ⟨rfl, fun i _ => rfl, fun i hi => ?_, ?_⟩
      · rw [XF.getLsbD_bv hi, eq_s_g_sum_0 i hi, eq_P_g_col_1 i hi, bit_a i hi, bit_b i hi, hcarry i (by omega)]
      · rw [eq_cout_plain_2, hcarry N (Nat.le_refl N)]
    obtain ⟨h1, h2⟩ := add_spec hv
    rw [SvState.port_ofBitVec known_s_g_sum_0 (by omega) (by omega), SvState.port_ofBool known_cout_plain_2 rfl, h1, h2]
    exact ⟨rfl, rfl⟩
  sv_obligations

/-! ## Axioms -/

/--
info: 'Examples.«system-verilog».prefix_sklansky.add_proof.prefix_sklansky_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prefix_sklansky_add

end Examples.«system-verilog».prefix_sklansky.add_proof
