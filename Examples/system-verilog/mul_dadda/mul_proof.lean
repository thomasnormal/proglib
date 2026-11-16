import Examples.«system-verilog».mul_dadda.acyclic
import Examples.«system-verilog».mul_dadda.cover
import Examples.«system-verilog».mul_dadda.statement
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombTask
import LeanModels.Sv.CombTaskTactic

/-!
# The Dadda record meets the multiplier statement, for every `N` in range

`mul_dadda_mul : MulStatement mul_dadda.sem` (`statement.lean`: the svGolf `mul` task's statement over ls-sv,
`1 ≤ N < 2^30`): for every `N` in range, the ports, no clocked process, no combinational loop, termination, and in every
cycle whose stimulus drives `a`, `b` with known values, `p` holds the product `a * b` on `2N` bits. From

* `CombDesign` with the shared obligations and `Acyclic` (`comb_proof.lean`, `acyclic.lean`);
* `sv_interface`: the ports;
* `CombTask.of_comb` and `sv_inputs`: the generic conjuncts, the stimulus form, the input ports' bits;
* `sv_equations` with the localparams as variables of the netlist view (`sv_comb.lp_atoms_view`: the stage count `S`, a
  sum of 51 `?:`, and `NP` are atoms of the equations, their definitions hypotheses); its 13 obligations close by
  `dadda_obligation` (`cover.lean`);
* the equations as the netlist's view `arith.DView` (one field per family of assigns: each assign's equation
  instantiated at the stage's numbers `t = tS N s`, `u = uS N s` and the column's counts `f`, `h`, `c`, its premises by
  the closed forms of the record's `?:` counts, `tE`, `uE`, `fE`, `hE`, `cE`, `HnE`, `H0E`, `loE`, its indices by
  `omega`), and the mathematics (`arith.lean`, `DView.out`: the column ledger, the final rows, the ripple adder), so
  `p`'s value is `a * b`; `SvState.port_ofBitVec` assembles the port.

No `sorry`, `native_decide` or `bv_decide`; one `decide +kernel` (the table's 51 entries, `dT_dd`); the axioms are
pinned at the end.

Build: `lake build Examples.«system-verilog».mul_dadda.mul_proof`.
-/

open Lean Elab Tactic Meta
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».mul_dadda.gen Examples.«system-verilog».mul_dadda.comb_proof
open Examples.«system-verilog».mul_dadda.acyclic Examples.«system-verilog».mul_dadda.cover
open Examples.«system-verilog».mul_dadda.arith Examples.«system-verilog».mul_dadda.statement

namespace Examples.«system-verilog».mul_dadda.mul_proof

/-! ## 1. The record's `?:` counts as the equations print them are the closed forms -/

/-- The table at an index inside it is the heights `dd` (`decide +kernel`: kernel reduction over the 51 entries, no
axiom; as the table's facts in `comb_proof.lean`, whose Meta-level `decide` grew past 6 GB). -/
theorem dT_dd : ∀ n : Fin 51, dT (n : Nat) = ((dd (n : Nat) : Nat) : Int) := by decide +kernel

theorem dT_dd' (j : Int) (h0 : 0 ≤ j) (h1 : j ≤ 50) : dT j = ((dd j.toNat : Nat) : Int) := by
  have h := dT_dd ⟨j.toNat, by omega⟩
  have e : ((j.toNat : Nat) : Int) = j := by omega
  simpa only [e] using h

/-- The stage count is the number of heights below `N` (`nst`). -/
theorem S_nst (N : Nat) (S : Int)
    (hdS : 0 ≤ S ∧ S ≤ 51 ∧ ((S = 0 ∧ (N : Int) ≤ 2) ∨
      (1 ≤ S ∧ dT (S - 1) < (N : Int) ∧ (N : Int) ≤ dT (S - 1) + dT (S - 1) / 2))) :
    S = ((nst N : Nat) : Int) := by
  obtain ⟨h0, h51, hc⟩ := hdS
  have hle := nst_le N
  rcases hc with ⟨hS, hN2⟩ | ⟨h1, hlo, hhi⟩
  · rw [hS, nst_eq_zero (by omega)]; rfl
  · rw [dT_dd' (S - 1) (by omega) (by omega)] at hlo hhi
    have hlt := (nst_iff (N := N) (r := (S - 1).toNat) (by omega)).mp (by omega)
    by_cases h51' : S = 51
    · omega
    · have hs := dd_succ_all (S - 1).toNat (by omega)
      rw [show (S - 1).toNat + 1 = S.toNat by omega] at hs
      have h2 : ¬ S.toNat < nst N := fun h => by
        have := (nst_iff (N := N) (r := S.toNat) (by omega)).mpr h
        omega
      omega

/-- `NP` is `NPn N`. -/
theorem NP_npn (N : Nat) (NP : Int) (h : ((N : Int) < 2 ∧ NP = 2) ∨ (2 ≤ (N : Int) ∧ NP = (N : Int))) :
    NP = ((NPn N : Nat) : Int) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> unfold NPn <;> split <;> omega

theorem tE {N : Nat} {S : Int} (hS : S = ((nst N : Nat) : Int)) {s : Nat} (hs : s < nst N) :
    dT (S + -1 + -1 * (s : Int)) = ((tS N s : Nat) : Int) := by
  have hle := nst_le N
  rw [dT_dd' _ (by omega) (by omega)]
  unfold tS
  congr 2
  omega

theorem uE (N s : Nat) :
    (if (s : Int) = 0 then (N : Int) else ((tS N s : Nat) : Int) + ((tS N s : Nat) : Int) / 2 ^ 1) =
      ((uS N s : Nat) : Int) := by
  unfold uS
  by_cases h : s = 0 <;> simp [h] <;> omega

theorem fE {N s t u k : Nat} (hst : Stg N s t u) (hk : k < 2 * N) :
    ((if (t : Int) < (if (if k ≤ N then (k : Int) else 2 * (N : Int) + -1 * (k : Int)) < (u : Int) then
          (if k ≤ N then (k : Int) else 2 * (N : Int) + -1 * (k : Int)) else (u : Int)) then
        (if (if k ≤ N then (k : Int) else 2 * (N : Int) + -1 * (k : Int)) < (u : Int) then
          (if k ≤ N then (k : Int) else 2 * (N : Int) + -1 * (k : Int)) else (u : Int)) + -1 * (t : Int)
      else 0) +
      -1 * (if (s : Int) = 0 then (if (k : Int) = (N : Int) then 1 else 0) else 0)) =
      ((fF N s t u k : Nat) : Int) := by
  unfold fF mF ind; csolve

theorem hE {N s t u k : Nat} (hst : Stg N s t u) (hk : k < 2 * N) :
    (if t ≤ k then (if k < u then (1 : Int) else if (s : Int) = 0 then (if (k : Int) = (N : Int) then 1 else 0) else 0)
      else if (s : Int) = 0 then (if (k : Int) = (N : Int) then 1 else 0) else 0) = ((hF N s t u k : Nat) : Int) := by
  unfold hF ind; csolve

theorem cE {N s t u k : Nat} (hst : Stg N s t u) (hk : k < 2 * N) :
    (if (t : Int) < (if (if k ≤ N then (k : Int) else 2 * (N : Int) + 1 + -1 * (k : Int)) < (u : Int) then
          (if k ≤ N then (k : Int) else 2 * (N : Int) + 1 + -1 * (k : Int)) else (u : Int)) then
        (if (if k ≤ N then (k : Int) else 2 * (N : Int) + 1 + -1 * (k : Int)) < (u : Int) then
          (if k ≤ N then (k : Int) else 2 * (N : Int) + 1 + -1 * (k : Int)) else (u : Int)) + -1 * (t : Int)
      else 0) = ((cF N t u k : Nat) : Int) := by
  unfold cF mF'; csolve

theorem HnE {N s t u k : Nat} (hst : Stg N s t u) (hk : k < 2 * N) :
    (if (k : Int) ≤ 2 * (N : Int) + -1 * (t : Int) then (if k < t then (k : Int) + 1 else (t : Int))
      else 2 * (N : Int) + -1 + -1 * (k : Int)) = ((HnF N t k : Nat) : Int) := by
  unfold HnF; csolve

theorem H0E (N k : Nat) (hk : k < 2 * N) :
    (if k < N then (k : Int) + 1 else 2 * (N : Int) + -1 + -1 * (k : Int)) = ((H0F N k : Nat) : Int) := by
  unfold H0F; split <;> omega

theorem loE (N k : Nat) (hN : 1 ≤ N) :
    (if N ≤ k then (k : Int) + -1 * (N : Int) + 1 else 0) = ((loF N k : Nat) : Int) := by
  unfold loF; split <;> omega

/-! ## 2. The cells -/

/-- Bit `i` of column `k` before stage `s` (`T[s][k][i]`). -/
def Tc (st : SvState) (N : Nat) (NP : Int) (s k i : Nat) : Bool :=
  st.boolAt "T" (rmN NP ((rmN (2 * (N : Int)) (s : Int) (k : Int) : Nat) : Int) (i : Int))
/-- The sum of adder `q` of column `k` in stage `s`. -/
def SMc (st : SvState) (N : Nat) (NP : Int) (s k q : Nat) : Bool :=
  st.boolAt "SM" (rmN NP ((rmN (2 * (N : Int)) (s : Int) (k : Int) : Nat) : Int) (q : Int))
/-- The carry of adder `q` of column `k` in stage `s`. -/
def CYc (st : SvState) (N : Nat) (NP : Int) (s k q : Nat) : Bool :=
  st.boolAt "CY" (rmN NP ((rmN (2 * (N : Int)) (s : Int) (k : Int) : Nat) : Int) (q : Int))

theorem boolAt_idx {st : SvState} {n : String} {a b : Nat} (h : a = b) : st.boolAt n a = st.boolAt n b := h ▸ rfl

/-- Two reads of one array whose stage, column and bit `omega` shows equal. -/
theorem rmN3_congr {st : SvState} {n : String} {W1 W2 a b c a' b' c' : Int} (ha : a = a') (hb : b = b')
    (hc : c = c') : st.boolAt n (rmN W1 ((rmN W2 a b : Nat) : Int) c) = st.boolAt n (rmN W1 ((rmN W2 a' b' : Nat) : Int) c') := by
  rw [ha, hb, hc]

/-- A slice's cell `c + k` is the cell at column `c + k`. -/
theorem rmN_slice {st : SvState} {n : String} {W1 R c : Int} {k : Nat} (hc : 0 ≤ c) :
    st.boolAt n (rmN W1 R c + k) = st.boolAt n (rmN W1 R (c + (k : Int))) := by
  rw [rmN_add_col k hc]

/-- Row 0 of a two-dimensional offset. -/
theorem rmN_zero_row (W : Int) (k : Nat) : ((rmN W ((0 : Nat) : Int) (k : Int) : Nat) : Int) = (k : Int) := by
  simp [rmN]

/-! ## 3. The statement -/

set_option maxHeartbeats 4000000 in
/-- The ports: `a`, `b` in, `p` out, with the task's widths. -/
theorem dadda_ports (N : Nat) (hN : 1 ≤ N) (h30 : N < 2 ^ 30) (hc : CombDesign (mul_dadda.sem N)) :
    (mul_dadda.sem N).inputPorts = [("a", N), ("b", N)] ∧ (mul_dadda.sem N).outputPorts = [("p", 2 * N)] := by
  sv_interface

set_option hygiene false in
/-- One equation of a stage's assigns at stage `s`, column `k`: the one-iteration genvars at the stage's numbers and the
column's counts, every premise by the closed forms in context (`hTe` … `hCe`) and `omega`; the instance is `h`, its
remaining binders the assign's own (the adder or the bit, and its arm). -/
macro "stage_eq " e:term " as " h:ident : tactic => `(tactic| (
  have $h := $e s (by omega) (tS N s) (by rw [hTe]; omega) (by rw [hTe]; omega) (uS N s) (by rw [hUe]; omega)
    (by rw [hUe]; omega) k (by omega) (fF N s (tS N s) (uS N s) k) (by rw [hFe]; omega) (by rw [hFe]; omega)
    (hF N s (tS N s) (uS N s) k) (by rw [hHe]; omega) (by rw [hHe]; omega)
    (cF N (tS N s) (uS N s) k) (by rw [hCe]; omega) (by rw [hCe]; omega)))

set_option hygiene false in
/-- The closed forms of stage `s`, column `k` in context (`stage_eq` reads them). -/
macro "stage_forms" : tactic => `(tactic| (
  have hst := stg_of h30 hs
  have := hst.t2; have := hst.tu; have := hst.uN; have := hst.u3
  have hTe := tE hSn hs
  have hUe := uE N s
  have hFe := fE hst hk
  have hHe := hE hst hk
  have hCe := cE hst hk
  have hHne := HnE hst hk
  have hNP2 := NPn_two N
  have hNPN := NPn_ge N
  have hr3 := id_reads hst hk
  have hbl := id_Hb_le hst (k := k)
  have hsl := id_slots hst hk
  have hc0 := id_carry0 hst
  have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)))

set_option sv_comb.lp_atoms true in
set_option sv_comb.lp_atoms_view true in
set_option maxHeartbeats 100000000 in
/-- **The Dadda record meets the multiplier statement**, at every `N` with `1 ≤ N < 2^30`. -/
theorem mul_dadda_mul : MulStatement mul_dadda.sem := by
  intro N ⟨hN, h30⟩
  obtain ⟨hc, hso⟩ := mul_dadda_comb_shared N hN h30
  have ha := mul_dadda_acyclic N hN h30 hc hso
  refine CombTask.of_comb hc ha (dadda_ports N hN h30 hc) fun inputs st heqs hsh hin => ?_
  intro x y hA hB
  sv_inputs
  quiet sv_equations
  · dadda_abs
    dadda_stage
    have hSn := S_nst N S hdS
    have hNPn := NP_npn N NP hNPc
    -- the netlist's view
    have hv : DView N x.getLsbD y.getLsbD (Tc st N NP) (SMc st N NP) (CYc st N NP) (st.boolAt "K")
        (st.boolAt "p") := by
      refine ⟨?pp, ?sm, ?cy, ?nx, ?k0, ?kk, ?pk⟩
      case pp =>
        intro k hk i hi
        have hNPN := NPn_ge N
        have hH := H0E N k hk
        have hlo := loE N k hN
        have hlo' : loF N k = k - (N - 1) := rfl
        have hH0 : H0F N k = min (k + 1) (2 * N - 1 - k) := rfl
        unfold Tc T0
        rw [rmN_zero_row]
        by_cases h1 : i < H0F N k
        · rw [ite_eq_left h1, eq_T_g_pp_g_bit_0 k (by omega) i (by rw [hNPn]; omega) (by rw [hH]; omega), hlo,
            bit_a, bit_b]
          · congr 2 <;> omega
          · omega
          · omega
        · rw [ite_eq_right h1, eq_T_g_pp_g_bit_1 k (by omega) i (by rw [hNPn]; omega) (by rw [hH]; omega)]
      case sm =>
        intro s hs k hk q hq
        stage_forms
        unfold SMc smB
        by_cases hw : q < uS N s - tS N s + 1
        · rw [ite_eq_left hw]
          by_cases h1 : q < fF N s (tS N s) (uS N s) k
          · rw [ite_eq_left h1]
            stage_eq eq_SM_g_add_0 as e
            rw [e q (by omega) h1]
            unfold Tc
            rw [show (3 : Int) * (q : Int) + 2 = ((3 * q + 2 : Nat) : Int) by omega,
              show (3 : Int) * (q : Int) + 1 = ((3 * q + 1 : Nat) : Int) by omega,
              show (3 : Int) * (q : Int) = ((3 * q : Nat) : Int) by omega]
          · rw [ite_eq_right h1]
            by_cases h2 : q < fF N s (tS N s) (uS N s) k + hF N s (tS N s) (uS N s) k
            · rw [ite_eq_left h2]
              stage_eq eq_SM_g_add_2 as e
              rw [e q (by omega) h1 (by omega)]
              unfold Tc
              rw [show (3 : Int) * (q : Int) + 1 = ((3 * q + 1 : Nat) : Int) by omega,
                show (3 : Int) * (q : Int) = ((3 * q : Nat) : Int) by omega]
            · rw [ite_eq_right h2]
              stage_eq eq_SM_g_add_4 as e
              exact e q (by omega) h1 (by omega)
        · rw [ite_eq_right hw]
          stage_eq eq_SM_g_c_1 as e
          have e' := e (q - (uS N s - tS N s + 1)) (by rw [hNPn]; omega)
          rw [rmN_slice (c := ((uS N s : Nat) : Int) + -1 * ((tS N s : Nat) : Int) + 1) (by omega)] at e'
          exact (rmN3_congr rfl rfl (by omega)).trans e'
      case cy =>
        intro s hs k hk q hq
        stage_forms
        unfold CYc cyB
        by_cases hw : q < uS N s - tS N s + 1
        · rw [ite_eq_left hw]
          by_cases h1 : q < fF N s (tS N s) (uS N s) k
          · rw [ite_eq_left h1]
            stage_eq eq_CY_g_add_1 as e
            rw [e q (by omega) h1]
            unfold Tc
            rw [show (3 : Int) * (q : Int) + 2 = ((3 * q + 2 : Nat) : Int) by omega,
              show (3 : Int) * (q : Int) + 1 = ((3 * q + 1 : Nat) : Int) by omega,
              show (3 : Int) * (q : Int) = ((3 * q : Nat) : Int) by omega]
          · rw [ite_eq_right h1]
            by_cases h2 : q < fF N s (tS N s) (uS N s) k + hF N s (tS N s) (uS N s) k
            · rw [ite_eq_left h2]
              stage_eq eq_CY_g_add_3 as e
              rw [e q (by omega) h1 (by omega)]
              unfold Tc
              rw [show (3 : Int) * (q : Int) + 1 = ((3 * q + 1 : Nat) : Int) by omega,
                show (3 : Int) * (q : Int) = ((3 * q : Nat) : Int) by omega]
            · rw [ite_eq_right h2]
              stage_eq eq_CY_g_add_5 as e
              exact e q (by omega) h1 (by omega)
        · rw [ite_eq_right hw]
          stage_eq eq_CY_g_c_2 as e
          have e' := e (q - (uS N s - tS N s + 1)) (by rw [hNPn]; omega)
          rw [rmN_slice (c := ((uS N s : Nat) : Int) + -1 * ((tS N s : Nat) : Int) + 1) (by omega)] at e'
          exact (rmN3_congr rfl rfl (by omega)).trans e'
      case nx =>
        intro s hs k hk i hi
        stage_forms
        have hht := id_height hst hk
        unfold nextCol
        by_cases ht : i < tS N s
        · rw [ite_eq_left ht]
          by_cases h1 : i < cF N (tS N s) (uS N s) k
          · rw [ite_eq_left h1]
            have hk1 : 1 ≤ k := by
              rcases Nat.eq_zero_or_pos k with rfl | h
              · omega
              · exact h
            stage_eq eq_T_g_st_g_t_g_u_g_col_g_f_g_h_g_c_g_bit_0 as e
            unfold Tc CYc
            exact (rmN3_congr (by omega) rfl rfl).trans ((e i ht h1).trans (rmN3_congr rfl (by omega) rfl))
          · rw [ite_eq_right h1]
            by_cases h2 : i < cF N (tS N s) (uS N s) k + fF N s (tS N s) (uS N s) k + hF N s (tS N s) (uS N s) k
            · rw [ite_eq_left h2]
              stage_eq eq_T_g_st_g_t_g_u_g_col_g_f_g_h_g_c_g_bit_1 as e
              unfold Tc SMc
              exact (rmN3_congr (by omega) rfl rfl).trans ((e i ht h1 (by omega)).trans (rmN3_congr rfl rfl (by omega)))
            · rw [ite_eq_right h2]
              by_cases h3 : i < HnF N (tS N s) k
              · rw [ite_eq_left h3]
                stage_eq eq_T_g_st_g_t_g_u_g_col_g_f_g_h_g_c_g_bit_2 as e
                unfold Tc
                exact (rmN3_congr (by omega) rfl rfl).trans
                  ((e i ht h1 (by omega) (by rw [hHne]; omega)).trans (rmN3_congr rfl rfl (by omega)))
              · rw [ite_eq_right h3]
                stage_eq eq_T_g_st_g_t_g_u_g_col_g_f_g_h_g_c_g_bit_3 as e
                unfold Tc
                exact (rmN3_congr (by omega) rfl rfl).trans (e i ht h1 (by omega) (by rw [hHne]; omega))
        · rw [ite_eq_right ht]
          stage_eq eq_T_g_c_4 as e
          have e' := e (i - tS N s) (by rw [hNPn]; omega)
          rw [rmN_slice (c := ((tS N s : Nat) : Int)) (by omega)] at e'
          unfold Tc
          exact (rmN3_congr (by omega) rfl (by omega)).trans e'
      case k0 => exact eq_K_plain_2
      case kk =>
        intro k hk
        unfold Tc
        rw [show ((0 : Nat) : Int) = 0 from rfl, show ((1 : Nat) : Int) = 1 from rfl, ← hSn]
        exact eq_K_g_fin_1 k (by omega)
      case pk =>
        intro k hk
        unfold Tc
        rw [show ((0 : Nat) : Int) = 0 from rfl, show ((1 : Nat) : Int) = 1 from rfl, ← hSn]
        exact eq_p_g_fin_0 k (by omega)
    -- the value of `p`, then the port from its known bits
    have hval := hv.out hN h30
    rw [bfVal_bv, bfVal_bv] at hval
    have hlt : x.toNat * y.toNat < 2 ^ (2 * N) := by
      rw [Nat.two_mul, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_lt x.isLt y.isLt
    have hPv : bfVal (BitVec.ofNat (2 * N) (x.toNat * y.toNat)).getLsbD (2 * N) = x.toNat * y.toNat := by
      rw [bfVal_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hkp : ∀ k, k < 2 * N →
        (∃ v, st.lookup "p" = some v ∧ v.width = (2 * (N : Int) + -1).natAbs + 1) ∧ KnownBit st "p" k :=
      fun k hk => known_p_g_fin_0 k (by omega)
    rw [SvState.port_ofBitVec hkp (by omega) (by omega)]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [XF.getLsbD_bv hk]
    exact bfVal_inj (2 * N) (hval.trans hPv.symm) k hk
  all_goals dadda_obligation

/-! ## Axioms -/

/--
info: 'Examples.«system-verilog».mul_dadda.mul_proof.mul_dadda_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mul_dadda_mul

end Examples.«system-verilog».mul_dadda.mul_proof
