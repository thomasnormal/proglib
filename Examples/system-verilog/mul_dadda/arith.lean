import LeanModels.Sv.CombLib

/-!
# The mathematics of the Dadda record (`mul_dadda`): plain `Bool`/`Nat`, no ls-sv

The record (`mul_dadda.sv`) reduces the columns of partial products of an `N`-bit multiplier with full and half adders,
stage by stage, down to two rows, then adds them with a ripple-carry adder. Its schedule (the stage count, the target
heights, the adder counts of a column) is written into the generate expressions as closed forms of `N`, the stage and
the column; here they are `Nat` functions (`nst`, `tS`, `uS`, `fF`, `hF`, `cF`, `HnF`, `H0F`).

* **The ledger** (sections 1 to 9): the weighted sum `Σ_k 2^k · (bits of column k)` is `A * B` for the partial
  products (`ldg_zero`) and is unchanged by a stage (`step_ledger`: a full adder is `x + y + z = s + 2c`, a half adder
  `x + y = s + 2c`, every bit no adder uses keeps its weight; the counts obey a few linear identities, `id_*`, decided
  region by region by `omega`); after the last stage every column holds at most two bits (`final_rows`), which the
  ripple-carry adder adds (`ripple_final`). These sections restate the column ledger of the svGolf Dadda entry's own
  proof (`dadda_rc.lean`, its plain-Lean part) over `LeanModels.Sv.CombLib`.
* **The netlist's view** (section 10): `DView` is what the netlist's equations say of its cells, one field per family
  of assigns, at `Nat` indices; `DView.cells` (by induction over the stages, every cell is the bit model `tv`) and
  `DView.out` (the output's value is `A * B`).

The record's own `?:` forms of these functions, and the netlist's equations, are met in `mul_proof.lean`.
-/

namespace Examples.«system-verilog».mul_dadda.arith

open LeanModels.Sv.CombLib

/-! ## 1. Finite sums -/

/-- `nsum f n = f 0 + … + f (n - 1)`. -/
def nsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => nsum f n + f n

@[simp] theorem nsum_zero (f : Nat → Nat) : nsum f 0 = 0 := rfl

theorem nsum_succ (f : Nat → Nat) (n : Nat) : nsum f (n + 1) = nsum f n + f n := rfl

theorem nsum_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) : nsum f n = nsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsum_succ, nsum_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem nsum_add (f g : Nat → Nat) (n : Nat) :
    nsum (fun i => f i + g i) n = nsum f n + nsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsum_succ, ih]; omega

theorem nsum_mul (c : Nat) (f : Nat → Nat) (n : Nat) :
    nsum (fun i => c * f i) n = c * nsum f n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [nsum_succ, ih, Nat.mul_add]

theorem nsum_eq_zero {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = 0) : nsum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsum_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem nsum_split (f : Nat → Nat) (m n : Nat) :
    nsum f (m + n) = nsum f m + nsum (fun i => f (m + i)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, nsum_succ, ih, nsum_succ]; omega

theorem nsum_front (f : Nat → Nat) (n : Nat) :
    nsum f (n + 1) = f 0 + nsum (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp [nsum]
  | succ n ih => rw [nsum_succ, ih, nsum_succ]; omega

theorem nsum_triple (f : Nat → Nat) (n : Nat) :
    nsum f (3 * n) = nsum (fun q => f (3 * q) + f (3 * q + 1) + f (3 * q + 2)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 2 + 1 by omega, nsum_succ, nsum_succ, nsum_succ, ih, nsum_succ]
    rw [show 3 * n + 2 = 3 * n + 1 + 1 by omega]
    omega

theorem nsum_swap (g : Nat → Nat → Nat) (m n : Nat) :
    nsum (fun k => nsum (fun i => g k i) m) n = nsum (fun i => nsum (fun k => g k i) n) m := by
  induction n with
  | zero => simp only [nsum_zero]; exact (nsum_eq_zero (fun _ _ => rfl)).symm
  | succ n ih =>
    rw [nsum_succ, ih]
    simp only [nsum_succ]
    rw [nsum_add]

theorem nsum_two (f : Nat → Nat) : nsum f 2 = f 0 + f 1 := by simp [nsum]

theorem nsum_one (f : Nat → Nat) : nsum f 1 = f 0 := by simp [nsum]

theorem nsum_split3 (F : Nat → Nat) (a b c : Nat) :
    nsum F (a + (b + c)) =
      nsum F a + nsum (fun i => F (a + i)) b + nsum (fun j => F (a + b + j)) c := by
  rw [nsum_split F a (b + c), nsum_split (fun i => F (a + i)) b c, ← Nat.add_assoc]
  congr 1
  apply nsum_congr
  intro i _
  rw [Nat.add_assoc]

/-- Zero terms past `m` do not count. -/
theorem nsum_extend (f : Nat → Nat) {m n : Nat} (hmn : m ≤ n) (h0 : ∀ i, m ≤ i → i < n → f i = 0) :
    nsum f n = nsum f m := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  rw [nsum_split, nsum_eq_zero (fun i hi => h0 (m + i) (by omega) (by omega)), Nat.add_zero]

/-- Zero terms below `m` do not count. -/
theorem nsum_shift_zero (f : Nat → Nat) {m n : Nat} (h0 : ∀ i < m, f i = 0) :
    nsum f (m + n) = nsum (fun i => f (m + i)) n := by
  rw [nsum_split, nsum_eq_zero h0, Nat.zero_add]

/-- A weighted bit sum is `bfVal`. -/
theorem bfVal_eq_nsum (f : Nat → Bool) (n : Nat) :
    bfVal f n = nsum (fun j => 2 ^ j * (f j).toNat) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bfVal, nsum_succ, ih]

theorem bfVal_lt (f : Nat → Bool) (n : Nat) : bfVal f n < 2 ^ n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    rw [bfVal, Nat.pow_succ]
    have := Bool.toNat_le (f n)
    have h2 : 2 ^ n * (f n).toNat ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ this
    omega

/-! ## 2. The Dadda heights and the number of stages -/

/-- `d(0) = 2`, `d(r+1) = d(r) + ⌊d(r) / 2⌋`: the 52 heights below `2^31`. -/
def ddTab : List Nat :=
  [2, 3, 4, 6, 9, 13, 19, 28, 42, 63, 94, 141, 211, 316, 474, 711, 1066, 1599, 2398, 3597, 5395,
   8092, 12138, 18207, 27310, 40965, 61447, 92170, 138255, 207382, 311073, 466609, 699913, 1049869,
   1574803, 2362204, 3543306, 5314959, 7972438, 11958657, 17937985, 26906977, 40360465, 60540697,
   90811045, 136216567, 204324850, 306487275, 459730912, 689596368, 1034394552, 1551591828]

def dd (r : Nat) : Nat := ddTab.getD r 0

theorem dd_succ_all : ∀ r, r < 51 → dd (r + 1) = dd r + dd r / 2 := by decide

theorem dd_ge_two_all : ∀ r, r < 52 → 2 ≤ dd r := by decide

theorem dd_zero : dd 0 = 2 := rfl

theorem dd_51 : 2 ^ 30 ≤ dd 51 := by decide

theorem dd_lt_succ {r : Nat} (hr : r < 51) : dd r < dd (r + 1) := by
  have h1 := dd_succ_all r hr
  have h2 := dd_ge_two_all r (by omega)
  omega

/-- The number of stages: the Dadda heights below `N`. -/
def nst (N : Nat) : Nat := nsum (fun r => if dd r < N then 1 else 0) 51

/-- An antitone indicator counts a prefix. -/
theorem count_prefix (P : Nat → Prop) [DecidablePred P] (hP : ∀ r, P (r + 1) → P r) :
    ∀ n, (nsum (fun r => if P r then 1 else 0) n ≤ n) ∧
      ∀ r < n, (P r ↔ r < nsum (fun r => if P r then 1 else 0) n) := by
  have anti : ∀ d r, P (r + d) → P r := by
    intro d
    induction d with
    | zero => intro r h; exact h
    | succ d ih => intro r h; exact ih r (hP (r + d) (by rw [← Nat.add_assoc] at h; exact h))
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hle, hiff⟩ := ih
    rw [nsum_succ]
    by_cases hn : P n
    · have hall : ∀ r, r ≤ n → P r := fun r hr => anti (n - r) r (by rwa [Nat.add_sub_of_le hr])
      have hcn : nsum (fun r => if P r then 1 else 0) n = n := by
        have hlt : ∀ r < n, r < nsum (fun r => if P r then 1 else 0) n :=
          fun r hr => (hiff r hr).mp (hall r (by omega))
        rcases n with _ | n
        · simp
        · have := hlt n (by omega); omega
      rw [ite_eq_left hn, hcn]
      exact ⟨by omega, fun r hr => ⟨fun _ => by omega, fun _ => hall r (by omega)⟩⟩
    · rw [ite_eq_right hn, Nat.add_zero]
      refine ⟨by omega, fun r hr => ?_⟩
      rcases Nat.lt_or_ge r n with h | h
      · exact hiff r h
      · obtain rfl : r = n := by omega
        exact ⟨fun h => absurd h hn, fun h => by omega⟩

theorem nst_spec (N : Nat) : nst N ≤ 51 ∧ ∀ r < 51, (dd r < N ↔ r < nst N) := by
  have hP : ∀ r, (r + 1 < 51 ∧ dd (r + 1) < N) → (r < 51 ∧ dd r < N) := by
    intro r ⟨h1, h2⟩
    exact ⟨by omega, Nat.lt_trans (dd_lt_succ (by omega)) h2⟩
  obtain ⟨hle, hiff⟩ := count_prefix (fun r => r < 51 ∧ dd r < N) hP 51
  have heq : nsum (fun r => if (r < 51 ∧ dd r < N) then 1 else 0) 51 = nst N := by
    unfold nst
    apply nsum_congr
    intro i hi
    by_cases h : dd i < N
    · simp [hi, h]
    · simp [h]
  rw [heq] at hle hiff
  refine ⟨hle, fun r hr => ?_⟩
  rw [← hiff r hr]
  exact ⟨fun h => ⟨hr, h⟩, fun h => h.2⟩

theorem nst_le (N : Nat) : nst N ≤ 51 := (nst_spec N).1

theorem nst_iff {N r : Nat} (hr : r < 51) : dd r < N ↔ r < nst N := (nst_spec N).2 r hr

theorem nst_eq_zero {N : Nat} (h : N ≤ 2) : nst N = 0 := by
  have h0 : ¬ (0 < nst N) := fun h' => by
    have := (nst_iff (N := N) (r := 0) (by omega)).mpr h'
    rw [dd_zero] at this
    omega
  omega

theorem le_two_of_nst {N : Nat} (h : nst N = 0) : N ≤ 2 := by
  have := (nst_iff (N := N) (r := 0) (by omega))
  rw [dd_zero, h] at this
  rcases Nat.lt_or_ge 2 N with h2 | h2
  · exact absurd (this.mp h2) (Nat.lt_irrefl 0)
  · exact h2

/-- The target of stage `s`: `d(S - 1 - s)`. -/
def tS (N s : Nat) : Nat := dd (nst N - 1 - s)

/-- The height bound before stage `s`: `N` at the first stage, `d(S - s) = t + ⌊t / 2⌋` after. -/
def uS (N s : Nat) : Nat := if s = 0 then N else tS N s + tS N s / 2

/-- What a stage needs of its two numbers. -/
structure Stg (N s t u : Nat) : Prop where
  t2 : 2 ≤ t
  tu : t < u
  uN : u ≤ N
  u3 : 2 * u ≤ 3 * t
  first : s = 0 → u = N

theorem stg_of {N s : Nat} (hN : N < 2 ^ 30) (hs : s < nst N) : Stg N s (tS N s) (uS N s) := by
  have hle := nst_le N
  have hr : nst N - 1 - s < nst N := by omega
  have hbelow : dd (nst N - 1 - s) < N := (nst_iff (by omega)).mpr hr
  have h2 := dd_ge_two_all (nst N - 1 - s) (by omega)
  unfold uS tS
  by_cases h0 : s = 0
  · subst h0
    rw [ite_eq_left rfl]
    simp only [Nat.sub_zero] at *
    have htop : N ≤ dd (nst N) := by
      by_cases h51 : nst N < 51
      · exact Nat.le_of_not_lt (fun h => Nat.lt_irrefl _ ((nst_iff h51).mp h))
      · have : nst N = 51 := by omega
        rw [this]; have := dd_51; omega
    have hsucc := dd_succ_all (nst N - 1) (by omega)
    rw [show nst N - 1 + 1 = nst N by omega] at hsucc
    exact ⟨h2, hbelow, Nat.le_refl _, by omega, fun _ => rfl⟩
  · rw [ite_eq_right h0]
    have hsucc := dd_succ_all (nst N - 1 - s) (by omega)
    have hb2 : dd (nst N - 1 - s + 1) < N :=
      (nst_iff (by omega)).mpr (by omega)
    rw [hsucc] at hb2
    exact ⟨h2, by omega, by omega, by omega, fun h => absurd h h0⟩

theorem uS_prev {N s : Nat} (hs : s < nst N) (h1 : 1 ≤ s) : uS N s = tS N (s - 1) := by
  have hle := nst_le N
  unfold uS tS
  rw [ite_eq_right (by omega)]
  have hsucc := dd_succ_all (nst N - 1 - s) (by omega)
  rw [show nst N - 1 - (s - 1) = nst N - 1 - s + 1 by omega, hsucc]

theorem tS_last {N : Nat} (h : 1 ≤ nst N) : tS N (nst N - 1) = 2 := by
  unfold tS
  rw [show nst N - 1 - (nst N - 1) = 0 by omega]
  rfl

/-! ## 3. The schedule of one column (closed forms) -/

/-- `1` if `p`, else `0`. -/
def ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

theorem ind_spec (p : Prop) [Decidable p] : (p ∧ ind p = 1) ∨ (¬ p ∧ ind p = 0) := by
  unfold ind
  by_cases h : p
  · exact Or.inl ⟨h, ite_eq_left h⟩
  · exact Or.inr ⟨h, ite_eq_right h⟩

def mF (N k : Nat) : Nat := min k (2 * N - k)
def mF' (N k : Nat) : Nat := min k (2 * N + 1 - k)
/-- Full adders of column `k`. -/
def fF (N s t u k : Nat) : Nat := (min (mF N k) u - t) - ind (s = 0 ∧ k = N)
/-- Half adders of column `k` (0 or 1). -/
def hF (N s t u k : Nat) : Nat := ind ((t ≤ k ∧ k < u) ∨ (s = 0 ∧ k = N))
/-- Carries into column `k`. -/
def cF (N t u k : Nat) : Nat := min (mF' N k) u - t
/-- Height of column `k` after a stage with target `t`. -/
def HnF (N t k : Nat) : Nat := if k ≤ 2 * N - t then min (k + 1) t else 2 * N - 1 - k
/-- Height of column `k` of the partial products. -/
def H0F (N k : Nat) : Nat := min (k + 1) (2 * N - 1 - k)
/-- Height of column `k` before a stage. -/
def HbF (N s u k : Nat) : Nat := if s = 0 then H0F N k else HnF N u k

theorem HnF_spec (N t k : Nat) :
    (k ≤ 2 * N - t ∧ HnF N t k = min (k + 1) t) ∨ (¬ k ≤ 2 * N - t ∧ HnF N t k = 2 * N - 1 - k) := by
  unfold HnF
  by_cases h : k ≤ 2 * N - t
  · exact Or.inl ⟨h, ite_eq_left h⟩
  · exact Or.inr ⟨h, ite_eq_right h⟩

theorem HbF_spec (N s u k : Nat) :
    (s = 0 ∧ HbF N s u k = min (k + 1) (2 * N - 1 - k)) ∨
      (s ≠ 0 ∧ k ≤ 2 * N - u ∧ HbF N s u k = min (k + 1) u) ∨
      (s ≠ 0 ∧ ¬ k ≤ 2 * N - u ∧ HbF N s u k = 2 * N - 1 - k) := by
  unfold HbF
  by_cases h : s = 0
  · exact Or.inl ⟨h, by rw [ite_eq_left h]; rfl⟩
  · rw [ite_eq_right h]
    rcases HnF_spec N u k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h, h1, h2⟩)

/-- The regions of a column index between the stage's thresholds. -/
theorem kregion (N t u k : Nat) :
    k < t ∨ (t ≤ k ∧ k < u) ∨ (u ≤ k ∧ k < N) ∨ k = N ∨ (N < k ∧ k ≤ 2 * N - u) ∨
      (2 * N - u < k ∧ k ≤ 2 * N - t) ∨ 2 * N - t < k := by
  omega

section ids

variable {N s t u : Nat} (hst : Stg N s t u)
include hst

set_option hygiene false in
/-- Every identity, region by region: the stage's facts in context, the column index placed between
the thresholds, every `min` and `if` decided by `omega`, then the linear goal. -/
macro "dsolve" k:term : tactic => `(tactic| (
  have := hst.t2; have := hst.tu; have := hst.uN; have := hst.u3; have := hst.first
  try unfold fF
  try unfold hF
  try unfold cF
  try unfold HbF
  try unfold H0F
  try unfold HnF
  try unfold mF
  try unfold mF'
  try unfold ind
  rcases kregion N t u $k with h | h | h | h | h | h | h <;>
    rcases Nat.eq_zero_or_pos s with h0 | h0 <;>
    simp (disch := omega) only [Nat.min_eq_left, Nat.min_eq_right, ite_eq_left, ite_eq_right] <;> omega))

theorem id_reads {k : Nat} (hk : k < 2 * N) : 3 * fF N s t u k + 2 * hF N s t u k ≤ HbF N s u k := by
  dsolve k

theorem id_carry0 : cF N t u 0 = 0 := by
  have := hst.t2
  unfold cF mF'
  omega

theorem id_carry {k : Nat} (hk : k + 1 < 2 * N) : cF N t u (k + 1) = fF N s t u k + hF N s t u k := by
  dsolve k

theorem id_height {k : Nat} (hk : k < 2 * N) :
    cF N t u k + fF N s t u k + hF N s t u k +
      (HbF N s u k - (3 * fF N s t u k + 2 * hF N s t u k)) = HnF N t k := by
  dsolve k

theorem id_slots {k : Nat} (hk : k < 2 * N) : fF N s t u k + hF N s t u k ≤ u - t + 1 := by
  dsolve k

theorem id_top_f : fF N s t u (2 * N - 1) = 0 := by
  dsolve (2 * N - 1)

theorem id_top_h : hF N s t u (2 * N - 1) = 0 := by
  dsolve (2 * N - 1)

theorem id_top : fF N s t u (2 * N - 1) = 0 ∧ hF N s t u (2 * N - 1) = 0 :=
  ⟨id_top_f hst, id_top_h hst⟩

theorem id_Hb_le {k : Nat} : HbF N s u k ≤ N := by
  dsolve k

omit hst in
theorem id_h_le {k : Nat} : hF N s t u k ≤ 1 := by
  have := ind_spec ((t ≤ k ∧ k < u) ∨ (s = 0 ∧ k = N))
  unfold hF
  omega

end ids

theorem HnF_le (N t k : Nat) : HnF N t k ≤ t := by
  have := HnF_spec N t k
  omega

theorem add_congr' {a b c d : Nat} (h1 : a = b) (h2 : c = d) : a + c = b + d := by rw [h1, h2]

/-! ## 4. The model of the bits -/

/-- The `b` offset of column `k`'s partial products: `max(0, k - N + 1)`. -/
def loF (N k : Nat) : Nat := k - (N - 1)

/-- Stage 0: the partial products of column `k`, zeros above the column's height. -/
def T0 (N : Nat) (A B : Nat → Bool) (k i : Nat) : Bool :=
  if i < H0F N k then A (k - i - loF N k) && B (i + loF N k) else false

/-- The sum of adder `q` of column `k` in a stage (`false` above the adders). -/
def smB (N s t u : Nat) (T : Nat → Nat → Bool) (k q : Nat) : Bool :=
  if q < u - t + 1 then
    if q < fF N s t u k then (T k (3 * q) ^^ T k (3 * q + 1)) ^^ T k (3 * q + 2)
    else if q < fF N s t u k + hF N s t u k then T k (3 * q) ^^ T k (3 * q + 1)
    else false
  else false

/-- The carry of adder `q` of column `k` in a stage. -/
def cyB (N s t u : Nat) (T : Nat → Nat → Bool) (k q : Nat) : Bool :=
  if q < u - t + 1 then
    if q < fF N s t u k then
      (T k (3 * q) && T k (3 * q + 1)) || (T k (3 * q + 2) && (T k (3 * q) ^^ T k (3 * q + 1)))
    else if q < fF N s t u k + hF N s t u k then T k (3 * q) && T k (3 * q + 1)
    else false
  else false

/-- Column `k` after a stage: carries in, sums, the bits no adder used, zeros. -/
def stepT (N s t u : Nat) (T : Nat → Nat → Bool) (k i : Nat) : Bool :=
  if i < t then
    if i < cF N t u k then cyB N s t u T (k - 1) i
    else if i < cF N t u k + fF N s t u k + hF N s t u k then smB N s t u T k (i - cF N t u k)
    else if i < HnF N t k then T k (i - cF N t u k + 2 * fF N s t u k + hF N s t u k)
    else false
  else false

/-- The bits before stage `s`. -/
def tv (N : Nat) (A B : Nat → Bool) : Nat → Nat → Nat → Bool
  | 0 => T0 N A B
  | s + 1 => stepT N s (tS N s) (uS N s) (tv N A B s)

/-- The height of the columns before stage `s`. -/
def Hs (N s k : Nat) : Nat := if s = 0 then H0F N k else HnF N (tS N (s - 1)) k

/-! ## 5. One column through one stage -/

theorem col_new (T Tn cy sm : Nat → Bool) (c f h Hb Hn t : Nat)
    (hH : c + f + h + (Hb - (3 * f + 2 * h)) = Hn) (hHt : Hn ≤ t)
    (hTn : ∀ i, Tn i = if i < t then (if i < c then cy i else if i < c + f + h then sm (i - c)
      else if i < Hn then T (i - c + 2 * f + h) else false) else false) :
    nsum (fun i => (Tn i).toNat) Hn =
      nsum (fun i => (cy i).toNat) c + nsum (fun q => (sm q).toNat) (f + h) +
        nsum (fun j => (T (3 * f + 2 * h + j)).toNat) (Hb - (3 * f + 2 * h)) := by
  rw [← hH, show c + f + h + (Hb - (3 * f + 2 * h)) = c + ((f + h) + (Hb - (3 * f + 2 * h))) by omega,
    nsum_split3]
  refine add_congr' (add_congr' ?_ ?_) ?_
  · apply nsum_congr
    intro i hi
    have c1 : i < t := by omega
    simp only [hTn, c1, hi, ite_true]
  · apply nsum_congr
    intro q hq
    have c1 : c + q < t := by omega
    have c2 : ¬ c + q < c := by omega
    have c3 : c + q < c + f + h := by omega
    simp only [hTn, c1, c2, c3, ite_true, ite_false, Nat.add_sub_cancel_left]
  · apply nsum_congr
    intro j hj
    have c1 : c + (f + h) + j < t := by omega
    have c2 : ¬ c + (f + h) + j < c := by omega
    have c3 : ¬ c + (f + h) + j < c + f + h := by omega
    have c5 : c + (f + h) + j < Hn := by omega
    simp only [hTn, c1, c2, c3, c5, ite_true, ite_false]
    all_goals rw [show c + (f + h) + j - c + 2 * f + h = 3 * f + 2 * h + j by omega]

theorem ha_arith (x y : Bool) : (x ^^ y).toNat + 2 * (x && y).toNat = x.toNat + y.toNat := by
  cases x <;> cases y <;> decide

theorem col_old (T sm cy : Nat → Bool) (f h w Hb : Nat) (hh : h ≤ 1) (hw : f + h ≤ w)
    (hR : 3 * f + 2 * h ≤ Hb)
    (hsm : ∀ q, sm q = if q < w then (if q < f then (T (3 * q) ^^ T (3 * q + 1)) ^^ T (3 * q + 2)
      else if q < f + h then T (3 * q) ^^ T (3 * q + 1) else false) else false)
    (hcy : ∀ q, cy q = if q < w then (if q < f then
        (T (3 * q) && T (3 * q + 1)) || (T (3 * q + 2) && (T (3 * q) ^^ T (3 * q + 1)))
      else if q < f + h then T (3 * q) && T (3 * q + 1) else false) else false) :
    nsum (fun i => (T i).toNat) Hb =
      nsum (fun q => (sm q).toNat) (f + h) + 2 * nsum (fun q => (cy q).toNat) (f + h) +
        nsum (fun j => (T (3 * f + 2 * h + j)).toNat) (Hb - (3 * f + 2 * h)) := by
  obtain ⟨R, rfl⟩ : ∃ R, Hb = 3 * f + 2 * h + R := ⟨Hb - (3 * f + 2 * h), by omega⟩
  rw [Nat.add_sub_cancel_left, nsum_split (fun i => (T i).toNat) (3 * f + 2 * h) R,
    nsum_split (fun i => (T i).toNat) (3 * f) (2 * h), nsum_triple]
  refine add_congr' ?_ rfl
  rw [← nsum_mul, ← nsum_add, nsum_split (fun q => (sm q).toNat + 2 * (cy q).toNat) f h]
  refine add_congr' ?_ ?_
  · apply nsum_congr
    intro q hq
    have c1 : q < w := by omega
    simp only [hsm, hcy, c1, hq, ite_true]
    have := fullAdder_arith (T (3 * q)) (T (3 * q + 1)) (T (3 * q + 2))
    omega
  · rcases (show h = 0 ∨ h = 1 by omega) with rfl | rfl
    · rfl
    · rw [show 2 * 1 = 2 from rfl, nsum_two, nsum_one]
      have c1 : f < w := by omega
      have c2 : ¬ f < f := Nat.lt_irrefl f
      have c3 : f < f + 1 := Nat.lt_succ_self f
      simp only [Nat.add_zero, hsm, hcy, c1, c2, c3, ite_true, ite_false]
      have := ha_arith (T (3 * f)) (T (3 * f + 1))
      omega

/-! ## 6. The ledger is unchanged by a stage -/

/-- The weighted sum of the columns, column `k` holding the bits below `H k`. -/
def ldg (N : Nat) (H : Nat → Nat) (T : Nat → Nat → Bool) : Nat :=
  nsum (fun k => 2 ^ k * nsum (fun i => (T k i).toNat) (H k)) (2 * N)

theorem ldg_congr {N : Nat} {H H' : Nat → Nat} {T T' : Nat → Nat → Bool}
    (hH : ∀ k < 2 * N, H k = H' k) (hT : ∀ k < 2 * N, ∀ i < H k, T k i = T' k i) :
    ldg N H T = ldg N H' T' := by
  unfold ldg
  apply nsum_congr
  intro k hk
  rw [← hH k hk]
  congr 1
  apply nsum_congr
  intro i hi
  rw [hT k hk i hi]

theorem step_ledger {N s t u : Nat} (hN : 1 ≤ N) (hst : Stg N s t u) (T : Nat → Nat → Bool) :
    ldg N (HnF N t) (stepT N s t u T) = ldg N (HbF N s u) T := by
  -- the per-column parts
  let SMs : Nat → Nat := fun k =>
    nsum (fun q => (smB N s t u T k q).toNat) (fF N s t u k + hF N s t u k)
  let CYs : Nat → Nat := fun k =>
    nsum (fun q => (cyB N s t u T k q).toNat) (fF N s t u k + hF N s t u k)
  let R : Nat → Nat := fun k =>
    nsum (fun j => (T k (3 * fF N s t u k + 2 * hF N s t u k + j)).toNat)
      (HbF N s u k - (3 * fF N s t u k + 2 * hF N s t u k))
  let CYp : Nat → Nat := fun k => nsum (fun i => (cyB N s t u T (k - 1) i).toNat) (cF N t u k)
  have hnew : ∀ k < 2 * N, nsum (fun i => (stepT N s t u T k i).toNat) (HnF N t k) =
      CYp k + SMs k + R k := by
    intro k hk
    exact col_new (T k) (stepT N s t u T k) (cyB N s t u T (k - 1)) (smB N s t u T k)
      (cF N t u k) (fF N s t u k) (hF N s t u k) (HbF N s u k) (HnF N t k) t
      (id_height hst hk) (HnF_le N t k) (fun i => rfl)
  have hold : ∀ k < 2 * N, nsum (fun i => (T k i).toNat) (HbF N s u k) =
      SMs k + 2 * CYs k + R k := by
    intro k hk
    exact col_old (T k) (smB N s t u T k) (cyB N s t u T k) (fF N s t u k) (hF N s t u k)
      (u - t + 1) (HbF N s u k) id_h_le (id_slots hst hk) (id_reads hst hk)
      (fun q => rfl) (fun q => rfl)
  have hp0 : CYp 0 = 0 := by
    show nsum _ (cF N t u 0) = 0
    rw [id_carry0 hst]; rfl
  have hp1 : ∀ k, k + 1 < 2 * N → CYp (k + 1) = CYs k := by
    intro k hk
    show nsum _ (cF N t u (k + 1)) = _
    rw [id_carry hst hk]
    rfl
  obtain ⟨M, hM⟩ : ∃ M, 2 * N = M + 1 := ⟨2 * N - 1, by omega⟩
  have htop : CYs M = 0 := by
    show nsum _ (fF N s t u M + hF N s t u M) = 0
    have ht := id_top hst
    rw [show 2 * N - 1 = M by omega] at ht
    rw [ht.1, ht.2]; rfl
  have L1 : ldg N (HnF N t) (stepT N s t u T) =
      nsum (fun k => 2 ^ k * CYp k) (2 * N) + nsum (fun k => 2 ^ k * (SMs k + R k)) (2 * N) := by
    unfold ldg
    rw [← nsum_add]
    apply nsum_congr
    intro k hk
    rw [hnew k hk]
    simp only [Nat.mul_add]
    omega
  have L2 : ldg N (HbF N s u) T =
      nsum (fun k => 2 ^ k * (2 * CYs k)) (2 * N) + nsum (fun k => 2 ^ k * (SMs k + R k)) (2 * N) := by
    unfold ldg
    rw [← nsum_add]
    apply nsum_congr
    intro k hk
    rw [hold k hk]
    simp only [Nat.mul_add]
    omega
  rw [L1, L2]
  refine add_congr' ?_ rfl
  rw [hM, nsum_front (fun k => 2 ^ k * CYp k) M, nsum_succ (fun k => 2 ^ k * (2 * CYs k)) M, hp0,
    htop]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  apply nsum_congr
  intro k hk
  rw [hp1 k (by omega), Nat.pow_succ, Nat.mul_assoc]

/-! ## 7. Stage 0: the partial products hold the product -/

theorem ldg_zero (N : Nat) (hN : 1 ≤ N) (A B : Nat → Bool) :
    ldg N (H0F N) (T0 N A B) = bfVal A N * bfVal B N := by
  -- the partial product of column `k` with `b` index `j`
  let P : Nat → Nat → Nat := fun k j => if j ≤ k ∧ k - j < N then (A (k - j) && B j).toNat else 0
  have hcol : ∀ k < 2 * N, nsum (fun i => (T0 N A B k i).toNat) (H0F N k) = nsum (P k) N := by
    intro k hk
    by_cases hkN : k < N
    · have hH : H0F N k = k + 1 := by unfold H0F; omega
      have hlo : loF N k = 0 := by unfold loF; omega
      rw [nsum_extend (P k) (m := k + 1) (by omega) (fun i hi _ => by
        show (if i ≤ k ∧ k - i < N then _ else 0) = 0
        rw [ite_eq_right (by omega)]), hH]
      apply nsum_congr
      intro i hi
      have c1 : i < H0F N k := by omega
      have c2 : i ≤ k ∧ k - i < N := by omega
      show (if i < H0F N k then _ else false).toNat = if i ≤ k ∧ k - i < N then _ else 0
      rw [ite_eq_left c1, ite_eq_left c2, hlo, Nat.sub_zero, Nat.add_zero]
    · have hH : H0F N k = 2 * N - 1 - k := by unfold H0F; omega
      have e := nsum_shift_zero (P k) (m := k - (N - 1)) (n := 2 * N - 1 - k) (fun i hi => by
        show (if i ≤ k ∧ k - i < N then _ else 0) = 0
        rw [ite_eq_right (by omega)])
      rw [show k - (N - 1) + (2 * N - 1 - k) = N by omega] at e
      rw [e, hH]
      apply nsum_congr
      intro i hi
      have c1 : i < H0F N k := by omega
      have c2 : k - (N - 1) + i ≤ k ∧ k - (k - (N - 1) + i) < N := by omega
      show (if i < H0F N k then _ else false).toNat =
        if k - (N - 1) + i ≤ k ∧ k - (k - (N - 1) + i) < N then _ else 0
      rw [ite_eq_left c1, ite_eq_left c2]
      unfold loF
      rw [show k - i - (k - (N - 1)) = k - (k - (N - 1) + i) by omega, Nat.add_comm i]
  have hL : ldg N (H0F N) (T0 N A B) = nsum (fun k => nsum (fun j => 2 ^ k * P k j) N) (2 * N) := by
    unfold ldg
    apply nsum_congr
    intro k hk
    rw [hcol k hk, nsum_mul]
  rw [hL, nsum_swap (fun k j => 2 ^ k * P k j)]
  -- one `b` bit: its row of partial products
  have hrow : ∀ j < N, nsum (fun k => 2 ^ k * P k j) (2 * N) =
      2 ^ j * (B j).toNat * bfVal A N := by
    intro j hj
    have e1 := nsum_shift_zero (fun k => 2 ^ k * P k j) (m := j) (n := 2 * N - j) (fun i hi => by
      show 2 ^ i * (if j ≤ i ∧ i - j < N then _ else 0) = 0
      rw [ite_eq_right (by omega), Nat.mul_zero])
    rw [show j + (2 * N - j) = 2 * N by omega] at e1
    rw [e1, nsum_extend _ (m := N) (by omega) (fun i hi1 hi2 => by
      show 2 ^ (j + i) * (if j ≤ j + i ∧ j + i - j < N then _ else 0) = 0
      rw [ite_eq_right (by omega), Nat.mul_zero]), bfVal_eq_nsum, ← nsum_mul]
    apply nsum_congr
    intro i hi
    show 2 ^ (j + i) * (if j ≤ j + i ∧ j + i - j < N then _ else 0) = _
    rw [ite_eq_left (show j ≤ j + i ∧ j + i - j < N by omega), show j + i - j = i by omega, Nat.pow_add]
    cases A i <;> cases B j <;> simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [nsum_congr hrow, bfVal_eq_nsum B N, ← nsum_mul]
  exact nsum_congr (fun j _ => Nat.mul_comm _ _)

/-! ## 8. Every stage keeps the product; the last leaves two rows -/

theorem tv_zero {N : Nat} (A B : Nat → Bool) (hN : N < 2 ^ 30) :
    ∀ s, s ≤ nst N → ∀ k i, k < 2 * N → Hs N s k ≤ i → tv N A B s k i = false := by
  intro s hs k i hk hi
  cases s with
  | zero =>
    have c1 : ¬ i < H0F N k := by simp [Hs] at hi; omega
    show (if i < H0F N k then _ else false) = false
    rw [ite_eq_right c1]
  | succ s =>
    have hst := stg_of hN (show s < nst N by omega)
    have hh := id_height hst hk
    have hi' : HnF N (tS N s) k ≤ i := by simpa [Hs] using hi
    show stepT N s (tS N s) (uS N s) (tv N A B s) k i = false
    unfold stepT
    have c1 : ¬ i < cF N (tS N s) (uS N s) k := by omega
    have c2 : ¬ i < cF N (tS N s) (uS N s) k + fF N s (tS N s) (uS N s) k +
        hF N s (tS N s) (uS N s) k := by omega
    have c3 : ¬ i < HnF N (tS N s) k := by omega
    simp only [c1, c2, c3, ite_false, ite_self]

theorem tv_ledger {N : Nat} (hN1 : 1 ≤ N) (hN : N < 2 ^ 30) (A B : Nat → Bool) :
    ∀ s, s ≤ nst N → ldg N (Hs N s) (tv N A B s) = bfVal A N * bfVal B N := by
  intro s
  induction s with
  | zero =>
    intro _
    rw [← ldg_zero N hN1 A B]
    exact ldg_congr (fun k _ => by simp [Hs]) (fun k _ i _ => rfl)
  | succ s ih =>
    intro hs
    have hst := stg_of hN (show s < nst N by omega)
    have e1 : ldg N (Hs N (s + 1)) (tv N A B (s + 1)) =
        ldg N (HnF N (tS N s)) (stepT N s (tS N s) (uS N s) (tv N A B s)) :=
      ldg_congr (fun k _ => by simp [Hs]) (fun k _ i _ => rfl)
    have e2 : ldg N (HbF N s (uS N s)) (tv N A B s) = ldg N (Hs N s) (tv N A B s) := by
      apply ldg_congr _ (fun k _ i _ => rfl)
      intro k _
      unfold HbF Hs
      by_cases h0 : s = 0
      · simp [h0]
      · rw [ite_eq_right h0, ite_eq_right h0, uS_prev (by omega) (by omega)]
    rw [e1, step_ledger hN1 hst, e2, ih (by omega)]

/-- **The two rows left after the last stage add up to the product.** -/
theorem final_rows {N : Nat} (hN1 : 1 ≤ N) (hN : N < 2 ^ 30) (A B : Nat → Bool) :
    bfVal (fun k => tv N A B (nst N) k 0) (2 * N) + bfVal (fun k => tv N A B (nst N) k 1) (2 * N) =
      bfVal A N * bfVal B N := by
  rw [← tv_ledger hN1 hN A B (nst N) (Nat.le_refl _)]
  unfold ldg
  rw [bfVal_eq_nsum, bfVal_eq_nsum, ← nsum_add]
  apply nsum_congr
  intro k hk
  have hle : Hs N (nst N) k ≤ 2 := by
    unfold Hs
    split
    · have := le_two_of_nst (by assumption)
      unfold H0F
      omega
    · exact Nat.le_trans (HnF_le _ _ _) (Nat.le_of_eq (tS_last (by omega)))
  have hz := tv_zero A B hN (nst N) (Nat.le_refl _) k
  rcases (show Hs N (nst N) k = 0 ∨ Hs N (nst N) k = 1 ∨ Hs N (nst N) k = 2 by omega) with h | h | h
  · rw [h, hz 0 hk (by omega), hz 1 hk (by omega)]
    simp
  · rw [h, hz 1 hk (by omega), nsum_one]
    simp
  · rw [h, nsum_two, Nat.mul_add]

/-! ## 9. The final ripple-carry adder -/

theorem ripple_final (n : Nat) (x y p K : Nat → Bool) (hK0 : K 0 = false)
    (hp : ∀ k < n, p k = ((x k ^^ y k) ^^ K k))
    (hK : ∀ k < n, K (k + 1) = ((x k && y k) || (K k && (x k ^^ y k))))
    (hv : bfVal x n + bfVal y n < 2 ^ n) : bfVal p n = bfVal x n + bfVal y n := by
  have h := ripple_row n x y (fun j => x j ^^ y j) p K (fun j _ => rfl) hp hK
  rw [hK0] at h
  have hb := bfVal_lt p n
  cases hKn : K n
  · rw [hKn] at h
    simp at h
    omega
  · rw [hKn] at h
    simp at h
    omega

/-! ## 10. The netlist's view, and the product it computes -/

/-- `NP`: the bits per column in the record's arrays (at least the two final rows). -/
def NPn (N : Nat) : Nat := if N < 2 then 2 else N

theorem NPn_ge (N : Nat) : N ≤ NPn N := by unfold NPn; split <;> omega
theorem NPn_two (N : Nat) : 2 ≤ NPn N := by unfold NPn; split <;> omega

/-- Column `k` after stage `s` as the record's assigns write it from the cells of the stage (`T` before it, the sums
`SM` and carries `CY` of its adders). -/
def nextCol (N s : Nat) (T SM CY : Nat → Nat → Bool) (k i : Nat) : Bool :=
  if i < tS N s then
    if i < cF N (tS N s) (uS N s) k then CY (k - 1) i
    else if i < cF N (tS N s) (uS N s) k + fF N s (tS N s) (uS N s) k + hF N s (tS N s) (uS N s) k then
      SM k (i - cF N (tS N s) (uS N s) k)
    else if i < HnF N (tS N s) k then
      T k (i - cF N (tS N s) (uS N s) k + 2 * fF N s (tS N s) (uS N s) k + hF N s (tS N s) (uS N s) k)
    else false
  else false

/-- **What the netlist's equations say of its cells**, one field per family of assigns, at `Nat` indices: `T s k i`
(bit `i` of column `k` before stage `s`), `SM s k q`, `CY s k q` (the sum and carry of adder `q` of column `k` in stage
`s`), the final adder's carries `K` and the output `P`. -/
structure DView (N : Nat) (A B : Nat → Bool) (T SM CY : Nat → Nat → Nat → Bool) (K P : Nat → Bool) : Prop where
  pp : ∀ k < 2 * N, ∀ i < NPn N, T 0 k i = T0 N A B k i
  sm : ∀ s < nst N, ∀ k < 2 * N, ∀ q < NPn N, SM s k q = smB N s (tS N s) (uS N s) (T s) k q
  cy : ∀ s < nst N, ∀ k < 2 * N, ∀ q < NPn N, CY s k q = cyB N s (tS N s) (uS N s) (T s) k q
  nx : ∀ s < nst N, ∀ k < 2 * N, ∀ i < NPn N, T (s + 1) k i = nextCol N s (T s) (SM s) (CY s) k i
  k0 : K 0 = false
  kk : ∀ k < 2 * N, K (k + 1) = ((T (nst N) k 0 && T (nst N) k 1) || (K k && (T (nst N) k 0 ^^ T (nst N) k 1)))
  pk : ∀ k < 2 * N, P k = ((T (nst N) k 0 ^^ T (nst N) k 1) ^^ K k)

theorem smB_congr {N s t u : Nat} {T T' : Nat → Nat → Bool} {k q : Nat}
    (h : ∀ j, j < 3 * fF N s t u k + 2 * hF N s t u k → T k j = T' k j) (hh : hF N s t u k ≤ 1) :
    smB N s t u T k q = smB N s t u T' k q := by
  unfold smB
  split
  · split
    · rw [h (3 * q) (by omega), h (3 * q + 1) (by omega), h (3 * q + 2) (by omega)]
    · split
      · rw [h (3 * q) (by omega), h (3 * q + 1) (by omega)]
      · rfl
  · rfl

theorem cyB_congr {N s t u : Nat} {T T' : Nat → Nat → Bool} {k q : Nat}
    (h : ∀ j, j < 3 * fF N s t u k + 2 * hF N s t u k → T k j = T' k j) (hh : hF N s t u k ≤ 1) :
    cyB N s t u T k q = cyB N s t u T' k q := by
  unfold cyB
  split
  · split
    · rw [h (3 * q) (by omega), h (3 * q + 1) (by omega), h (3 * q + 2) (by omega)]
    · split
      · rw [h (3 * q) (by omega), h (3 * q + 1) (by omega)]
      · rfl
  · rfl

/-- The cells before every stage are the bit model `tv`. -/
theorem DView.cells {N : Nat} {A B : Nat → Bool} {T SM CY : Nat → Nat → Nat → Bool} {K P : Nat → Bool}
    (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) (hv : DView N A B T SM CY K P) :
    ∀ s ≤ nst N, ∀ k < 2 * N, ∀ i < NPn N, T s k i = tv N A B s k i := by
  have hNP := NPn_ge N
  intro s
  induction s with
  | zero => intro _ k hk i hi; exact hv.pp k hk i hi
  | succ s ih =>
    intro hs k hk i hi
    have hst := stg_of h30 (show s < nst N by omega)
    have ih' := ih (by omega)
    -- the cells a stage reads are the model's
    have hrd : ∀ k', k' < 2 * N → ∀ j, j < 3 * fF N s (tS N s) (uS N s) k' + 2 * hF N s (tS N s) (uS N s) k' →
        T s k' j = tv N A B s k' j := by
      intro k' hk' j hj
      have := id_reads hst hk'
      have := id_Hb_le hst (k := k')
      exact ih' k' hk' j (by omega)
    rw [hv.nx s (by omega) k hk i hi]
    show nextCol N s (T s) (SM s) (CY s) k i = stepT N s (tS N s) (uS N s) (tv N A B s) k i
    unfold nextCol stepT
    have hht := id_height hst hk
    have hc0 := id_carry0 hst
    have hbl := id_Hb_le hst (k := k)
    split
    · split
      · rename_i _ h1
        have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with rfl | h
          · omega
          · exact h
        rw [hv.cy s (by omega) (k - 1) (by omega) i hi]
        exact cyB_congr (hrd (k - 1) (by omega)) id_h_le
      · split
        · rw [hv.sm s (by omega) k hk _ (by omega)]
          exact smB_congr (hrd k hk) id_h_le
        · split
          · exact ih' k hk _ (by omega)
          · rfl
    · rfl

/-- The carries of the final adder. -/
def kc (N : Nat) (A B : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => (tv N A B (nst N) k 0 && tv N A B (nst N) k 1) ||
      (kc N A B k && (tv N A B (nst N) k 0 ^^ tv N A B (nst N) k 1))

/-- Two bit functions with the same value agree below the width. -/
theorem bfVal_inj {f g : Nat → Bool} : ∀ n, bfVal f n = bfVal g n → ∀ j < n, f j = g j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, h, j, hj => by
    have h1 := bfVal_lt f n
    have h2 := bfVal_lt g n
    rw [bfVal, bfVal] at h
    have hfn : f n = g n ∧ bfVal f n = bfVal g n := by
      cases hf : f n <;> cases hg : g n <;> simp [hf, hg] at h ⊢ <;> omega
    rcases Nat.lt_or_ge j n with hj' | hj'
    · exact bfVal_inj n hfn.2 j hj'
    · obtain rfl : j = n := by omega
      exact hfn.1

/-- **The netlist computes the product**: the output's value is `A * B`. -/
theorem DView.out {N : Nat} {A B : Nat → Bool} {T SM CY : Nat → Nat → Nat → Bool} {K P : Nat → Bool}
    (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) (hv : DView N A B T SM CY K P) :
    bfVal P (2 * N) = bfVal A N * bfVal B N := by
  have hP2 := NPn_two N
  have hS := hv.cells hN1 h30 (nst N) (Nat.le_refl _)
  have hK : ∀ k ≤ 2 * N, K k = kc N A B k := by
    intro k
    induction k with
    | zero => intro _; exact hv.k0
    | succ k ih =>
      intro hk
      rw [hv.kk k (by omega), ih (by omega), hS k (by omega) 0 (by omega), hS k (by omega) 1 (by omega)]
      rfl
  have hrows := final_rows hN1 h30 A B
  have hlt : bfVal A N * bfVal B N < 2 ^ (2 * N) := by
    rw [Nat.two_mul, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (bfVal_lt A N) (bfVal_lt B N)
  have hrip := ripple_final (2 * N) (fun k => tv N A B (nst N) k 0) (fun k => tv N A B (nst N) k 1)
    (fun k => (tv N A B (nst N) k 0 ^^ tv N A B (nst N) k 1) ^^ kc N A B k)
    (kc N A B) rfl (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hrows]; exact hlt)
  rw [hrows] at hrip
  rw [← hrip]
  apply bfVal_congr
  intro k hk
  rw [hv.pk k hk, hS k hk 0 (by omega), hS k hk 1 (by omega), hK k (by omega)]

end Examples.«system-verilog».mul_dadda.arith
