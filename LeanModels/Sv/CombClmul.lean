import LeanModels.Sv.XorSum
import LeanModels.Sv.PinAxioms

/-!
# Carry-less products over GF(2): XOR sums, the product, Karatsuba (comb lane, untrusted library lemmas)

The mathematics a proof of a carry-less multiplier reaches once the comb tactics have handed it the equations of the
netlist over `Bool`: plain `Bool`/`Nat` lemmas, no design and no ls-sv term. A polynomial over GF(2) is the function
`Nat → Bool` of its coefficients; its sums are XOR sums `XorSum.bx f n` (the XOR of `f 0, …, f (n-1)`).

* **XOR sums**: `bx_succ`, `bx_congr`, `bx_trunc`, `bx_false`, `bx_add`, `bx_xor`, `bx_and`, `bx_pair` (one term of a
  sum survives where only one index meets a condition).
* **The carry-less product** `cl n A B k`: coefficient `k` of the product of the two polynomials of degree below `n`
  whose coefficients are `A`, `B` (the XOR over `i + j = k`, `i, j < n`, of `A i && B j`); `cl_congr` (it reads the
  first `n` coefficients only), `cl_big` (degree at most `2n - 2`), `cl_shift`, `cl_trunc` (operands that vanish from
  `N` on: the product over `M ≥ N` positions is the product over `N`), `cl_sum`.
* **Karatsuba**: one split of a `2H`-coefficient product into its four half products (`karatsuba`), the middle terms
  from the product of the half sums (`karatsuba_full`: `(aL + x^H aH)(bL + x^H bH) = L + x^H((aL+aH)(bL+bH) + L + H) +
  x^2H H`, `L = aL bL`, `H = aH bH`), and the same column by column (`karatsuba_cols`: the low, high and middle
  products of a node and its `4H - 1` output columns written as a netlist writes them give the `2H`-coefficient
  product).
* **The 4-coefficient base**: `cl_four_0` … `cl_four_6`, the seven coefficients of a 4 x 4 product as XOR trees of
  partial products.

The XOR-sum and Karatsuba lemmas are the ones the svGolf combinational proofs state for themselves
(`SvGolf/CombLemmas.lean`), restated here over `LeanModels.Sv.XorSum.bx` so that a proof in this repository can use
them. Nothing here is trusted; every theorem is proved and pins its axioms at the end.
-/

namespace LeanModels.Sv.CombClmul

open LeanModels.Sv.XorSum

/-! ## XOR sums -/

theorem bx_succ (f : Nat → Bool) (n : Nat) : bx f (n + 1) = (bx f n ^^ f n) := rfl

theorem bx_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j, j < n → f j = g j) : bx f n = bx g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bx]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

/-- Terms `n ≤ j < m` that are `false` do not change the sum. -/
theorem bx_trunc {f : Nat → Bool} {n m : Nat} (hnm : n ≤ m) (h : ∀ j, n ≤ j → j < m → f j = false) :
    bx f m = bx f n := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst hn; rfl
    · simp only [bx]
      rw [ih (by omega) (fun j hj1 hj2 => h j hj1 (by omega)), h m (by omega) (by omega)]
      simp

theorem bx_false {f : Nat → Bool} {n : Nat} (h : ∀ t, t < n → f t = false) : bx f n = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bx_succ, ih (fun t ht => h t (by omega)), h n (by omega)]; rfl

/-- A sum over `m + n` terms, split at `m`. -/
theorem bx_add (f : Nat → Bool) (m n : Nat) :
    bx f (m + n) = (bx f m ^^ bx (fun t => f (m + t)) n) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    rw [← Nat.add_assoc, bx_succ, ih, bx_succ]
    cases bx f m <;> cases bx (fun t => f (m + t)) n <;> cases f (m + n) <;> rfl

theorem bx_xor (f g : Nat → Bool) (n : Nat) :
    bx (fun t => f t ^^ g t) n = (bx f n ^^ bx g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bx_succ, ih, bx_succ, bx_succ]
    cases bx f n <;> cases bx g n <;> cases f n <;> cases g n <;> rfl

theorem bx_and (c : Bool) (f : Nat → Bool) (n : Nat) :
    bx (fun t => c && f t) n = (c && bx f n) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    rw [bx_succ, ih, bx_succ]
    cases c <;> cases bx f n <;> cases f n <;> rfl

/-- The inner sum of a carry-less product: one term `j = k - i` survives. -/
theorem bx_pair (i k : Nat) (x : Bool) (c : Nat → Bool) (n : Nat) :
    bx (fun j => decide (i + j = k) && x && c j) n = (decide (i ≤ k ∧ k - i < n) && x && c (k - i)) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    simp only [bx, ih]
    by_cases h : i + n = k
    · have h1 : k - i = n := by omega
      have h3 : i ≤ k ∧ k - i < n + 1 := by omega
      simp [h, h1, h3]
    · have h4 : (decide (i ≤ k ∧ k - i < n + 1)) = (decide (i ≤ k ∧ k - i < n)) := by
        apply decide_eq_decide.mpr; omega
      have h5 : decide (i + n = k) = false := by simp [h]
      rw [h5, h4]; simp

/-! ## The carry-less product -/

/-- The carry-less product of two `n`-coefficient operands, coefficient `k`: the XOR over `i + j = k`, `i, j < n`, of
`A i && B j`. -/
def cl (n : Nat) (A B : Nat → Bool) (k : Nat) : Bool :=
  bx (fun i => bx (fun j => decide (i + j = k) && A i && B j) n) n

theorem cl_congr {n : Nat} {A A' B B' : Nat → Bool} (hA : ∀ i, i < n → A i = A' i)
    (hB : ∀ j, j < n → B j = B' j) (k : Nat) : cl n A B k = cl n A' B' k := by
  unfold cl
  apply bx_congr
  intro i hi
  apply bx_congr
  intro j hj
  rw [hA i hi, hB j hj]

/-- Coefficients `k ≥ 2n - 1` of an `n`-coefficient product are `false`. -/
theorem cl_big {n : Nat} {A B : Nat → Bool} {k : Nat} (hk : 2 * n ≤ k + 1) : cl n A B k = false := by
  unfold cl
  apply bx_false
  intro i hi
  apply bx_false
  intro j hj
  have : ¬ (i + j = k) := by omega
  simp [this]

/-- A double sum shifted by `s`: only `k ≥ s` sees it, at `k - s`. -/
theorem cl_shift (n s k : Nat) (P Q : Nat → Bool) :
    bx (fun i => bx (fun j => decide (i + j + s = k) && P i && Q j) n) n =
      (decide (s ≤ k) && cl n P Q (k - s)) := by
  by_cases h : s ≤ k
  · have e : ∀ i j, decide (i + j + s = k) = decide (i + j = k - s) := by
      intro i j; apply decide_eq_decide.mpr; omega
    simp only [e, h, decide_true, Bool.true_and]
    rfl
  · have e : ∀ i j, decide (i + j + s = k) = false := by
      intro i j; simp; omega
    have h' : decide (s ≤ k) = false := by simp; omega
    simp only [e, h', Bool.false_and]
    apply bx_false; intro i hi; apply bx_false; intro j hj; rfl

/-- Operands that vanish from `N` on: the sums over `M ≥ N` positions see only the first `N`. -/
theorem cl_trunc {N M : Nat} (hNM : N ≤ M) {A B : Nat → Bool} (hA : ∀ i, N ≤ i → A i = false)
    (hB : ∀ j, N ≤ j → B j = false) (k : Nat) : cl M A B k = cl N A B k := by
  unfold cl
  have inner : ∀ i, bx (fun j => decide (i + j = k) && A i && B j) M =
      bx (fun j => decide (i + j = k) && A i && B j) N := by
    intro i
    apply bx_trunc hNM
    intro j hj _
    rw [hB j hj]; simp
  simp only [inner]
  apply bx_trunc hNM
  intro i hi _
  rw [bx_false]
  intro j hj
  rw [hA i hi]; simp

/-- The product of the half sums is the sum of the four half products. -/
theorem cl_sum (H : Nat) (X Y : Nat → Bool) (m : Nat) :
    cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) m =
      (cl H X Y m ^^ (cl H X (fun j => Y (H + j)) m ^^ (cl H (fun i => X (H + i)) Y m ^^
        cl H (fun i => X (H + i)) (fun j => Y (H + j)) m))) := by
  unfold cl
  have e : ∀ i j, (decide (i + j = m) && (X i ^^ X (H + i)) && (Y j ^^ Y (H + j))) =
      ((decide (i + j = m) && X i && Y j) ^^ ((decide (i + j = m) && X i && Y (H + j)) ^^
        ((decide (i + j = m) && X (H + i) && Y j) ^^ (decide (i + j = m) && X (H + i) && Y (H + j))))) := by
    intro i j
    cases decide (i + j = m) <;> cases X i <;> cases X (H + i) <;> cases Y j <;> cases Y (H + j) <;> rfl
  simp only [e, bx_xor]

/-! ## Karatsuba -/

/-- **One Karatsuba split** of a `2H`-coefficient carry-less product into its four half products. -/
theorem karatsuba (H : Nat) (X Y : Nat → Bool) (k : Nat) :
    cl (H + H) X Y k =
      (cl H X Y k ^^
        ((decide (H ≤ k) && cl H X (fun j => Y (H + j)) (k - H)) ^^
          ((decide (H ≤ k) && cl H (fun i => X (H + i)) Y (k - H)) ^^
            (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H)))))) := by
  have h1 : ∀ i, bx (fun j => decide (i + j = k) && X i && Y j) (H + H) =
      (bx (fun j => decide (i + j = k) && X i && Y j) H ^^
        bx (fun u => decide (i + (H + u) = k) && X i && Y (H + u)) H) := fun i => bx_add _ H H
  have hA01 : bx (fun i => bx (fun u => decide (i + (H + u) = k) && X i && Y (H + u)) H) H =
      (decide (H ≤ k) && cl H X (fun j => Y (H + j)) (k - H)) := by
    have e : ∀ i u, decide (i + (H + u) = k) = decide (i + u + H = k) := by
      intro i u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H H k X (fun j => Y (H + j))
  have hA10 : bx (fun t => bx (fun u => decide (H + t + u = k) && X (H + t) && Y u) H) H =
      (decide (H ≤ k) && cl H (fun i => X (H + i)) Y (k - H)) := by
    have e : ∀ t u, decide (H + t + u = k) = decide (t + u + H = k) := by
      intro t u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H H k (fun i => X (H + i)) Y
  have hA11 : bx (fun t => bx (fun u => decide (H + t + (H + u) = k) && X (H + t) && Y (H + u)) H) H =
      (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H))) := by
    have e : ∀ t u, decide (H + t + (H + u) = k) = decide (t + u + (H + H) = k) := by
      intro t u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H (H + H) k (fun i => X (H + i)) (fun j => Y (H + j))
  show bx (fun i => bx (fun j => decide (i + j = k) && X i && Y j) (H + H)) (H + H) = _
  rw [bx_add]
  simp only [h1, bx_xor]
  rw [hA01, hA10, hA11]
  have hL : cl H X Y k = bx (fun i => bx (fun j => decide (i + j = k) && X i && Y j) H) H := rfl
  rw [hL]
  simp only [Bool.xor_assoc]

/-- **One Karatsuba step**: the middle terms from the product of the half sums. -/
theorem karatsuba_full (H : Nat) (X Y : Nat → Bool) (k : Nat) :
    cl (H + H) X Y k =
      (cl H X Y k ^^
        ((decide (H ≤ k) && (cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (k - H) ^^
            cl H X Y (k - H) ^^ cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - H))) ^^
          (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H))))) := by
  rw [karatsuba, cl_sum]
  generalize cl H X Y k = l0
  generalize cl H X Y (k - H) = l1
  generalize cl H X (fun j => Y (H + j)) (k - H) = a
  generalize cl H (fun i => X (H + i)) Y (k - H) = b
  generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - H) = h1
  generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H)) = h2
  generalize decide (H ≤ k) = c1
  generalize decide (H + H ≤ k) = c2
  cases l0 <;> cases l1 <;> cases a <;> cases b <;> cases h1 <;> cases h2 <;> cases c1 <;> cases c2 <;> rfl

/-- **A Karatsuba node, column by column**: the low product `PL`, the high product `PH` and the middle product `PM` (of
the half sums), each `2H - 1` coefficients, combined into the `4H - 1` columns `PF` as
`PF = PL + x^H (PM + PL + PH) + x^2H PH`, give the `2H`-coefficient product. The column hypotheses are the shape a
netlist writes them in: columns `0 .. H-1` copy `PL`; columns `H .. 2H-2` add `PL` at the column and the three
products `H` below; column `2H - 1` adds the three products' top coefficients; columns `2H .. 3H-2` add `PH` `2H` below
and the three products `H` below; columns `3H-1 .. 4H-2` copy `PH`'s upper coefficients. -/
theorem karatsuba_cols {H : Nat} (hH : 1 ≤ H) {X Y : Nat → Bool} {PL PH PM PF : Nat → Bool}
    (hL : ∀ k, k < 2 * H - 1 → PL k = cl H X Y k)
    (hHh : ∀ k, k < 2 * H - 1 → PH k = cl H (fun i => X (H + i)) (fun j => Y (H + j)) k)
    (hM : ∀ k, k < 2 * H - 1 → PM k = cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) k)
    (c0 : ∀ i, i < H → PF i = PL i)
    (c1 : ∀ i, i + 1 < H → PF (H + i) = (PL (H + i) ^^ (PM i ^^ PL i ^^ PH i)))
    (c1' : PF (2 * H - 1) = (PM (H - 1) ^^ PL (H - 1) ^^ PH (H - 1)))
    (c2 : ∀ i, i + 1 < H → PF (2 * H + i) = (PH i ^^ (PM (H + i) ^^ PL (H + i) ^^ PH (H + i))))
    (c3 : ∀ i, i < H → PF (3 * H - 1 + i) = PH (H - 1 + i)) :
    ∀ k, k < 4 * H - 1 → PF k = cl (H + H) X Y k := by
  intro k hk
  rw [karatsuba_full]
  have big : ∀ (A B : Nat → Bool) m, 2 * H - 1 ≤ m → cl H A B m = false :=
    fun A B m hm => cl_big (by omega)
  by_cases h1 : k < H
  · have d1 : decide (H ≤ k) = false := by simp; omega
    have d2 : decide (H + H ≤ k) = false := by simp; omega
    rw [c0 k h1, hL k (by omega), d1, d2]; simp
  by_cases h2 : k < 2 * H - 1
  · obtain ⟨i, rfl⟩ : ∃ i, k = H + i := ⟨k - H, by omega⟩
    have d1 : decide (H ≤ H + i) = true := by simp
    have d2 : decide (H + H ≤ H + i) = false := by simp; omega
    have e1 : H + i - H = i := by omega
    rw [c1 i (by omega), hL (H + i) h2, hL i (by omega), hHh i (by omega), hM i (by omega), d1, d2, e1]
    simp
  by_cases h3 : k = 2 * H - 1
  · subst h3
    have d1 : decide (H ≤ 2 * H - 1) = true := by simp; omega
    have d2 : decide (H + H ≤ 2 * H - 1) = false := by simp; omega
    have e1 : 2 * H - 1 - H = H - 1 := by omega
    rw [c1', hM (H - 1) (by omega), hL (H - 1) (by omega), hHh (H - 1) (by omega), d1, d2, e1,
      big X Y (2 * H - 1) (by omega)]
    simp
  by_cases h4 : k < 3 * H - 1
  · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * H + i := ⟨k - 2 * H, by omega⟩
    have d1 : decide (H ≤ 2 * H + i) = true := by simp; omega
    have d2 : decide (H + H ≤ 2 * H + i) = true := by simp; omega
    have e1 : 2 * H + i - H = H + i := by omega
    have e2 : 2 * H + i - (H + H) = i := by omega
    rw [c2 i (by omega), hHh i (by omega), hM (H + i) (by omega), hL (H + i) (by omega),
      hHh (H + i) (by omega), d1, d2, e1, e2, big X Y (2 * H + i) (by omega)]
    simp only [Bool.true_and, Bool.false_xor]
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) i = a
    generalize cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (H + i) = m
    generalize cl H X Y (H + i) = l
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (H + i) = h
    cases a <;> cases m <;> cases l <;> cases h <;> rfl
  · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * H - 1 + i := ⟨k - (3 * H - 1), by omega⟩
    have d1 : decide (H ≤ 3 * H - 1 + i) = true := by simp; omega
    have d2 : decide (H + H ≤ 3 * H - 1 + i) = true := by simp; omega
    have e1 : 3 * H - 1 + i - H = 2 * H - 1 + i := by omega
    have e2 : 3 * H - 1 + i - (H + H) = H - 1 + i := by omega
    have bm : cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (2 * H - 1 + i) = false :=
      big _ _ _ (by omega)
    have bl : cl H X Y (2 * H - 1 + i) = false := big _ _ _ (by omega)
    have bh : cl H (fun i => X (H + i)) (fun j => Y (H + j)) (2 * H - 1 + i) = false := big _ _ _ (by omega)
    have bl0 : cl H X Y (3 * H - 1 + i) = false := big _ _ _ (by omega)
    rw [c3 i (by omega), hHh (H - 1 + i) (by omega), d1, d2, e1, e2, bm, bl, bh, bl0]
    simp

/-! ## The 4-coefficient base: a 4 x 4 product, coefficient by coefficient

Each coefficient as a balanced XOR tree of its partial products by ascending index of `A` (the shape a schoolbook base
writes). Each proof unfolds the sum (sixteen terms, all but the ones of `i + j = k` zero) and checks the remaining
identity of eight Boolean variables by `decide` (kernel evaluation of 256 cases; no axiom). -/

theorem cl_four_0 (A B : Nat → Bool) : cl 4 A B 0 = (A 0 && B 0) := by
  simp only [cl, bx]
  generalize A 0 = a0; generalize A 1 = a1; generalize A 2 = a2; generalize A 3 = a3
  generalize B 0 = b0; generalize B 1 = b1; generalize B 2 = b2; generalize B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3; decide

theorem cl_four_1 (A B : Nat → Bool) : cl 4 A B 1 = ((A 0 && B 1) ^^ (A 1 && B 0)) := by
  simp only [cl, bx]
  generalize A 0 = a0; generalize A 1 = a1; generalize A 2 = a2; generalize A 3 = a3
  generalize B 0 = b0; generalize B 1 = b1; generalize B 2 = b2; generalize B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3; decide

theorem cl_four_2 (A B : Nat → Bool) :
    cl 4 A B 2 = (((A 0 && B 2) ^^ (A 1 && B 1)) ^^ (A 2 && B 0)) := by
  simp only [cl, bx]
  generalize A 0 = a0; generalize A 1 = a1; generalize A 2 = a2; generalize A 3 = a3
  generalize B 0 = b0; generalize B 1 = b1; generalize B 2 = b2; generalize B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3; decide

theorem cl_four_3 (A B : Nat → Bool) :
    cl 4 A B 3 = (((A 0 && B 3) ^^ (A 1 && B 2)) ^^ ((A 2 && B 1) ^^ (A 3 && B 0))) := by
  simp only [cl, bx]
  generalize A 0 = a0; generalize A 1 = a1; generalize A 2 = a2; generalize A 3 = a3
  generalize B 0 = b0; generalize B 1 = b1; generalize B 2 = b2; generalize B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3; decide

theorem cl_four_4 (A B : Nat → Bool) :
    cl 4 A B 4 = (((A 1 && B 3) ^^ (A 2 && B 2)) ^^ (A 3 && B 1)) := by
  simp only [cl, bx]
  generalize A 0 = a0; generalize A 1 = a1; generalize A 2 = a2; generalize A 3 = a3
  generalize B 0 = b0; generalize B 1 = b1; generalize B 2 = b2; generalize B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3; decide

theorem cl_four_5 (A B : Nat → Bool) : cl 4 A B 5 = ((A 2 && B 3) ^^ (A 3 && B 2)) := by
  simp only [cl, bx]
  generalize A 0 = a0; generalize A 1 = a1; generalize A 2 = a2; generalize A 3 = a3
  generalize B 0 = b0; generalize B 1 = b1; generalize B 2 = b2; generalize B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3; decide

theorem cl_four_6 (A B : Nat → Bool) : cl 4 A B 6 = (A 3 && B 3) := by
  simp only [cl, bx]
  generalize A 0 = a0; generalize A 1 = a1; generalize A 2 = a2; generalize A 3 = a3
  generalize B 0 = b0; generalize B 1 = b1; generalize B 2 = b2; generalize B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3; decide

end LeanModels.Sv.CombClmul

#pin_axioms LeanModels.Sv.CombClmul.bx_congr LeanModels.Sv.CombClmul.bx_trunc LeanModels.Sv.CombClmul.bx_false
  LeanModels.Sv.CombClmul.bx_add LeanModels.Sv.CombClmul.bx_xor LeanModels.Sv.CombClmul.bx_and
  LeanModels.Sv.CombClmul.bx_pair LeanModels.Sv.CombClmul.cl_congr LeanModels.Sv.CombClmul.cl_big
  LeanModels.Sv.CombClmul.cl_shift LeanModels.Sv.CombClmul.cl_trunc LeanModels.Sv.CombClmul.cl_sum
  LeanModels.Sv.CombClmul.karatsuba LeanModels.Sv.CombClmul.karatsuba_full LeanModels.Sv.CombClmul.karatsuba_cols
  LeanModels.Sv.CombClmul.cl_four_0 LeanModels.Sv.CombClmul.cl_four_1
  LeanModels.Sv.CombClmul.cl_four_2 LeanModels.Sv.CombClmul.cl_four_3 LeanModels.Sv.CombClmul.cl_four_4
  LeanModels.Sv.CombClmul.cl_four_5 LeanModels.Sv.CombClmul.cl_four_6
