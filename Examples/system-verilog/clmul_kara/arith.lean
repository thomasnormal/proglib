import LeanModels.Sv.CombClmul
import Examples.«system-verilog».clmul_kara.statement

/-!
# The mathematics of the Karatsuba record (`clmul_kara`): plain `Bool`/`Nat`, no ls-sv

The record's rows as functions of a row index and a column: `av l j`, `bv l j` (the operands of level `l`, node `t` in
columns `t·W l .. t·W l + W l - 1`) and `rv l j` (the products, node `t` in the slot of `2·W l` columns from
`2·(t·W l)`), where `W L l = 4·2^L / 2^l` is the record's slot width `P >> l`. `View` is what the netlist's equations
say of them, one field per assign (the split of a node into its three children, the 4 x 4 base, the five column groups
of a combine), at `Nat` indices; `view_node` is the recursion: by induction from the base level `L` up, node `t` of
level `l` holds the carry-less product of its operands (`CombClmul.cl`), the base by the 4 x 4 coefficients
(`cl_four_*`) and each combine by one Karatsuba step (`karatsuba_cols`). `view_out` reads the product of level 0 off
the zero-padded operands (`cl_trunc`), and `coeff_eq` is the task's double sum as the same product.

The generic lemmas (XOR sums, the product, Karatsuba, the base) are the library's (`LeanModels/Sv/CombClmul.lean`);
what is here is the record's own layout.
-/

namespace Examples.«system-verilog».clmul_kara.arith

open LeanModels.Sv.XorSum LeanModels.Sv.CombClmul

/-! ## The slot widths -/

/-- The slot width of level `l`: the record's `P >> l`, `P = 4·2^L`. -/
def W (L l : Nat) : Nat := 4 * 2 ^ L / 2 ^ l

theorem W_eq {L l : Nat} (h : l ≤ L + 2) : W L l = 2 ^ (L + 2 - l) := by
  unfold W
  have e : 4 * 2 ^ L = 2 ^ (L + 2) := by rw [Nat.pow_add, Nat.mul_comm]
  rw [e, Nat.pow_div h (by decide)]

theorem W_succ {L l : Nat} (h : l < L + 2) : W L l = W L (l + 1) + W L (l + 1) := by
  rw [W_eq (by omega), W_eq (by omega)]
  have e : L + 2 - l = (L + 2 - (l + 1)) + 1 := by omega
  rw [e, Nat.pow_succ]
  omega

theorem W_L (L : Nat) : W L L = 4 := by
  rw [W_eq (by omega)]
  have e : L + 2 - L = 2 := by omega
  rw [e]

theorem W_pos {L l : Nat} (h : l ≤ L + 2) : 1 ≤ W L l := by
  rw [W_eq h]; exact Nat.one_le_two_pow

/-! ## The rows' equations -/

/-- The netlist's equations over the rows, at `Nat` indices (one field per assign of the record). -/
structure View (L : Nat) (av bv rv : Nat → Nat → Bool) : Prop where
  /-- child `3t` of node `t` of level `l < L`: the low half of its operands -/
  split0a : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ i, i < W L (l + 1) →
    av (l + 1) (3 * (t * W L (l + 1)) + i) = av l (t * W L l + i)
  split0b : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ i, i < W L (l + 1) →
    bv (l + 1) (3 * (t * W L (l + 1)) + i) = bv l (t * W L l + i)
  /-- child `3t + 1`: the high half -/
  split1a : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ i, i < W L (l + 1) →
    av (l + 1) (3 * (t * W L (l + 1)) + W L (l + 1) + i) = av l (t * W L l + W L (l + 1) + i)
  split1b : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ i, i < W L (l + 1) →
    bv (l + 1) (3 * (t * W L (l + 1)) + W L (l + 1) + i) = bv l (t * W L l + W L (l + 1) + i)
  /-- child `3t + 2`: the XOR of the halves -/
  split2a : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ i, i < W L (l + 1) →
    av (l + 1) (3 * (t * W L (l + 1)) + 2 * W L (l + 1) + i) =
      (av l (t * W L l + i) ^^ av l (t * W L l + W L (l + 1) + i))
  split2b : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ i, i < W L (l + 1) →
    bv (l + 1) (3 * (t * W L (l + 1)) + 2 * W L (l + 1) + i) =
      (bv l (t * W L l + i) ^^ bv l (t * W L l + W L (l + 1) + i))
  /-- the base level: a 4 x 4 product per node, column by column -/
  base0 : ∀ t, t < 3 ^ L → rv L (8 * t) = (av L (4 * t) && bv L (4 * t))
  base1 : ∀ t, t < 3 ^ L →
    rv L (8 * t + 1) = ((av L (4 * t) && bv L (4 * t + 1)) ^^ (av L (4 * t + 1) && bv L (4 * t)))
  base2 : ∀ t, t < 3 ^ L →
    rv L (8 * t + 2) = (((av L (4 * t) && bv L (4 * t + 2)) ^^ (av L (4 * t + 1) && bv L (4 * t + 1))) ^^
      (av L (4 * t + 2) && bv L (4 * t)))
  base3 : ∀ t, t < 3 ^ L →
    rv L (8 * t + 3) = (((av L (4 * t) && bv L (4 * t + 3)) ^^ (av L (4 * t + 1) && bv L (4 * t + 2))) ^^
      ((av L (4 * t + 2) && bv L (4 * t + 1)) ^^ (av L (4 * t + 3) && bv L (4 * t))))
  base4 : ∀ t, t < 3 ^ L →
    rv L (8 * t + 4) = (((av L (4 * t + 1) && bv L (4 * t + 3)) ^^ (av L (4 * t + 2) && bv L (4 * t + 2))) ^^
      (av L (4 * t + 3) && bv L (4 * t + 1)))
  base5 : ∀ t, t < 3 ^ L →
    rv L (8 * t + 5) = ((av L (4 * t + 2) && bv L (4 * t + 3)) ^^ (av L (4 * t + 3) && bv L (4 * t + 2)))
  base6 : ∀ t, t < 3 ^ L → rv L (8 * t + 6) = (av L (4 * t + 3) && bv L (4 * t + 3))
  /-- a combine, columns `0 .. m-1` (`m = W L (l + 1)`): the low product -/
  comb0 : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ k, k < W L (l + 1) →
    rv l (2 * (t * W L l) + k) = rv (l + 1) (3 * (t * W L l) + k)
  /-- columns `m .. 2m-2` -/
  comb1 : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ k, k + 1 < W L (l + 1) →
    rv l (2 * (t * W L l) + W L (l + 1) + k) =
      ((rv (l + 1) (3 * (t * W L l) + k) ^^ rv (l + 1) (3 * (t * W L l) + W L (l + 1) + k)) ^^
        (rv (l + 1) (3 * (t * W L l) + W L l + k) ^^ rv (l + 1) (3 * (t * W L l) + 2 * W L l + k)))
  /-- column `2m - 1` -/
  comb2 : ∀ l, l < L → ∀ t, t < 3 ^ l →
    rv l (2 * (t * W L l) + W L l - 1) =
      ((rv (l + 1) (3 * (t * W L l) + W L (l + 1) - 1) ^^ rv (l + 1) (3 * (t * W L l) + W L l + W L (l + 1) - 1)) ^^
        rv (l + 1) (3 * (t * W L l) + 2 * W L l + W L (l + 1) - 1))
  /-- columns `2m .. 3m-2` -/
  comb3 : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ k, k + 1 < W L (l + 1) →
    rv l (2 * (t * W L l) + W L l + k) =
      ((rv (l + 1) (3 * (t * W L l) + W L (l + 1) + k) ^^ rv (l + 1) (3 * (t * W L l) + W L l + k)) ^^
        (rv (l + 1) (3 * (t * W L l) + W L l + W L (l + 1) + k) ^^
          rv (l + 1) (3 * (t * W L l) + 2 * W L l + W L (l + 1) + k)))
  /-- columns `3m-1 .. 4m-2`: the high product's upper half -/
  comb4 : ∀ l, l < L → ∀ t, t < 3 ^ l → ∀ k, k < W L (l + 1) →
    rv l (2 * (t * W L l) + W L l + W L (l + 1) - 1 + k) =
      rv (l + 1) (3 * (t * W L l) + W L l + W L (l + 1) - 1 + k)

/-! ## The recursion -/

/-- A function of an index at two equal indices. -/
theorem idx {f : Nat → Bool} {a b : Nat} (h : a = b) : f a = f b := h ▸ rfl

/-- The product of node `t` of level `l`, from its operands' rows. -/
def NodeOk (L : Nat) (av bv rv : Nat → Nat → Bool) (l : Nat) : Prop :=
  ∀ t, t < 3 ^ l → ∀ k, k < 2 * W L l - 1 →
    rv l (2 * (t * W L l) + k) = cl (W L l) (fun i => av l (t * W L l + i)) (fun j => bv l (t * W L l + j)) k

/-- The base level: each node's 4 x 4 product. -/
theorem nodeOk_base {L : Nat} {av bv rv : Nat → Nat → Bool} (hv : View L av bv rv) : NodeOk L av bv rv L := by
  intro t ht k hk
  rw [W_L] at hk ⊢
  have e8 : ∀ m, 2 * (t * 4) + m = 8 * t + m := fun m => by omega
  have e4 : ∀ m, t * 4 + m = 4 * t + m := fun m => by omega
  rw [e8]
  simp only [e4]
  have hk7 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Nat.add_zero, cl_four_0]; rw [hv.base0 t ht]
  · simp only [Nat.add_zero, cl_four_1]; rw [hv.base1 t ht]
  · simp only [Nat.add_zero, cl_four_2]; rw [hv.base2 t ht]
  · simp only [Nat.add_zero, cl_four_3]; rw [hv.base3 t ht]
  · simp only [cl_four_4]; rw [hv.base4 t ht]
  · simp only [cl_four_5]; rw [hv.base5 t ht]
  · simp only [cl_four_6]; rw [hv.base6 t ht]

/-- A combine: node `t` of level `l < L` from its three children at level `l + 1` (one Karatsuba step). -/
theorem nodeOk_step {L l : Nat} {av bv rv : Nat → Nat → Bool} (hv : View L av bv rv) (hl : l < L)
    (ih : NodeOk L av bv rv (l + 1)) : NodeOk L av bv rv l := by
  intro t ht k hk
  have hW := W_succ (L := L) (l := l) (by omega)
  have hH1 := W_pos (L := L) (l := l + 1) (by omega)
  generalize hHdef : W L (l + 1) = H at hW hH1
  generalize hWdef : W L l = Wl at hW hk ⊢
  -- the products of the slot widths with the node indices, as `omega` atoms
  have m1 : t * Wl = t * H + t * H := by rw [hW, Nat.mul_add]
  have m30 : (3 * t) * H = 3 * (t * H) := Nat.mul_assoc 3 t H
  have m31 : (3 * t + 1) * H = 3 * (t * H) + H := by rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  have m32 : (3 * t + 2) * H = 3 * (t * H) + 2 * H := by rw [Nat.add_mul, Nat.mul_assoc]
  have h3 : 3 ^ (l + 1) = 3 * 3 ^ l := by rw [Nat.pow_succ, Nat.mul_comm]
  have ih0 := ih (3 * t) (by omega)
  have ih1 := ih (3 * t + 1) (by omega)
  have ih2 := ih (3 * t + 2) (by omega)
  rw [hHdef] at ih0 ih1 ih2
  -- the node's operands
  let X := fun i => av l (t * Wl + i)
  let Y := fun j => bv l (t * Wl + j)
  have key := karatsuba_cols (H := H) hH1 (X := X) (Y := Y)
    (PL := fun k => rv (l + 1) (3 * (t * Wl) + k)) (PH := fun k => rv (l + 1) (3 * (t * Wl) + Wl + k))
    (PM := fun k => rv (l + 1) (3 * (t * Wl) + 2 * Wl + k)) (PF := fun k => rv l (2 * (t * Wl) + k))
    (fun k hk => by
      show rv (l + 1) (3 * (t * Wl) + k) = cl H X Y k
      rw [idx (f := rv (l + 1)) (show 3 * (t * Wl) + k = 2 * (3 * t * H) + k by omega), ih0 k (by omega)]
      apply cl_congr
      · intro i hi
        show av (l + 1) (3 * t * H + i) = av l (t * Wl + i)
        rw [idx (f := av (l + 1)) (show 3 * t * H + i = 3 * (t * W L (l + 1)) + i by rw [hHdef]; omega),
          hv.split0a l hl t ht i (by rw [hHdef]; exact hi), hWdef]
      · intro j hj
        show bv (l + 1) (3 * t * H + j) = bv l (t * Wl + j)
        rw [idx (f := bv (l + 1)) (show 3 * t * H + j = 3 * (t * W L (l + 1)) + j by rw [hHdef]; omega),
          hv.split0b l hl t ht j (by rw [hHdef]; exact hj), hWdef])
    (fun k hk => by
      show rv (l + 1) (3 * (t * Wl) + Wl + k) = cl H (fun i => X (H + i)) (fun j => Y (H + j)) k
      rw [idx (f := rv (l + 1)) (show 3 * (t * Wl) + Wl + k = 2 * ((3 * t + 1) * H) + k by omega), ih1 k (by omega)]
      apply cl_congr
      · intro i hi
        show av (l + 1) ((3 * t + 1) * H + i) = av l (t * Wl + (H + i))
        rw [idx (f := av (l + 1)) (show (3 * t + 1) * H + i = 3 * (t * W L (l + 1)) + W L (l + 1) + i by
            rw [hHdef]; omega),
          hv.split1a l hl t ht i (by rw [hHdef]; exact hi), hWdef, hHdef, Nat.add_assoc]
      · intro j hj
        show bv (l + 1) ((3 * t + 1) * H + j) = bv l (t * Wl + (H + j))
        rw [idx (f := bv (l + 1)) (show (3 * t + 1) * H + j = 3 * (t * W L (l + 1)) + W L (l + 1) + j by
            rw [hHdef]; omega),
          hv.split1b l hl t ht j (by rw [hHdef]; exact hj), hWdef, hHdef, Nat.add_assoc])
    (fun k hk => by
      show rv (l + 1) (3 * (t * Wl) + 2 * Wl + k) =
        cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) k
      rw [idx (f := rv (l + 1)) (show 3 * (t * Wl) + 2 * Wl + k = 2 * ((3 * t + 2) * H) + k by omega),
        ih2 k (by omega)]
      apply cl_congr
      · intro i hi
        show av (l + 1) ((3 * t + 2) * H + i) = (av l (t * Wl + i) ^^ av l (t * Wl + (H + i)))
        rw [idx (f := av (l + 1)) (show (3 * t + 2) * H + i = 3 * (t * W L (l + 1)) + 2 * W L (l + 1) + i by
            rw [hHdef]; omega),
          hv.split2a l hl t ht i (by rw [hHdef]; exact hi), hWdef, hHdef, Nat.add_assoc]
      · intro j hj
        show bv (l + 1) ((3 * t + 2) * H + j) = (bv l (t * Wl + j) ^^ bv l (t * Wl + (H + j)))
        rw [idx (f := bv (l + 1)) (show (3 * t + 2) * H + j = 3 * (t * W L (l + 1)) + 2 * W L (l + 1) + j by
            rw [hHdef]; omega),
          hv.split2b l hl t ht j (by rw [hHdef]; exact hj), hWdef, hHdef, Nat.add_assoc])
    (fun i hi => by
      show rv l (2 * (t * Wl) + i) = rv (l + 1) (3 * (t * Wl) + i)
      have h := hv.comb0 l hl t ht i (by rw [hHdef]; exact hi)
      rw [hWdef] at h
      exact h)
    (fun i hi => by
      show rv l (2 * (t * Wl) + (H + i)) =
        (rv (l + 1) (3 * (t * Wl) + (H + i)) ^^
          (rv (l + 1) (3 * (t * Wl) + 2 * Wl + i) ^^ rv (l + 1) (3 * (t * Wl) + i) ^^ rv (l + 1) (3 * (t * Wl) + Wl + i)))
      have h := hv.comb1 l hl t ht i (by rw [hHdef]; exact hi)
      rw [hWdef, hHdef] at h
      rw [idx (f := rv l) (show 2 * (t * Wl) + (H + i) = 2 * (t * Wl) + H + i by omega), h,
        idx (f := rv (l + 1)) (show 3 * (t * Wl) + H + i = 3 * (t * Wl) + (H + i) by omega)]
      generalize rv (l + 1) (3 * (t * Wl) + i) = a
      generalize rv (l + 1) (3 * (t * Wl) + (H + i)) = b
      generalize rv (l + 1) (3 * (t * Wl) + Wl + i) = c
      generalize rv (l + 1) (3 * (t * Wl) + 2 * Wl + i) = d
      revert a b c d; decide)
    (by
      show rv l (2 * (t * Wl) + (2 * H - 1)) =
        (rv (l + 1) (3 * (t * Wl) + 2 * Wl + (H - 1)) ^^ rv (l + 1) (3 * (t * Wl) + (H - 1)) ^^
          rv (l + 1) (3 * (t * Wl) + Wl + (H - 1)))
      have h := hv.comb2 l hl t ht
      rw [hWdef, hHdef] at h
      rw [idx (f := rv l) (show 2 * (t * Wl) + (2 * H - 1) = 2 * (t * Wl) + Wl - 1 by omega), h,
        idx (f := rv (l + 1)) (show 3 * (t * Wl) + H - 1 = 3 * (t * Wl) + (H - 1) by omega),
        idx (f := rv (l + 1)) (show 3 * (t * Wl) + Wl + H - 1 = 3 * (t * Wl) + Wl + (H - 1) by omega),
        idx (f := rv (l + 1)) (show 3 * (t * Wl) + 2 * Wl + H - 1 = 3 * (t * Wl) + 2 * Wl + (H - 1) by omega)]
      generalize rv (l + 1) (3 * (t * Wl) + (H - 1)) = a
      generalize rv (l + 1) (3 * (t * Wl) + Wl + (H - 1)) = c
      generalize rv (l + 1) (3 * (t * Wl) + 2 * Wl + (H - 1)) = d
      revert a c d; decide)
    (fun i hi => by
      show rv l (2 * (t * Wl) + (2 * H + i)) =
        (rv (l + 1) (3 * (t * Wl) + Wl + i) ^^
          (rv (l + 1) (3 * (t * Wl) + 2 * Wl + (H + i)) ^^ rv (l + 1) (3 * (t * Wl) + (H + i)) ^^
            rv (l + 1) (3 * (t * Wl) + Wl + (H + i))))
      have h := hv.comb3 l hl t ht i (by rw [hHdef]; exact hi)
      rw [hWdef, hHdef] at h
      rw [idx (f := rv l) (show 2 * (t * Wl) + (2 * H + i) = 2 * (t * Wl) + Wl + i by omega), h,
        idx (f := rv (l + 1)) (show 3 * (t * Wl) + H + i = 3 * (t * Wl) + (H + i) by omega),
        idx (f := rv (l + 1)) (show 3 * (t * Wl) + Wl + H + i = 3 * (t * Wl) + Wl + (H + i) by omega),
        idx (f := rv (l + 1)) (show 3 * (t * Wl) + 2 * Wl + H + i = 3 * (t * Wl) + 2 * Wl + (H + i) by omega)]
      generalize rv (l + 1) (3 * (t * Wl) + (H + i)) = a
      generalize rv (l + 1) (3 * (t * Wl) + Wl + i) = b
      generalize rv (l + 1) (3 * (t * Wl) + Wl + (H + i)) = c
      generalize rv (l + 1) (3 * (t * Wl) + 2 * Wl + (H + i)) = d
      revert a b c d; decide)
    (fun i hi => by
      show rv l (2 * (t * Wl) + (3 * H - 1 + i)) = rv (l + 1) (3 * (t * Wl) + Wl + (H - 1 + i))
      have h := hv.comb4 l hl t ht i (by rw [hHdef]; exact hi)
      rw [hWdef, hHdef] at h
      rw [idx (f := rv l) (show 2 * (t * Wl) + (3 * H - 1 + i) = 2 * (t * Wl) + Wl + H - 1 + i by omega), h]
      exact idx (by omega))
  have hk' : k < 4 * H - 1 := by omega
  rw [key k hk']
  exact congrArg (fun n => cl n X Y k) hW.symm

/-- **Every node of every level holds its carry-less product**, by induction from the base level up. -/
theorem nodeOk_all {L : Nat} {av bv rv : Nat → Nat → Bool} (hv : View L av bv rv) :
    ∀ d l, l + d = L → NodeOk L av bv rv l := by
  intro d
  induction d with
  | zero => intro l hl; obtain rfl : l = L := by omega
            exact nodeOk_base hv
  | succ d ih => intro l hl; exact nodeOk_step hv (by omega) (ih (l + 1) (by omega))

/-- **The output**: where level 0 holds the zero-padded operands `x`, `y` (`N ≤ P` coefficients) and the output bits
are the low `2N - 1` columns of its product, they are the carry-less product of `x` and `y`. -/
theorem view_out {L N : Nat} {av bv rv : Nat → Nat → Bool} {x y p : Nat → Bool} (hv : View L av bv rv)
    (hNP : N ≤ W L 0) (ha : ∀ j, j < W L 0 → av 0 j = (decide (j < N) && x j))
    (hb : ∀ j, j < W L 0 → bv 0 j = (decide (j < N) && y j)) (hp : ∀ k, k < 2 * N - 1 → p k = rv 0 k) :
    ∀ k, k < 2 * N - 1 → p k = cl N x y k := by
  intro k hk
  have h0 := nodeOk_all hv L 0 (by omega) 0 (by simp) k (by omega)
  simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add] at h0
  rw [hp k hk, h0, cl_congr (A' := fun i => decide (i < N) && x i) (B' := fun j => decide (j < N) && y j) ha hb,
    cl_trunc hNP (fun i hi => by have : ¬ i < N := by omega
                                 simp [this])
      (fun j hj => by have : ¬ j < N := by omega
                      simp [this])]
  apply cl_congr
  · intro i hi; simp [hi]
  · intro j hj; simp [hj]

/-- The task's double sum is the carry-less product of the operands' bits. -/
theorem coeff_eq (N : Nat) (a b : BitVec N) (k : Nat) :
    statement.coeff N a b k = cl N a.getLsbD b.getLsbD k := by
  unfold statement.coeff cl
  simp only [foldl_xor]
  simp

theorem getLsbD_ofBits : ∀ (n : Nat) (f : Nat → Bool) (k : Nat),
    (statement.ofBits n f).getLsbD k = (decide (k < n) && f k)
  | 0, f, k => by simp [statement.ofBits]
  | n + 1, f, k => by
    rw [statement.ofBits, BitVec.getLsbD_append, getLsbD_ofBits n]
    cases k with
    | zero => simp
    | succ k => simp

end Examples.«system-verilog».clmul_kara.arith
