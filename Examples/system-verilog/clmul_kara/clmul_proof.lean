import Examples.«system-verilog».clmul_kara.gen
import Examples.«system-verilog».clmul_kara.statement
import Examples.«system-verilog».clmul_kara.arith
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombTask
import LeanModels.Sv.CombTaskTactic

/-!
# The Karatsuba record meets the carry-less multiplier statement, for every `N` in its range

`clmul_kara_clmul : ClmulStatement clmul_kara.sem` (`statement.lean`: the svGolf `clmul` task's statement over ls-sv at
the record's range `1 ≤ N < 2^16`): for every `N` in range, the ports, no clocked process, no combinational loop,
termination, and in every cycle whose stimulus drives `a`, `b` with known values, `p` holds the coefficients of the
product of the two polynomials over GF(2) that `a` and `b` encode. From

* `sv_structure`: `CombDesign` with the shared obligations, then `Acyclic` (operands down the levels, the base, products
  up the levels, the output last), each in a theorem of its own; the structural obligations close with the slot-width
  facts of the record's layout (`kara_facts`: `P >> l = 4·2^L / 2^l` halves from one level to the next, the products of
  a node index with a slot width), the player's closer;
* `sv_interface`: the ports;
* `CombTask.of_comb` and `sv_inputs`: the generic conjuncts, the stimulus form, the input ports' bits;
* `sv_equations`: the settled-state equations of the netlist over `Bool`, and the knownness of every driven bit;
  `sv_eq_nat` states them at `Nat` indices; their 27 obligations close by `sv_obligations` (the slot-window rule of
  `sv_cover` for the 16 coverage goals);
* the record's equations as the rows' `arith.View` (one field per assign: each is the equation `sv_equations` derived,
  its indices rewritten by `omega`, `kara_idx`), and the mathematics (`arith.lean`): by induction from the base level
  up, every node holds the carry-less product of its operands (the 4 x 4 base, one Karatsuba step per combine,
  `LeanModels/Sv/CombClmul.lean`), so level 0 holds the product of the zero-padded inputs, whose low `2N - 1` columns
  are the task's `coeff`; `SvState.port_ofBitVec` assembles the port.

No `sorry`, `native_decide` or `bv_decide`; the axioms are pinned at the end.

Build: `lake build Examples.«system-verilog».clmul_kara.clmul_proof`.
-/

open Lean Elab Tactic Meta
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».clmul_kara.gen Examples.«system-verilog».clmul_kara.statement

namespace Examples.«system-verilog».clmul_kara.clmul_proof

/-! ## 1. The slot-width facts of the record's layout (the structural closer) -/

/-- `4 · 2^L / 2^k = 2^(L + 2 - k)` for `k ≤ L + 2` (an exact division of powers of two). -/
theorem kq_div (L k : Nat) (hk : k ≤ L + 2) : (4 * 2 ^ L : Int) / 2 ^ k = ((2 ^ (L + 2 - k) : Nat) : Int) := by
  have e1 : (4 * 2 ^ L : Int) = ((2 ^ (L + 2) : Nat) : Int) := by
    rw [Nat.pow_add]; simp only [Nat.reducePow, Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]; omega
  have e2 : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by simp
  rw [e1, e2, ← Int.natCast_ediv, Nat.pow_div hk (by decide)]

/-- The slot width of a level is twice the next level's. -/
theorem kq_half (L : Nat) (x : Int) (h0 : 0 ≤ x) (h1 : x < L) :
    (4 * 2 ^ L : Int) / 2 ^ x.toNat = 2 * ((4 * 2 ^ L : Int) / 2 ^ (x + 1).toNat) := by
  have ht : (x + 1).toNat = x.toNat + 1 := by omega
  rw [kq_div L x.toNat (by omega), ht, kq_div L (x.toNat + 1) (by omega)]
  have e : L + 2 - x.toNat = (L + 2 - (x.toNat + 1)) + 1 := by omega
  rw [e, Nat.pow_succ]
  simp only [Int.natCast_mul, Int.cast_ofNat_Int]
  omega

/-- The next level's slot width is at least 4. -/
theorem kq_pos (L : Nat) (x : Int) (h0 : 0 ≤ x) (h1 : x < L) : 4 ≤ (4 * 2 ^ L : Int) / 2 ^ (x + 1).toNat := by
  rw [kq_div L (x + 1).toNat (by omega)]
  have e : L + 2 - (x + 1).toNat = (L - (x + 1).toNat) + 2 := by omega
  rw [e, Nat.pow_add]
  have h := Nat.one_le_two_pow (n := L - (x + 1).toNat)
  simp only [Nat.reducePow, Int.natCast_mul, Int.cast_ofNat_Int]
  have : (1 : Int) ≤ ((2 ^ (L - (x + 1).toNat) : Nat) : Int) := by exact_mod_cast h
  omega

/-- `3^(k+1) · 2^(L+1-k) ≤ 4 · 3^L` for `k < L` (the node count of a level times the next level's slot width). -/
theorem kq_m_nat (L k : Nat) (hk : k < L) : 3 * (3 ^ k * 2 ^ (L + 1 - k)) ≤ 4 * 3 ^ L := by
  obtain ⟨m, rfl⟩ : ∃ m, L = k + 1 + m := ⟨L - k - 1, by omega⟩
  have e1 : k + 1 + m + 1 - k = m + 2 := by omega
  rw [e1, Nat.pow_add 2 m 2, Nat.pow_add 3 (k + 1) m, Nat.pow_succ 3 k]
  have h : 3 ^ k * 2 ^ m ≤ 3 ^ k * 3 ^ m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) m)
  have e2 : 3 * (3 ^ k * (2 ^ m * 2 ^ 2)) = 12 * (3 ^ k * 2 ^ m) := by
    rw [Nat.mul_comm (2 ^ m) (2 ^ 2), ← Nat.mul_assoc (3 ^ k), Nat.mul_comm (3 ^ k) (2 ^ 2), Nat.mul_assoc,
      ← Nat.mul_assoc 3]
  have e3 : 4 * (3 ^ k * 3 * 3 ^ m) = 12 * (3 ^ k * 3 ^ m) := by
    rw [Nat.mul_comm (3 ^ k) 3, Nat.mul_assoc 3, ← Nat.mul_assoc 4]
  rw [e2, e3]
  omega

theorem kq_m (L : Nat) (x : Int) (h0 : 0 ≤ x) (h1 : x < L) :
    3 * (3 ^ x.toNat * ((4 * 2 ^ L : Int) / 2 ^ (x + 1).toNat)) ≤ 4 * 3 ^ L := by
  rw [kq_div L (x + 1).toNat (by omega)]
  have e : L + 2 - (x + 1).toNat = L + 1 - x.toNat := by omega
  rw [e]
  have h := kq_m_nat L x.toNat (by omega)
  have : ((3 * (3 ^ x.toNat * 2 ^ (L + 1 - x.toNat)) : Nat) : Int) ≤ ((4 * 3 ^ L : Nat) : Int) := by exact_mod_cast h
  simpa only [Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int] using this

/-- A factor below `B` gives the product one `y` below `B · y`. -/
theorem mul_add_le (g B y : Int) (hg : g < B) (hy : 0 ≤ y) : g * y + y ≤ B * y := by
  have h := Int.mul_le_mul_of_nonneg_right (show g + 1 ≤ B by omega) hy
  rw [Int.add_mul, Int.one_mul] at h
  exact h

/-- A product with the level's slot width is twice the product with the next level's. -/
theorem mul_half (L : Nat) (x g : Int) (h0 : 0 ≤ x) (h1 : x < L) :
    g * ((4 * 2 ^ L : Int) / 2 ^ x.toNat) = 2 * (g * ((4 * 2 ^ L : Int) / 2 ^ (x + 1).toNat)) := by
  rw [kq_half L x h0 h1, Int.mul_left_comm]

/-- The subterms of `e` (closed, no loose bound variables). -/
partial def subterms (e : Lean.Expr) : Array Lean.Expr :=
  let sub := match e with
    | .app f a => subterms f ++ subterms a
    | .mdata _ b | .proj _ _ b => subterms b
    | _ => #[]
  if e.hasLooseBVars then sub else sub.push e

/-- The level variable `x` of an exponent `x.toNat` or `(x + 1).toNat` (`some (x, 0)` / `some (x, 1)`). -/
def expVar? (t : Lean.Expr) : Option (Lean.Expr × Nat) :=
  if t.isAppOfArity ``Int.toNat 1 then
    let a := t.appArg!
    if a.isFVar then some (a, 0)
    else if a.isAppOfArity ``HAdd.hAdd 6 && (a.getArg! 4).isFVar && (a.getArg! 5).int? == some 1 then
      some (a.getArg! 4, 1)
    else none
  else none

/-- **The slot-width facts of a structural goal** (the player's closer): for every level variable `x` of the goal
(`0 ≤ x < L`), the halving of the slot width (`kq_half`), its lower bound (`kq_pos`) and the node count times the next
width (`kq_m`); for every product `t · (P >> e)` of a node index and a slot width, the bounds `t · Q + Q ≤ 3^x · Q`,
`0 ≤ t · Q` and the halving of the product (`mul_half`); for two such products, their order and congruence. -/
elab "kara_facts" : tactic => withMainContext do
  let g ← getMainGoal
  let mut es : Array Lean.Expr := #[← instantiateMVars (← g.getType)]
  for d in ← getLCtx do
    unless d.isImplementationDetail do es := es.push (← instantiateMVars d.type)
  let subs := es.flatMap subterms
  -- `L`: the `clog2` atom
  let some L := subs.find? (fun e => e.isAppOfArity ``LeanModels.Sv.clog2 1) | return
  let Lint ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, L]
  -- the level variables (exponents of the quotients' powers of two)
  let mut xs : Array Lean.Expr := #[]
  for e in subs do
    if e.isAppOfArity ``HPow.hPow 6 then
      if let some (x, _) := expVar? (e.getArg! 5) then
        unless xs.contains x do xs := xs.push x
  let mut ok : Array (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := #[]
  for x in xs do
    let some h0 ← omegaProves (← mkAppM ``LE.le #[toExpr (0 : Int), x]) | continue
    let some h1 ← omegaProves (← mkAppM ``LT.lt #[x, Lint]) | continue
    let half ← mkAppM ``kq_half #[L, x, h0, h1]
    -- `Q1`, the next level's slot width, read off `kq_half`'s statement `Q0 = 2 * Q1`
    let q1 := ((← inferType half).getArg! 2).getArg! 5
    assertMainM `hk_half (pure half)
    assertMainM `hk_pos (mkAppM ``kq_pos #[L, x, h0, h1])
    assertMainM `hk_m (mkAppM ``kq_m #[L, x, h0, h1])
    ok := ok.push (x, h0, h1, q1)
  -- the products `t · (4·2^L / 2^e)`
  let mut seen : Array (Lean.Expr × Lean.Expr) := #[]
  let mut halfSeen : Array (Lean.Expr × Lean.Expr) := #[]
  let mut prods : Array (Lean.Expr × Lean.Expr) := #[]
  for e in subs do
    unless e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 4).isFVar do continue
    let q := e.getArg! 5
    unless q.isAppOfArity ``HDiv.hDiv 6 && (q.getArg! 5).isAppOfArity ``HPow.hPow 6 do continue
    let some (x, d) := expVar? ((q.getArg! 5).getArg! 5) | continue
    let some (_, h0, h1, q1) := ok.find? (fun (x', _, _, _) => x' == x) | continue
    let gv := e.getArg! 4
    if d == 0 && !halfSeen.any (fun (g', x') => g' == gv && x' == x) then
      halfSeen := halfSeen.push (gv, x)
      assertMainM `hk_mhalf (mkAppM ``mul_half #[L, x, gv, h0, h1])
    if seen.any (fun (g', x') => g' == gv && x' == x) then continue
    seen := seen.push (gv, x)
    -- `t · Q1 + Q1 ≤ 3^x · Q1` (the product with the next level's width, `t < 3^x`)
    let B ← mkAppM ``HPow.hPow #[toExpr (3 : Int), ← mkAppM ``Int.toNat #[x]]
    let some hg ← omegaProves (← mkAppM ``LT.lt #[gv, B]) | continue
    let hpos ← mkAppM ``kq_pos #[L, x, h0, h1]
    let hy ← mkAppM ``Int.le_trans #[← mkDecideProof (← mkAppM ``LE.le #[toExpr (0 : Int), toExpr (4 : Int)]), hpos]
    assertMainM `hk_mul (mkAppM ``mul_add_le #[gv, B, q1, hg, hy])
    -- `0 ≤ t · Q1`
    if let some hg0 ← omegaProves (← mkAppM ``LE.le #[toExpr (0 : Int), gv]) then
      assertMainM `hk_mul0 (mkAppM ``Int.mul_nonneg #[hg0, hy])
    prods := prods.push (gv, q1)
  -- two products of two loop instances: their widths' congruence, the products' monotonicity and congruence
  for i in [0:prods.size] do
    for j in [0:prods.size] do
      if i == j then continue
      let (g1, y1) := prods[i]!
      let (g2, y2) := prods[j]!
      assertMainM `hk_mono (mkAppM ``LeanModels.Sv.CombView.mul_lt_mul_or₂ #[g1, g2, y1, y2])
      if i < j then
        assertMainM `hk_congr (mkAppM ``LeanModels.Sv.CombView.mul_congr_or #[g1, g2, y1, y2])
        if y1 != y2 then
          assertMainM `hk_wcongr (mkAppM ``LeanModels.Sv.CombView.div_pow_congr_or
            #[y1.getArg! 4, y2.getArg! 4, (y1.getArg! 5).getArg! 5, (y2.getArg! 5).getArg! 5])

/-! ## 2. Structure and ports -/

set_option maxHeartbeats 6000000 in
/-- `CombDesign` at every `1 ≤ N < 2^16`, with the shared obligations. -/
theorem kara_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 16) :
    CombDesign (clmul_kara.sem N) ∧ SharedObl clmul_kara.pdesign [N] := by
  sv_structure
  all_goals (intros; kara_facts; sv_rowmajor; (try simp only [true_and]); omega)

set_option maxHeartbeats 6000000 in
/-- `Acyclic`: operands down the levels, the base, products up the levels (the level counted from the base, so the key
is a `Nat` without truncation), the output last. -/
theorem kara_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 16) (hc : CombDesign (clmul_kara.sem N))
    (hso : SharedObl clmul_kara.pdesign [N]) : Acyclic (clmul_kara.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_split.g_node" _ [l, _] => (1, l.toNat, 0)
    | .fam "g_base" _ [_] => (2, 0, 0)
    | .fam "g_comb.g_node" _ [l, _] => (3, LeanModels.Sv.clog2 ((((N : Int) + 3) / 4).toNat) - l.toNat, 0)
    | .plain 2 => (4, 0, 0)
    | _ => (0, 0, 0)) using hc
  all_goals (intros; sv_rowmajor; (try simp only [true_and]); omega)

/-- The ports: `a`, `b` in, `p` out, with the task's widths. -/
theorem kara_ports (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 16) (hc : CombDesign (clmul_kara.sem N)) :
    (clmul_kara.sem N).inputPorts = [("a", N), ("b", N)] ∧
      (clmul_kara.sem N).outputPorts = [("p", 2 * N - 1)] := by
  sv_interface

/-! ## 3. From the equations to the rows' `View` -/

theorem boolAt_idx {st : SvState} {n : String} {a b : Nat} (h : a = b) : st.boolAt n a = st.boolAt n b := h ▸ rfl

theorem xor_congr' {a b c d : Bool} (h1 : a = c) (h2 : b = d) : (a ^^ b) = (c ^^ d) := h1 ▸ h2 ▸ rfl

theorem and_congr' {a b c d : Bool} (h1 : a = c) (h2 : b = d) : (a && b) = (c && d) := h1 ▸ h2 ▸ rfl

/-- Two Boolean terms of the same shape over `st.boolAt` reads whose indices `omega` shows equal. -/
syntax "kara_idx" : tactic
macro_rules
  | `(tactic| kara_idx) => `(tactic| first
      | exact boolAt_idx (by omega)
      | (refine xor_congr' ?_ ?_ <;> kara_idx)
      | (refine and_congr' ?_ ?_ <;> kara_idx))

/-- The slot width of a level as an `Int` quotient (the form the equations' bounds hold it in). -/
theorem W_cast (L l : Nat) : ((arith.W L l : Nat) : Int) = (4 : Int) * 2 ^ L / 2 ^ l := by
  simp only [arith.W, Int.natCast_ediv, Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]

/-! ## 4. The statement -/

set_option sv_comb.lp_atoms true in
set_option maxHeartbeats 8000000 in
/-- **The Karatsuba record meets the carry-less multiplier statement**, at every `N` with `1 ≤ N < 2^16`. -/
theorem clmul_kara_clmul : ClmulStatement clmul_kara.sem := by
  intro N ⟨hN, hR⟩
  obtain ⟨hc, hso⟩ := kara_comb N hN hR
  have ha := kara_acyclic N hN hR hc hso
  refine CombTask.of_comb hc ha (kara_ports N hN hR hc) fun inputs st heqs hsh hin => ?_
  intro x y hA hB
  sv_inputs
  sv_equations
  · sv_eq_nat
    -- the level count `L`, the zero padding `N ≤ P = 4·2^L ≤ 4·3^L`
    have hP := le_two_pow_clog2 ((N + 3) / 4)
    have h23 : 2 ^ clog2 ((N + 3) / 4) ≤ 3 ^ clog2 ((N + 3) / 4) :=
      Nat.pow_le_pow_left (by decide) _
    have hW0 : arith.W (clog2 ((N + 3) / 4)) 0 = 4 * 2 ^ clog2 ((N + 3) / 4) := by
      simp only [arith.W, Nat.pow_zero, Nat.div_one]
    -- the rows' equations
    have hv : arith.View (clog2 ((N + 3) / 4))
        (fun l j => st.boolAt "av" (l * (4 * 3 ^ clog2 ((N + 3) / 4)) + j))
        (fun l j => st.boolAt "bv" (l * (4 * 3 ^ clog2 ((N + 3) / 4)) + j))
        (fun l j => st.boolAt "rv" (l * (8 * 3 ^ clog2 ((N + 3) / 4)) + j)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro l hl t ht i hi
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hi hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_av_g_split_g_node_0 l hl t ht i (by omega)) ?_) <;> kara_idx
      · intro l hl t ht i hi
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hi hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_bv_g_split_g_node_1 l hl t ht i (by omega)) ?_) <;> kara_idx
      · intro l hl t ht i hi
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hi hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_av_g_split_g_node_2 l hl t ht i (by omega)) ?_) <;> kara_idx
      · intro l hl t ht i hi
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hi hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_bv_g_split_g_node_3 l hl t ht i (by omega)) ?_) <;> kara_idx
      · intro l hl t ht i hi
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hi hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_av_g_split_g_node_4 l hl t ht i (by omega)) ?_) <;> kara_idx
      · intro l hl t ht i hi
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hi hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_bv_g_split_g_node_5 l hl t ht i (by omega)) ?_) <;> kara_idx
      · intro t ht; exact eq_rv_g_base_0 t ht
      · intro t ht; exact eq_rv_g_base_1 t ht
      · intro t ht; exact eq_rv_g_base_2 t ht
      · intro t ht; exact eq_rv_g_base_3 t ht
      · intro t ht; exact eq_rv_g_base_4 t ht
      · intro t ht; exact eq_rv_g_base_5 t ht
      · intro t ht; exact eq_rv_g_base_6 t ht
      · intro l hl t ht k hk
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hk hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_rv_g_comb_g_node_0 l hl t ht k (by omega)) ?_) <;> kara_idx
      · intro l hl t ht k hk
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hk hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_rv_g_comb_g_node_1 l hl t ht k (by omega)) ?_) <;> kara_idx
      · intro l hl t ht
        simp only [arith.W]
        refine Eq.trans ?_ (Eq.trans (eq_rv_g_comb_g_node_2 l hl t ht) ?_) <;> kara_idx
      · intro l hl t ht k hk
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hk hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_rv_g_comb_g_node_3 l hl t ht k (by omega)) ?_) <;> kara_idx
      · intro l hl t ht k hk
        have hc1 := W_cast (clog2 ((N + 3) / 4)) (l + 1)
        simp only [arith.W] at hk hc1 ⊢
        refine Eq.trans ?_ (Eq.trans (eq_rv_g_comb_g_node_4 l hl t ht k (by omega)) ?_) <;> kara_idx
    -- level 0: the operands, zero-padded
    have ha0 : ∀ j, j < arith.W (clog2 ((N + 3) / 4)) 0 →
        st.boolAt "av" (0 * (4 * 3 ^ clog2 ((N + 3) / 4)) + j) = (decide (j < N) && x.getLsbD j) := by
      intro j hj
      rw [hW0] at hj
      rw [Nat.zero_mul, Nat.zero_add, eq_av_plain_0 j (by omega)]
      simp only [XF.zext]
      by_cases hjN : j < N
      · have h' : j < ((N : Int) + -1).natAbs + 1 := by omega
        simp [h', hjN, bit_a j hjN]
      · have h' : ¬ j < ((N : Int) + -1).natAbs + 1 := by omega
        simp [h', hjN]
    have hb0 : ∀ j, j < arith.W (clog2 ((N + 3) / 4)) 0 →
        st.boolAt "bv" (0 * (4 * 3 ^ clog2 ((N + 3) / 4)) + j) = (decide (j < N) && y.getLsbD j) := by
      intro j hj
      rw [hW0] at hj
      rw [Nat.zero_mul, Nat.zero_add, eq_bv_plain_1 j (by omega)]
      simp only [XF.zext]
      by_cases hjN : j < N
      · have h' : j < ((N : Int) + -1).natAbs + 1 := by omega
        simp [h', hjN, bit_b j hjN]
      · have h' : ¬ j < ((N : Int) + -1).natAbs + 1 := by omega
        simp [h', hjN]
    -- the output: the low `2N - 1` columns of level 0
    have hp0 : ∀ k, k < 2 * N - 1 → st.boolAt "p" k = st.boolAt "rv" (0 * (8 * 3 ^ clog2 ((N + 3) / 4)) + k) := by
      intro k hk
      rw [Nat.zero_mul, Nat.zero_add]
      exact eq_p_plain_2 k (by omega)
    have hbits := arith.view_out hv (by rw [hW0]; omega) ha0 hb0 hp0
    -- the port, from its known bits
    have hkp : ∀ k, k < 2 * N - 1 →
        (∃ v, st.lookup "p" = some v ∧ v.width = (2 * (N : Int) + -2).natAbs + 1) ∧ KnownBit st "p" k :=
      fun k hk => known_p_plain_2 k (by omega)
    rw [SvState.port_ofBitVec hkp (by omega) (by omega)]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [XF.getLsbD_bv hk, arith.getLsbD_ofBits, hbits k hk, ← arith.coeff_eq]
    simp [hk]
  sv_obligations

/-! ## Axioms -/

/--
info: 'Examples.«system-verilog».clmul_kara.clmul_proof.clmul_kara_clmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms clmul_kara_clmul

end Examples.«system-verilog».clmul_kara.clmul_proof
