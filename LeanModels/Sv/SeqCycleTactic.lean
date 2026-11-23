import LeanModels.Sv.SeqCycleInstant
import LeanModels.Sv.SeqCycleObl
import LeanModels.Sv.CombViewTactic
import LeanModels.Sv.Loop2Frag

/-!
# The clocked stages at symbolic parameters (`LeanModels.Sv.Kernel`, plumbing for `SeqCycle`)

The theory (`SeqCycle.lean`) relates the ordinary E route's slot function to a cycle on views. What remains per
design is computation at the design's symbolic parameters, and these macros do it, kernel-checked by `simp` and
`omega` (no `decide` on the loaded design: its instantiation is well-founded recursion, measured):

* `sv_seq_inst [X.e, X.pdesign] at hE` turns `hE : X.e P… = .ok E` into `hE : <normal form> = E`: the route's
  instantiation (`PDesign.instantiateCoreMemFrom`) evaluated at the symbolic parameters through its definitions'
  equation lemmas; the side conditions on the parameters (the 32-bit range of an `int` parameter, a declared width
  `[P-1:0]`, the unsigned range of an `int unsigned` parameter, the condition of a conditional generate construct)
  are closed by `omega` from the hypotheses in context. A generate loop is not expanded (the stage names it).
* `sv_seq_profile` closes `E.SeqProfile clk` on the normal form (`hE` substituted).
* `sv_seq_cycle h : E.cycleV clk v d using hE` (or `E.cycleMV clk (v, mv) d`) adds `h : … = <the computed result>`:
  THE CYCLE EQUATIONS, the pre and post sample of one cycle evaluated from the route's own definitions on a symbolic
  view (and memory view); a condition on the parameters is decided by `omega` from the context. A decision stays an
  `if` on values (an `if`, a `case` arm, an edge that may fire, a run-time index: `seqIndexRead`/`seqIndexWin`); a
  memory's next contents come out as one write equation (`memWrite`) and its reads as one read equation (`memRd`).
  A procedural `for` loop of nonblocking element writes comes out as ONE write equation over the header's value list
  (`memWriteL mv m (intRange a n) key data`: the list a function of the parameters, never unrolled), to be read through
  `memWriteL_id` / `memWriteL_index` / `memWriteL_of_not_key` with the index facts `seqK_index?_ofInt32`.

Each macro takes extra simp lemmas in brackets for facts of the design the default sets do not know. Nothing here is
trusted: every step is a `simp` or `omega` proof the kernel checks.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Lemmas the normalizations use -/

theorem seqE_except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem seqE_except_mapError_ok {ε ε' α : Type} (g : ε → ε') (a : α) :
    (Except.ok a : Except ε α).mapError g = .ok a := rfl

theorem seqE_except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

/-- The declared width of `[P-1:0]` at a parameter `P ≥ 1`. -/
theorem seqE_natAbs_sub_one_add_one (N : Nat) (h : 1 ≤ N) : ((N : Int) - 1).natAbs + 1 = N := by omega

theorem seqE_natAbs_sub_one (N : Nat) (h : 1 ≤ N) : ((N : Int) - 1).natAbs = N - 1 := by omega

/-- The declared width of `[A+B-1:0]` at parameters with `A + B ≥ 1`. -/
theorem seqE_natAbs_add_sub_one_add_one (A B : Nat) (h : 1 ≤ A + B) :
    ((A : Int) + (B : Int) - 1).natAbs + 1 = A + B := by
  omega

/-- No positive edge into a 0. -/
theorem seqE_isPosedge_l0 (b : Logic) : isPosedge b .l0 = false := by cases b <;> rfl

/-- Bit 0 as the cycle stage leaves it for a vector of known nonzero width (`v.bits[0]`), as the edge table reads it. -/
theorem seqE_getElem_zero (v : LVec) (h : 0 < v.bits.size) : v.bits[0]'h = v.bits[0]?.getD .lx := by
  simp [Array.getElem?_eq_getElem h]

theorem seqE_bit0_zero : (LVec.ofBitVec 0#1).bits[0]? = some Logic.l0 := by decide
theorem seqE_bit0_one : (LVec.ofBitVec 1#1).bits[0]? = some Logic.l1 := by decide

theorem seqE_resizeU_resizeU (v : LVec) (w : Nat) : (v.resizeU w).resizeU w = v.resizeU w :=
  LVec.resizeU_of_width (LVec.width_resizeU v w)

theorem seqE_resizeU_l0 : (⟨#[.l0]⟩ : LVec).resizeU 1 = ⟨#[.l0]⟩ := by decide

theorem seqE_width_bit (b : Logic) : (⟨#[b]⟩ : LVec).width = 1 := rfl

/-- Vector `+` has the wider operand's width. -/
theorem seqE_width_add (a b : LVec) : (a.add b).width = max a.width b.width := by
  unfold LVec.add
  split
  · exact LVec.width_ofNat _ _
  · simp [LVec.arithWidth]

/-- A whole-signal write at offset 0 of a value of the signal's width is that value. -/
theorem seqE_insertAt_zero {v p : LVec} (h : p.width = v.width) : v.insertAt 0 p = p :=
  LVec.insertAt_zero_of_width_eq h
theorem seqE_resizeU_l1 : (⟨#[.l1]⟩ : LVec).resizeU 1 = ⟨#[.l1]⟩ := by decide

/-- `{n{b}}` of one bit is `n` copies of the bit (§11.4.12.1): the replication of a one-bit literal, as a reset value
`{N{1'b0}}` writes it, in the form the knownness lemmas read (`LVec.replicate_l0`, `LVec.replicate_l1`). -/
theorem seqE_replVec_bit (n : Nat) (b : Logic) : LVec.replVec n ⟨#[b]⟩ = LVec.replicate n b := by
  have h : ∀ k : Nat, (List.replicate k [b]).flatten = List.replicate k b := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  unfold LVec.replVec LVec.replicate
  congr 1
  apply Array.ext'
  rw [Array.toList_flatten, Array.toList_replicate, List.map_replicate, Array.toList_replicate]
  exact h n

/-! ## Constant expressions over a parameter of an unsigned type

A dimension `[W-1:0]` over `parameter int W` is INT-class and the instantiation evaluates it in 32-bit signed arithmetic
(`evalIntExact`). Over `parameter int unsigned W` it is not: the instantiation sizes the expression (§11.6:
`evalSized`, the propagated type `ctype`, the evaluation at that type `evalAt`) and wraps every value to the unsigned
32-bit type. The instantiation pass evaluates that route through the lemmas below (a parameter read, an integer
literal, `+`, `-`, `*`; any other operator stays as the route left it and the stage reports the design as not
instantiated), and the arithmetic pass reads a wrapped value as itself where `omega` places it in `[0, 2^32)` from the
hypotheses in context. -/

/-- An unsigned 32-bit wrap of a value in `[0, 2^32)` is the value. -/
theorem seqE_canonU32_of_bounds {v : Int} (h1 : 0 ≤ v) (h2 : v < 4294967296) : canonInt 32 false v = v := by
  have h : (2 : Int) ^ 32 = 4294967296 := by decide
  unfold canonInt
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [h]
  exact Int.emod_eq_of_lt h1 h2

/-- The conversion of a 32-bit value in `[0, 2^32)` to the unsigned 32-bit type is the value. -/
theorem seqE_convertU32_of_bounds {v : Int} (h1 : 0 ≤ v) (h2 : v < 4294967296) :
    convertConst 32 32 false v = v := by
  have h : (2 : Int) ^ 32 = 4294967296 := by decide
  unfold convertConst
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h]
  have e : v.emod 4294967296 = v := Int.emod_eq_of_lt h1 h2
  rw [e]
  exact seqE_canonU32_of_bounds h1 h2

/-- `evalAt` on an integer literal. -/
theorem seqE_evalAt_int (env : IEnv) (ty : Nat × Bool) (v : Int) :
    evalAt env ty (.int v) = .ok (convertConst 32 ty.1 ty.2 v) := by
  simp only [evalAt]

/-- `evalAt` on a parameter read. -/
theorem seqE_evalAt_param (env : IEnv) (ty : Nat × Bool) (n : String) :
    evalAt env ty (.paramRef n none) = (match env.vals.lookup n with
      | some v => .ok (convertConst 32 ty.1 ty.2 v)
      | none =>
          match env.nvals.lookup n with
          | some (v, w, _) => .ok (convertConst w ty.1 ty.2 v)
          | none => .error s!"unbound parameter '{n}'") := by
  simp only [evalAt]
  cases h1 : List.lookup n env.vals with
  | some v => rfl
  | none =>
      cases h2 : List.lookup n env.nvals with
      | none => rfl
      | some t => rfl

/-- `evalAt` on a difference: both operands at the propagated type, the result wrapped to it. -/
theorem seqE_evalAt_sub (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary (.m0 .sub) l r) = (do
      let a ← evalAt env ty l
      let b ← evalAt env ty r
      .ok (canonInt ty.1 ty.2 (a - b))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

/-- `evalAt` on a sum. -/
theorem seqE_evalAt_add (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary (.m0 .add) l r) = (do
      let a ← evalAt env ty l
      let b ← evalAt env ty r
      .ok (canonInt ty.1 ty.2 (a + b))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

/-- `evalAt` on a product. -/
theorem seqE_evalAt_mul (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary (.m0 .mul) l r) = (do
      let a ← evalAt env ty l
      let b ← evalAt env ty r
      .ok (canonInt ty.1 ty.2 (a * b))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

/-! ## The condition of a conditional generate construct

The route selects the arm of `if (c) … else …` by `evalGenGuard` (the condition typed by `ctype` and evaluated at its
type by `evalAt`, IEEE 1800-2017 §27.5, §11.6). The instantiation pass evaluates a comparison of two constant
operands through the lemmas below (each is `evalAt`'s own arm for that operator: the operands at their common type, the
frontend's signedness check kept, the 0/1 result converted to the condition's type); the arithmetic pass then decides
the comparison by `omega` from the hypotheses in context, so a structure theorem states the arm it is about as a
hypothesis on the parameters (`(h : REG = 0)`, `(h : 1 ≤ REG)`). A condition the hypotheses do not decide stays an
`if`, and the stage reports the design as not instantiated at these parameters. -/

/-- `evalAt` on `l == r`. -/
theorem seqE_evalAt_eq (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary (.m0 .eq) l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      let a ← evalAt env (max wl wr, sl && sr) l
      let b ← evalAt env (max wl wr, sl && sr) r
      .ok (convertConst 1 ty.1 ty.2 (if a == b then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

/-- `evalAt` on `l != r`. -/
theorem seqE_evalAt_ne (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary (.m0 .ne) l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      let a ← evalAt env (max wl wr, sl && sr) l
      let b ← evalAt env (max wl wr, sl && sr) r
      .ok (convertConst 1 ty.1 ty.2 (if a != b then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

theorem seqE_evalAt_slt (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary .slt l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      if (true && !(sl && sr) || false && (sl && sr)) = true then
        .error s!"'{(SymBinOp.slt).sym}' contradicts the operand signedness (constant tier)"
      else do
        let a ← evalAt env (max wl wr, sl && sr) l
        let b ← evalAt env (max wl wr, sl && sr) r
        .ok (convertConst 1 ty.1 ty.2 (if decide (a < b) = true then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

theorem seqE_evalAt_sle (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary .sle l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      if (true && !(sl && sr) || false && (sl && sr)) = true then
        .error s!"'{(SymBinOp.sle).sym}' contradicts the operand signedness (constant tier)"
      else do
        let a ← evalAt env (max wl wr, sl && sr) l
        let b ← evalAt env (max wl wr, sl && sr) r
        .ok (convertConst 1 ty.1 ty.2 (if decide (a ≤ b) = true then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

theorem seqE_evalAt_sgt (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary .sgt l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      if (true && !(sl && sr) || false && (sl && sr)) = true then
        .error s!"'{(SymBinOp.sgt).sym}' contradicts the operand signedness (constant tier)"
      else do
        let a ← evalAt env (max wl wr, sl && sr) l
        let b ← evalAt env (max wl wr, sl && sr) r
        .ok (convertConst 1 ty.1 ty.2 (if decide (a > b) = true then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

theorem seqE_evalAt_sge (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary .sge l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      if (true && !(sl && sr) || false && (sl && sr)) = true then
        .error s!"'{(SymBinOp.sge).sym}' contradicts the operand signedness (constant tier)"
      else do
        let a ← evalAt env (max wl wr, sl && sr) l
        let b ← evalAt env (max wl wr, sl && sr) r
        .ok (convertConst 1 ty.1 ty.2 (if decide (a ≥ b) = true then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

theorem seqE_evalAt_lt (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary (.m0 .lt) l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      if (false && !(sl && sr) || true && (sl && sr)) = true then
        .error s!"'{((SymBinOp.m0 .lt)).sym}' contradicts the operand signedness (constant tier)"
      else do
        let a ← evalAt env (max wl wr, sl && sr) l
        let b ← evalAt env (max wl wr, sl && sr) r
        .ok (convertConst 1 ty.1 ty.2 (if decide (a < b) = true then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

theorem seqE_evalAt_le (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary (.m0 .le) l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      if (false && !(sl && sr) || true && (sl && sr)) = true then
        .error s!"'{((SymBinOp.m0 .le)).sym}' contradicts the operand signedness (constant tier)"
      else do
        let a ← evalAt env (max wl wr, sl && sr) l
        let b ← evalAt env (max wl wr, sl && sr) r
        .ok (convertConst 1 ty.1 ty.2 (if decide (a ≤ b) = true then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

theorem seqE_evalAt_gt (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary (.m0 .gt) l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      if (false && !(sl && sr) || true && (sl && sr)) = true then
        .error s!"'{((SymBinOp.m0 .gt)).sym}' contradicts the operand signedness (constant tier)"
      else do
        let a ← evalAt env (max wl wr, sl && sr) l
        let b ← evalAt env (max wl wr, sl && sr) r
        .ok (convertConst 1 ty.1 ty.2 (if decide (a > b) = true then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

theorem seqE_evalAt_ge (env : IEnv) (ty : Nat × Bool) (l r : PExpr) :
    evalAt env ty (.binary (.m0 .ge) l r) = (do
      let (wl, sl) ← ctype env l
      let (wr, sr) ← ctype env r
      if (false && !(sl && sr) || true && (sl && sr)) = true then
        .error s!"'{((SymBinOp.m0 .ge)).sym}' contradicts the operand signedness (constant tier)"
      else do
        let a ← evalAt env (max wl wr, sl && sr) l
        let b ← evalAt env (max wl wr, sl && sr) r
        .ok (convertConst 1 ty.1 ty.2 (if decide (a ≥ b) = true then 1 else 0))) := by
  simp only [evalAt, SymBinOp.constClass]
  rfl

/-- A 0/1 value is nonzero exactly when its condition holds (the route's arm selection `v != 0`). -/
theorem seqE_ite_ne_zero (c : Prop) [Decidable c] : ((if c then (1 : Int) else 0) != 0) = decide c := by
  split <;> simp_all

/-! ## Per-signal equations: a decision stays an `if` on the values it decides

The evaluation pass does not split the cycle at the design's decisions (an `if`, a `case` arm, an edge that may or may
not fire). It pushes each decision inward through `Res.ok`, pairs, lists and the commit, so the computed post view is
ONE list whose entries carry the decisions as `if`s on the values: the next value of each signal as its own equation
(`("q", if r.condTrue = true then … else …)`). A branch that refuses keeps the `if` at the `Res` level (no `.ok` to
merge with), so a refusal is never hidden. -/

theorem seqE_ite_ok {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then Res.ok a else Res.ok b) = Res.ok (if p then a else b) := by split <;> rfl

theorem seqE_ite_pair {α β : Type} (p : Prop) [Decidable p] (a c : α) (b d : β) :
    (if p then (a, b) else (c, d)) = (if p then a else c, if p then b else d) := by split <;> rfl

theorem seqE_ite_cons {α : Type} (p : Prop) [Decidable p] (x y : α) (xs ys : List α) :
    (if p then x :: xs else y :: ys) = (if p then x else y) :: (if p then xs else ys) := by split <;> rfl

theorem seqE_commit_ite (p : Prop) [Decidable p] (v : SvState) (q₁ q₂ : NbaQueue2) :
    commitNba2 v (if p then q₁ else q₂) = if p then commitNba2 v q₁ else commitNba2 v q₂ := by split <;> rfl

theorem seqE_resizeU_ite (p : Prop) [Decidable p] (a b : LVec) (w : Nat) :
    (if p then a else b).resizeU w = if p then a.resizeU w else b.resizeU w := by split <;> rfl

theorem seqE_width_ite (p : Prop) [Decidable p] (a b : LVec) :
    (if p then a else b).width = if p then a.width else b.width := by split <;> rfl

/-- The width of a literal vector. -/
theorem seqE_width_lit (bs : Array Logic) : (⟨bs⟩ : LVec).width = bs.size := rfl

/-- The commit of an empty queue changes nothing. -/
theorem seqE_commit_nil (v : SvState) : commitNba2 v [] = v := rfl

/-- The commit of a queue, one update at a time (so a queue that is an `if` is split by `seqE_commit_ite` before its
updates are applied, never unfolded into a `foldl` over an `if`). -/
theorem seqE_commit_cons (v : SvState) (u : String × Nat × LVec) (us : NbaQueue2) :
    commitNba2 v (u :: us) = commitNba2 (match SvState.lookup v u.1 with
      | some old => SvState.set v u.1 (old.insertAt u.2.1 u.2.2)
      | none => v) us := rfl

theorem seqE_append_ite {α : Type} (p : Prop) [Decidable p] (xs ys zs : List α) :
    xs ++ (if p then ys else zs) = if p then xs ++ ys else xs ++ zs := by split <;> rfl

theorem seqE_ite_append {α : Type} (p : Prop) [Decidable p] (xs ys zs : List α) :
    (if p then ys else zs) ++ xs = if p then ys ++ xs else zs ++ xs := by split <;> rfl

theorem seqE_ite_fst {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl

theorem seqE_ite_snd {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl

/-! ## Run-time selects: the index decision kept as a value

A run-time element read (`Expr2.index`) and a select target's window (`resolveLhs2` on `.index`) decide on the index
value (x/z or out of range: all x, or no write window, §11.5.1). The evaluation pass keeps that decision as a value
(`seqIndexRead`, `seqIndexWin`) instead of a `match` at the `Res` level, and evaluates the window resolver's fuel
evaluator by its fuel-free twin (`evalExpr2_eq_evalPure2`). -/

/-- `evalPure2`'s run-time element read, its decision a value. -/
def seqIndexRead (bv : LVec) (i? : Option Int) (w : Nat) : LVec :=
  match i? with
  | some i => if 0 ≤ i && (i + 1) * w ≤ bv.width then bv.extract (i.toNat * w) w else LVec.xVec w
  | none => LVec.xVec w

theorem seqE_evalPure2_index (st : SvState) (base idx : Expr2) (w : Nat) :
    evalPure2 st (.index base idx w) = (do
      let bv ← evalPure2 st base
      let iv ← evalPure2 st idx
      .ok (seqIndexRead bv (indexInt? idx iv) w)) := by
  rw [evalPure2_index]
  cases evalPure2 st base with
  | ok bv =>
      cases evalPure2 st idx with
      | ok iv =>
          simp only [Res.ok_bind, seqIndexRead]
          cases indexInt? idx iv with
          | none => rfl
          | some i =>
              by_cases hc : (decide (0 ≤ i) && decide ((i + 1) * (w : Int) ≤ (bv.width : Int))) = true <;>
                simp [hc]
      | timeout => rfl
      | unsupported m => rfl
  | timeout => rfl
  | unsupported m => rfl

/-- `resolveLhs2`'s window of a run-time select target, its decision a value (`none`: no write). -/
def seqIndexWin (old : LVec) (i? : Option Int) (w : Nat) : Option (Nat × Nat) :=
  match i? with
  | some i => if 0 ≤ i && (i + 1) * w ≤ old.width then some (i.toNat * w, w) else none
  | none => none

theorem seqE_resolveLhs2_index (fuel : Nat) (st : SvState) (n : String) (idx : Expr2) (w : Nat) :
    resolveLhs2 fuel st (.index n idx w) = (do
      let iv ← evalExpr2 fuel st idx
      match SvState.lookup st n with
      | none => .unsupported s!"unknown assignment target '{n}'"
      | some old => .ok (n, seqIndexWin old (indexInt? idx iv) w)) := by
  simp only [resolveLhs2]
  cases evalExpr2 fuel st idx with
  | ok iv =>
      simp only [Res.ok_bind]
      cases SvState.lookup st n with
      | none => rfl
      | some old =>
          simp only [seqIndexWin]
          cases indexInt? idx iv with
          | none => rfl
          | some i =>
              by_cases hc : (decide (0 ≤ i) && decide ((i + 1) * (w : Int) ≤ (old.width : Int))) = true <;>
                simp [hc]
  | timeout => rfl
  | unsupported m => rfl

/-! ## Memories: the write equation and the read equation through the evaluation pass

A memory's next contents come out of the evaluation pass as ONE write equation (`memWrite`) under the decisions that
issue it (pushed through `commitMemV`), its reads as ONE read equation (`memRd`) of the memory view the slot holds. -/

theorem seqE_commitMemV_ite (p : Prop) [Decidable p] (mv : MemV) (q₁ q₂ : MemQV) :
    commitMemV mv (if p then q₁ else q₂) = if p then commitMemV mv q₁ else commitMemV mv q₂ := by split <;> rfl

/-- The commit of one issued element write is the write equation. -/
theorem seqE_commitMemV_memIss (mv : MemV) (n : String) (k? : Option Int) (x : LVec) :
    commitMemV mv (memIss n k? x) = memWrite mv n k? x := by
  simpa using commitMemV_memIss mv n k? x []

theorem seqE_memRd_ite (p : Prop) [Decidable p] (a b : MemV) (n : String) (k? : Option Int) (w : Nat) :
    memRd (if p then a else b) n k? w = if p then memRd a n k? w else memRd b n k? w := by split <;> rfl

theorem seqE_memIss_ite (p : Prop) [Decidable p] (n : String) (k? : Option Int) (x y : LVec) :
    memIss n k? (if p then x else y) = if p then memIss n k? x else memIss n k? y := by split <;> rfl

/-- A read of an element: of the element width, when every element of the memory view has it. -/
theorem seqE_memRd_width {mv : MemV} {n : String} {w : Nat} (h : ∀ k, (mv n k).width = w) (k? : Option Int) :
    (memRd mv n k? w).width = w := by
  cases k? with
  | none => simp [memRd, LVec.xVec, LVec.replicate, LVec.width]
  | some k => exact h k

/-! ## The knownness bridge: the route's own decision forms on known values

Known2's simp set turns the evaluator's operators on known values (`LVec.ofBitVec`) into `BitVec` terms. The cycle
equations carry, beside them, the route's decision forms: `condTrue` of a logical not, an edge-table test on bit 0, a
case equality. On known values each is a `Bool` of the `BitVec`s, so a per-signal equation on known state and inputs
becomes a `BitVec` equation (`ite_ofBitVec` folds the `if`s). -/

/-- `!x` reads true exactly when `x` is zero. -/
theorem seqK_lnot_condTrue {w : Nat} (x : BitVec w) :
    (evalUnaryOp .lnot (LVec.ofBitVec x)).condTrue = decide (x = 0#w) := by
  by_cases hx : x = 0#w <;> simp [evalUnaryOp, LVec.lnot, hx]

/-- Bit 0 of a known vector. -/
theorem seqK_bit0 {w : Nat} (x : BitVec w) (hw : 0 < w) :
    (LVec.ofBitVec x).bits[0]?.getD Logic.lx = Logic.ofBool (x.getLsbD 0) := by
  simp [LVec.getElem?_ofBitVec, hw]

/-- The edge table (§9.4.2) on known bits: a fall is 1 → 0. -/
theorem seqK_isNegedge (a b : Bool) : isNegedge (Logic.ofBool a) (Logic.ofBool b) = (a && !b) := by
  cases a <;> cases b <;> rfl

/-- The edge table on known bits: a rise is 0 → 1. -/
theorem seqK_isPosedge (a b : Bool) : isPosedge (Logic.ofBool a) (Logic.ofBool b) = (!a && b) := by
  cases a <;> cases b <;> rfl

/-- Case equality of known vectors is `BitVec` equality. -/
theorem seqK_beq {w : Nat} (x y : BitVec w) : (LVec.ofBitVec x == LVec.ofBitVec y) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, LVec.ofBitVec_inj]

/-- A known unsigned index resolves to its value when it is in the declared range, and to the no-op otherwise. -/
theorem seqK_index? {w : Nat} (m : MemShape) (a : BitVec w) :
    m.index? false (LVec.ofBitVec a) = if m.inRange (a.toNat : Int) then some (a.toNat : Int) else none := by
  simp [MemShape.index?, LVec.toNat?_ofBitVec]

/-! ## Procedural `for` loops: the header's value list and the loop's write equation

The route evaluates a loop header to its value list (`forValues2`); for `for (i = a; i < P; i++)` and `<=` against a
parameter (a step `i++` or `i = i + 1`) the library has the list in closed form at a symbolic bound
(`Loop2.forValues2_slt`, `_sle` and their `_nval` forms below: `intRange a n`). The passes rewrite the header by it and keep the loop as the fold over that list (`execLoopV`), in
closed form when every iteration is evaluated (`execLoopV_ok`: the concatenation of the iterations' updates over the
list); the commit of a loop of element writes is `memWriteL`. Nothing is unrolled: `intRange a n` at a symbolic `n`
has no cons cell to unfold. -/

/-- An index a loop computes (a 32-bit integer, `LVec.ofInt 32 i`) reads as itself when it is in `[0, 2^32)`. -/
theorem seqK_toNat?_ofInt32 {i : Int} (h0 : 0 ≤ i) (h1 : i < 4294967296) :
    (LVec.ofInt 32 i).toNat? = some i.toNat := by
  have h : (2 : Int) ^ 32 = 4294967296 := by decide
  have h' : (2 : Nat) ^ 32 = 4294967296 := by decide
  have he : i.emod ((2 : Int) ^ 32) = i := by
    rw [h]
    exact Int.emod_eq_of_lt h0 h1
  rw [LVec.ofInt, he, LVec.toNat?_ofNat, h']
  congr 1
  apply Nat.mod_eq_of_lt
  omega

/-- **The index decision at a loop's index**: an integer index `i` in `[0, 2^32)` resolves to the label `i` when it is
in the declared range, and to the no-op otherwise (§11.5.1). -/
theorem seqK_index?_ofInt32 (m : MemShape) {i : Int} (h0 : 0 ≤ i) (h1 : i < 4294967296) :
    m.index? false (LVec.ofInt 32 i) = if m.inRange i then some i else none := by
  simp [MemShape.index?, seqK_toNat?_ofInt32 h0 h1, Int.toNat_of_nonneg h0]

/-- The statically allocated trip fuel covers every value in a checked loop
header's trace. The checked route can refuse a wrapping trace, while the
legacy arithmetic mirror is used only to expose its fuel count. -/
theorem seqE_loopTrips_ok {env : IEnv} {it : String} {init cond step : PExpr} {values : List Int}
    (h : forValues2Int32 env it init cond step = .ok values) : values.length ≤ loopTrips env it init cond step := by
  have hlegacy := forValues2_of_forValues2Int32_ok env it init cond step h
  unfold forValues2 at hlegacy
  unfold loopTrips
  cases hfuel : forFuel2 env it init cond step with
  | error e => simp [hfuel] at hlegacy
  | ok fuel =>
      rw [hfuel] at hlegacy
      have hl := forValuesFuel2_length_add_two_le env it init cond step hlegacy
      simp [hfuel] at *
      omega

/-- An element of a written memory has the element width when the old elements and the written value have it. -/
theorem seqE_memWrite_width {mv : MemV} {n : String} {k? : Option Int} {x : LVec} {w : Nat}
    (hmv : ∀ k, (mv n k).width = w) (hx : x.width = w) (k : Int) : (memWrite mv n k? x n k).width = w := by
  unfold memWrite
  split
  · exact hx
  · exact hmv k

/-- An element of a memory a loop wrote has the element width when the old elements and every written value have it. -/
theorem seqE_memWriteL_width {mv : MemV} {n : String} {vals : List Int} {key : Int → Option Int} {x : Int → LVec}
    {w : Nat} (hmv : ∀ k, (mv n k).width = w) (hx : ∀ i, (x i).width = w) (k : Int) :
    (memWriteL mv n vals key x n k).width = w :=
  memWriteL_width vals mv hmv (fun i _ => hx i) k

/-- A read of a memory a loop wrote, converted to the element width, is the read. -/
theorem seqE_resizeU_memRd_memWriteL {mv : MemV} {n : String} {vals : List Int} {key : Int → Option Int}
    {x : Int → LVec} {w : Nat} (h : ∀ k, (memWriteL mv n vals key x n k).width = w) (k? : Option Int) :
    (memRd (memWriteL mv n vals key x) n k? w).resizeU w = memRd (memWriteL mv n vals key x) n k? w :=
  LVec.resizeU_of_width (seqE_memRd_width h k?)

/-- A loop whose iterations issue nothing issues nothing. -/
theorem seqE_flatMap_nil {α β : Type} (l : List α) : (l.flatMap fun _ => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

end LeanModels.Sv.Kernel

namespace LeanModels.Sv.Loop2

/-! ### The ascending unit-step headers against a typed parameter

`forValues2_slt`/`_sle` read the bound from `IEnv.vals`. The clocked route binds a typed `int` parameter in
`IEnv.nvals` (its value with its width and signedness), where it is INT-class as well: the same closed form holds. -/

/-- **`for (it = s; it < e; step)` and `it <= e` against an INT-class bound `e`**, for a step of `+1` (`it++`,
`it = it + 1`): the bound evaluates to `B` whatever the iterator's value; the trips are `s, s+1, …` (`c.bound B - s`
of them, none when negative). `forValues2_up` is the instance `e = P`, a parameter bound in `IEnv.vals`, step
`it++`. -/
theorem forValues2_up_of {env : IEnv} {it : String} {rhs step : PExpr} {c : Cmp} {B : Int} (hc : c = .lt ∨ c = .le)
    (hstep : procStepDelta2 env it step = .ok 1)
    (hri : ∀ v, rhs.isInt (env.bindVal it v) = true) (hrv : ∀ v, evalInt (env.bindVal it v) rhs = .ok B)
    (hb : evalInt env rhs = .ok B) (s : Int) :
    forValues2 env it (.int s) (.binary c.op (.genvarRef it) rhs) step =
      .ok (intRange s (c.bound B - s).toNat) := by
  have hf : forFuel2 env it (.int s) (.binary c.op (.genvarRef it) rhs) step =
      .ok ((c.bound B - s).toNat + 2) := by
    rcases hc with rfl | rfl
    · by_cases hsb : s < B
      · have h1 : ¬ (B - s < 0) := by omega
        simp [forFuel2, procLoopIterator, Cmp.op, Cmp.bound, hb, hstep, Gen2.except_ok_bind, hsb, h1]
        rfl
      · have h1 : (B - s).toNat = 0 := by omega
        simp [forFuel2, procLoopIterator, Cmp.op, Cmp.bound, hb, hstep, Gen2.except_ok_bind, hsb, h1]
        rfl
    · by_cases hsb : s ≤ B
      · have h1 : ¬ (B - s + 1 < 0) := by omega
        have h2 : B + 1 - s = B - s + 1 := by omega
        simp [forFuel2, procLoopIterator, Cmp.op, Cmp.bound, hb, hstep, Gen2.except_ok_bind, hsb, h1, h2]
        rfl
      · have h1 : (B + 1 - s).toNat = 0 := by omega
        simp [forFuel2, procLoopIterator, Cmp.op, Cmp.bound, hb, hstep, Gen2.except_ok_bind, hsb, h1]
        rfl
  rw [forValues2, hf]
  simp only [forValuesFuel2, evalInt_int, hstep]
  rw [← TripSchema.toList_arith_one]
  have hg := guard_canon c hri hrv
  apply forValuesFuel2_go_arith _ s _ (by omega)
  · intro k hk
    obtain ⟨r, hr, hiff⟩ := hg (s + k * 1)
    exact ⟨r, hr, hiff.mpr (by
      rw [Cmp.holds_iff]; rcases hc with rfl | rfl <;> simp [Cmp.sign, Cmp.bound] at * <;> omega)⟩
  · obtain ⟨r, hr, hiff⟩ := hg (s + ((c.bound B - s).toNat : Nat) * 1)
    rw [hr]
    by_cases h0 : r = 0
    · rw [h0]
    · exact absurd (hiff.mp h0) (by
        rw [Cmp.holds_iff]; rcases hc with rfl | rfl <;> simp [Cmp.sign, Cmp.bound] <;> omega)

/-- `it = it + 1` steps by `1`. -/
theorem procStepDelta2_add_one (env : IEnv) (it : String) :
    procStepDelta2 env it (.binary (.m0 .add) (.genvarRef it) (.int 1)) = .ok 1 :=
  procStepDelta2_add (evalInt_int 1) (by decide)

/-- `for (it = s; it < P; it = it + 1)` and `it <= P` against a parameter bound in `IEnv.vals` (`forValues2_up` with
the step written as an assignment). -/
theorem forValues2_up_add {env : IEnv} {it p : String} {c : Cmp} (hc : c = .lt ∨ c = .le)
    (h : (env.vals.lookup p).isSome = true) (hne : p ≠ it) (s : Int) :
    forValues2 env it (.int s) (.binary c.op (.genvarRef it) (.paramRef p none))
        (.binary (.m0 .add) (.genvarRef it) (.int 1)) = .ok (intRange s (c.bound (envVal env p) - s).toNat) := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp h
  have hl : ∀ u, (env.bindVal it u).vals.lookup p = some B := fun u => by
    rw [vals_lookup_bindVal_ne u hne, hB]
  rw [envVal_of_lookup hB]
  exact forValues2_up_of hc (procStepDelta2_add_one env it) (fun u => isInt_paramRef_of (hl u))
    (fun u => evalInt_paramRef_of (hl u)) (evalInt_paramRef_of hB) s

theorem forValues2_slt_add {env : IEnv} {it p : String} (h : (env.vals.lookup p).isSome = true) (hne : p ≠ it)
    (s : Int) :
    forValues2 env it (.int s) (.binary .slt (.genvarRef it) (.paramRef p none))
        (.binary (.m0 .add) (.genvarRef it) (.int 1)) = .ok (intRange s (envVal env p - s).toNat) :=
  forValues2_up_add (c := .lt) (.inl rfl) h hne s

theorem forValues2_sle_add {env : IEnv} {it p : String} (h : (env.vals.lookup p).isSome = true) (hne : p ≠ it)
    (s : Int) :
    forValues2 env it (.int s) (.binary .sle (.genvarRef it) (.paramRef p none))
        (.binary (.m0 .add) (.genvarRef it) (.int 1)) = .ok (intRange s (envVal env p + 1 - s).toNat) :=
  forValues2_up_add (c := .le) (.inr rfl) h hne s

/-- The value of a typed parameter (`IEnv.nvals`), 0 when unbound. -/
def nvalOf (env : IEnv) (p : String) : Int :=
  match env.nvals.lookup p with
  | some (v, _, _) => v
  | none => 0

/-- A typed `int` parameter: bound in `IEnv.nvals` at 32 bits signed, not in `IEnv.vals` (INT-class, read from
`nvals`) and not stale (`IEnv.stale`: `evalInt` refuses a stale name, so its value is not the bound one). -/
def nvalInt (env : IEnv) (p : String) : Bool :=
  ((env.vals.lookup p).isNone &&
    match env.nvals.lookup p with
    | some (_, 32, true) => true
    | _ => false) && decide (p ∉ env.stale)

/-- A typed `int` parameter as a loop bound, for a step of `+1`. -/
theorem forValues2_up_nval {env : IEnv} {it p : String} {step : PExpr} {c : Cmp} (hc : c = .lt ∨ c = .le)
    (hstep : procStepDelta2 env it step = .ok 1) (h : nvalInt env p = true) (hne : p ≠ it) (s : Int) :
    forValues2 env it (.int s) (.binary c.op (.genvarRef it) (.paramRef p none)) step =
      .ok (intRange s (c.bound (nvalOf env p) - s).toNat) := by
  simp only [nvalInt, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hn⟩, hs⟩ := h
  have hsu : ∀ u, p ∉ (env.bindVal it u).stale := fun _ => hs
  have hlv : ∀ u, (env.bindVal it u).vals.lookup p = none := fun u => by rw [vals_lookup_bindVal_ne u hne, hv]
  have hnv : ∀ u, (env.bindVal it u).nvals = env.nvals := fun _ => rfl
  cases hl : env.nvals.lookup p with
  | none => rw [hl] at hn; simp at hn
  | some t =>
      obtain ⟨B, w, sg⟩ := t
      have hval : nvalOf env p = B := by simp [nvalOf, hl]
      rw [hval]
      refine forValues2_up_of hc hstep (fun u => ?_) (fun u => ?_) ?_ s
      · simp only [PExpr.isInt, hlv u, hnv u, Option.isSome_none, Bool.false_or]
        exact hn
      · simp only [evalInt, hlv u, hnv u, hl, hsu u, ↓reduceIte]
      · simp only [evalInt, hv, hl, hs, ↓reduceIte]

/-- `for (it = s; it < P; it++)` against a typed `int` parameter `P`. -/
theorem forValues2_slt_nval {env : IEnv} {it p : String} (h : nvalInt env p = true) (hne : p ≠ it) (s : Int) :
    forValues2 env it (.int s) (.binary .slt (.genvarRef it) (.paramRef p none)) (.unary .inc (.genvarRef it)) =
      .ok (intRange s (nvalOf env p - s).toNat) :=
  forValues2_up_nval (c := .lt) (.inl rfl) (procStepDelta2_inc env it) h hne s

/-- `for (it = s; it <= P; it++)` against a typed `int` parameter `P`. -/
theorem forValues2_sle_nval {env : IEnv} {it p : String} (h : nvalInt env p = true) (hne : p ≠ it) (s : Int) :
    forValues2 env it (.int s) (.binary .sle (.genvarRef it) (.paramRef p none)) (.unary .inc (.genvarRef it)) =
      .ok (intRange s (nvalOf env p + 1 - s).toNat) :=
  forValues2_up_nval (c := .le) (.inr rfl) (procStepDelta2_inc env it) h hne s

/-- `for (it = s; it < P; it = it + 1)` against a typed `int` parameter `P`. -/
theorem forValues2_slt_nval_add {env : IEnv} {it p : String} (h : nvalInt env p = true) (hne : p ≠ it) (s : Int) :
    forValues2 env it (.int s) (.binary .slt (.genvarRef it) (.paramRef p none))
        (.binary (.m0 .add) (.genvarRef it) (.int 1)) = .ok (intRange s (nvalOf env p - s).toNat) :=
  forValues2_up_nval (c := .lt) (.inl rfl) (procStepDelta2_add_one env it) h hne s

/-- `for (it = s; it <= P; it = it + 1)` against a typed `int` parameter `P`. -/
theorem forValues2_sle_nval_add {env : IEnv} {it p : String} (h : nvalInt env p = true) (hne : p ≠ it) (s : Int) :
    forValues2 env it (.int s) (.binary .sle (.genvarRef it) (.paramRef p none))
        (.binary (.m0 .add) (.genvarRef it) (.int 1)) = .ok (intRange s (nvalOf env p + 1 - s).toNat) :=
  forValues2_up_nval (c := .le) (.inr rfl) (procStepDelta2_add_one env it) h hne s

end LeanModels.Sv.Loop2

open LeanModels.Sv LeanModels.Sv.Kernel in
/-- The instantiation pass: the route's `do` block evaluated through its definitions' equation lemmas. -/
macro "sv_seq_inst_pass" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" " at " h:ident : tactic =>
  `(tactic| simp (config := {maxSteps := 4000000, decide := true}) [LeanModels.Sv.bindParamsRes,
      LeanModels.Sv.bindPackageParams, LeanModels.Sv.bindPackageEnums, LeanModels.Sv.bindLocals,
      LeanModels.Sv.bindEnums, LeanModels.Sv.typedParamWidthsE, LeanModels.Sv.Kernel.coreMemGeneratedDeclsList,
      LeanModels.Sv.Kernel.coreMemSubstDecl, LeanModels.Sv.Kernel.coreMemSubstName,
      LeanModels.Sv.Kernel.coreMemDeclInitializers,
      LeanModels.Sv.Kernel.coreMemLocalDeclsProc, LeanModels.Sv.Kernel.coreMemLocalDeclsStmt,
      LeanModels.Sv.Kernel.coreMemLocalDeclsList, LeanModels.Sv.Kernel.coreMemLocalDeclsCase,
      LeanModels.Sv.Kernel.coreMemExpandList, LeanModels.Sv.bindParams, LeanModels.Sv.declConstType,
      LeanModels.Sv.PType.width_packed_cons, LeanModels.Sv.PType.width_packed_nil, LeanModels.Sv.PDim.width,
      LeanModels.Sv.IEnv.bindNVal, LeanModels.Sv.IEnv.withPDims, LeanModels.Sv.Kernel.coreMemDeclNamesUnique,
      LeanModels.Sv.Kernel.coreMemMetadataDecls, LeanModels.Sv.Kernel.coreMemMetadataDecl,
      LeanModels.Sv.Kernel.coreMemMetadataType, LeanModels.Sv.Kernel.coreMemMetadataIsOutput,
      LeanModels.Sv.Kernel.coreMemFirstUnsupportedOther,
      LeanModels.Sv.Kernel.buildScalarDecls1, LeanModels.Sv.Kernel.instScalarDecl1, LeanModels.Sv.buildElems,
      LeanModels.Sv.Kernel.buildMemDecls1, LeanModels.Sv.PDecl.memShapeWithId?, LeanModels.Sv.evalMemDim,
      LeanModels.Sv.Kernel.buildAggDecls1, LeanModels.Sv.Kernel.PDecl.aggregateType?,
      LeanModels.Sv.Kernel.coreMemResolvedNetNames,
      LeanModels.Sv.Kernel.coreMemNetDecls, LeanModels.Sv.Kernel.CoreMemProc.ofPProcessAt,
      LeanModels.Sv.Kernel.CoreMemProc.ofPProcess, LeanModels.Sv.dimTable, LeanModels.Sv.dimTableStep,
      LeanModels.Sv.evalDims, LeanModels.Sv.evalInt, LeanModels.Sv.Kernel.seqE_except_ok_bind,
      LeanModels.Sv.Kernel.seqE_except_mapError_ok, LeanModels.Sv.Kernel.seqE_except_pure, List.lookup,
      LeanModels.Sv.Kernel.CoreMemDesign.compileAssigns, LeanModels.Sv.Kernel.CoreMemDesign.compileCombReads,
      LeanModels.Sv.Kernel.CoreMemDesign.compileImplicitReads, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
      LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf,
      LeanModels.Sv.Kernel.coreMemClockResetViol_none, LeanModels.Sv.Kernel.coreMemDropGeneratedNetMarkers,
      LeanModels.Sv.Kernel.coreMemGeneratedNetAllowed, LeanModels.Sv.Kernel.coreMemNetMetadataAllowed,
      LeanModels.Sv.Kernel.coreMemNetDriverAllowed,
      LeanModels.Sv.Kernel.coreMemEventSourceMultiWriteViol, LeanModels.Sv.Kernel.coreMemFirstRepeatedEventSource,
      LeanModels.Sv.Kernel.coreMemEventSources, LeanModels.Sv.Kernel.coreMemSourceWrittenTwiceInBody,
      LeanModels.Sv.Kernel.coreMemWritesNameTwice, LeanModels.Sv.Kernel.coreMemProcWrites,
      LeanModels.Sv.Kernel.coreMemStmtWrites, LeanModels.Sv.Kernel.coreMemStmtWritesList,
      LeanModels.Sv.Kernel.coreMemEdgeBlockingReadRaceViol,
      LeanModels.Sv.Kernel.coreMemEdgeBlockingReadRace,
      LeanModels.Sv.Kernel.coreMemEdgeBlockingReadRaceAt,
      LeanModels.Sv.Kernel.coreMemEdgeBlockingReadRacePair,
      LeanModels.Sv.Kernel.coreMemHasCommonEventSource,
      LeanModels.Sv.Kernel.coreMemPProcessEdgeSources,
      LeanModels.Sv.Kernel.coreMemPProcessReadNames,
      LeanModels.Sv.Kernel.coreMemAssignSources,
      LeanModels.Sv.Kernel.coreMemReadNamesThroughAssign,
      LeanModels.Sv.Kernel.coreMemEdgeBlockingReadRacePairThroughAssign,
      LeanModels.Sv.Kernel.coreMemEdgeBlockingReadRaceAtThroughAssign,
      LeanModels.Sv.Kernel.coreMemEdgeBlockingReadRaceThroughAssignFrom,
      LeanModels.Sv.Kernel.coreMemEdgeBlockingReadRaceThroughAssign,
      LeanModels.Sv.Kernel.coreMemEdgeMultipleWriteViol,
      LeanModels.Sv.Kernel.coreMemEdgeMultipleWrite,
      LeanModels.Sv.Kernel.coreMemEdgeMultipleWriteAt,
      LeanModels.Sv.Kernel.coreMemEdgeMultipleWritePair,
      LeanModels.Sv.Kernel.coreMemEdgeMultipleWriteThroughAssign,
      LeanModels.Sv.Kernel.coreMemEdgeMultipleWriteThroughAssignFrom,
      LeanModels.Sv.Kernel.coreMemEdgeMultipleWriteAtThroughAssign,
      LeanModels.Sv.Kernel.coreMemEdgeMultipleWritePairThroughAssign,
      LeanModels.Sv.Kernel.coreMemHasCommonEventSource,
      LeanModels.Sv.Kernel.coreMemHasCommonEventSourceThroughAssign,
      LeanModels.Sv.Kernel.coreMemPProcessEdgeEvents,
      LeanModels.Sv.Kernel.coreMemEventEdgesOverlap,
      LeanModels.Sv.Kernel.coreMemEventSourcesThroughAssign,
      LeanModels.Sv.Kernel.coreMemReactiveDriverSources,
      LeanModels.Sv.Kernel.coreMemDriverSources,
      LeanModels.Sv.Kernel.coreMemReadNamesThroughDrivers,
      LeanModels.Sv.Kernel.coreMemProcWriteLhss,
      LeanModels.Sv.Kernel.coreMemStmtWriteLhss,
      LeanModels.Sv.Kernel.coreMemStmtWriteLhssList,
      LeanModels.Sv.Kernel.coreMemCaseWriteLhss,
      LeanModels.Sv.Kernel.coreMemLhsMayOverlap,
      LeanModels.Sv.Kernel.coreMemLhsRoot,
      LeanModels.Sv.Kernel.coreMemCombSelfReadViol,
      LeanModels.Sv.Kernel.coreMemStmtReadBeforeWritesFrom,
      LeanModels.Sv.Kernel.coreMemStmtReadBeforeWritesListFrom,
      LeanModels.Sv.Kernel.coreMemPreemptiveBlockingViolReport,
      LeanModels.Sv.Kernel.coreMemPreemptiveBlockingViol,
      LeanModels.Sv.Kernel.coreMemPreemptiveBlockingViolAt,
      LeanModels.Sv.Kernel.coreMemPreemptiveBlockingPair,
      LeanModels.Sv.Kernel.coreMemPProcessAllReadNames,
      LeanModels.Sv.Kernel.coreMemPProcessReactive,
      LeanModels.Sv.Kernel.coreMemCaseWrites, LeanModels.Sv.Kernel.coreMemSourceHasBlockingWrite,
      LeanModels.Sv.Kernel.coreMemProcBlockingWrites, LeanModels.Sv.Kernel.coreMemStmtBlockingWrites,
      LeanModels.Sv.Kernel.coreMemStmtBlockingWritesList, LeanModels.Sv.Kernel.coreMemCaseBlockingWrites,
      LeanModels.Sv.Kernel.coreMemLatchSelfReadViol,
      LeanModels.Sv.Kernel.coreMemHasEventProcess,
      LeanModels.Sv.Kernel.coreMemEventSelfReadViol,
      LeanModels.Sv.Kernel.coreMemFirstTimeZeroEventSourceFor,
      LeanModels.Sv.Kernel.coreMemSourceWrittenAtTimeZeroFor,
      LeanModels.Sv.Kernel.coreMemTimeZeroSourceWritesFor,
      LeanModels.Sv.Kernel.coreMemPortAliasAtTimeZero,
      LeanModels.Sv.Kernel.coreMemTimeZeroSourceWrites,
      LeanModels.Sv.Kernel.coreMemTimeZeroProcWrites,
      LeanModels.Sv.Kernel.coreMemInputPortB,
      LeanModels.Sv.Kernel.coreMemHasTimeZeroWriter,
      LeanModels.Sv.Kernel.coreMemTimeZeroEventSourceViol, LeanModels.Sv.Kernel.coreMemFirstTimeZeroEventSource,
      LeanModels.Sv.Kernel.coreMemPAssignMemoryTopoB, LeanModels.Sv.Kernel.coreMemHasEdgeProc,
      LeanModels.Sv.Kernel.coreMemPAssignTarget,
      LeanModels.Sv.Kernel.coreMemPAssignValue, LeanModels.Sv.Kernel.coreMemPAssignUsesMemory,
      LeanModels.Sv.Kernel.coreMemPAssignTargets, LeanModels.Sv.Kernel.coreMemPExprHasMemory,
      LeanModels.Sv.Kernel.coreMemPExprHasMemoryList, LeanModels.Sv.Kernel.coreMemPLhsHasMemory,
      LeanModels.Sv.Kernel.coreMemPLhsHasMemoryList, LeanModels.Sv.Kernel.coreMemCombDependencyViol,
      LeanModels.Sv.Kernel.coreMemReactiveDependencyViol, LeanModels.Sv.Kernel.coreMemAssignReactiveChainViol,
      LeanModels.Sv.Kernel.coreMemAssignReactiveChainViolAt, LeanModels.Sv.Kernel.coreMemReactiveProc,
      LeanModels.Sv.Kernel.coreMemReactiveWrites, LeanModels.Sv.Kernel.coreMemReactiveReads,
      LeanModels.Sv.Kernel.coreMemReactiveLaterWrites, LeanModels.Sv.Kernel.coreMemFirstReadIn,
      LeanModels.Sv.Kernel.coreMemStmtReadNames, LeanModels.Sv.Kernel.coreMemStmtReadNamesList,
      LeanModels.Sv.Kernel.coreMemCaseReadNames, LeanModels.Sv.Kernel.coreMemLhsReadNames,
      LeanModels.Sv.Kernel.coreMemLhsReadNamesList, LeanModels.Sv.Kernel.coreMemSignalNames,
      LeanModels.Sv.Kernel.coreMemSignalNamesList,
      $ls,*] at $h:ident)

/-- The arithmetic pass: side conditions on the parameters, by `omega` from the context. -/
macro "sv_seq_arith_pass" " at " h:ident : tactic =>
  `(tactic| simp (disch := omega) only [LeanModels.Sv.CombView.canonInt32_of_bounds,
      LeanModels.Sv.Kernel.seqE_natAbs_sub_one_add_one, LeanModels.Sv.Kernel.seqE_natAbs_sub_one,
      Nat.sub_add_cancel] at $h:ident)

/-- The instantiation pass with the sized constant expressions (a parameter of an unsigned type, the condition of a
conditional generate construct) and the route's generate expansion of a conditional arm. Run only on an instantiation
the first pass leaves short of its normal form, so a design without these constructs costs what it did. -/
macro "sv_seq_inst_pass2" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" " at " h:ident : tactic =>
  `(tactic| sv_seq_inst_pass [$ls,*, LeanModels.Sv.evalSized, LeanModels.Sv.ctype,
      LeanModels.Sv.PExpr.pushedTarget, LeanModels.Sv.SymBinOp.constClass, LeanModels.Sv.Kernel.seqE_evalAt_int,
      LeanModels.Sv.Kernel.seqE_evalAt_param, LeanModels.Sv.Kernel.seqE_evalAt_sub,
      LeanModels.Sv.Kernel.seqE_evalAt_add, LeanModels.Sv.Kernel.seqE_evalAt_mul,
      LeanModels.Sv.Kernel.seqE_evalAt_eq, LeanModels.Sv.Kernel.seqE_evalAt_ne, LeanModels.Sv.Kernel.seqE_evalAt_slt,
      LeanModels.Sv.Kernel.seqE_evalAt_sle, LeanModels.Sv.Kernel.seqE_evalAt_sgt, LeanModels.Sv.Kernel.seqE_evalAt_sge,
      LeanModels.Sv.Kernel.seqE_evalAt_lt, LeanModels.Sv.Kernel.seqE_evalAt_le, LeanModels.Sv.Kernel.seqE_evalAt_gt,
      LeanModels.Sv.Kernel.seqE_evalAt_ge, LeanModels.Sv.evalGenGuard,
      LeanModels.Sv.Kernel.coreMemExpandItem, LeanModels.Sv.Kernel.coreMemGeneratedDeclsItem,
      LeanModels.Sv.Kernel.coreMemBindVals, LeanModels.Sv.Kernel.coreMemScopeEnv,
      LeanModels.Sv.Kernel.coreMemSubstProcess, LeanModels.Sv.Kernel.coreMemSubstStmt,
      LeanModels.Sv.Kernel.coreMemSubstStmtOpt, LeanModels.Sv.Kernel.coreMemSubstStmtList,
      LeanModels.Sv.Kernel.coreMemSubstCaseItems, LeanModels.Sv.Kernel.coreMemSubstExpr,
      LeanModels.Sv.Kernel.coreMemSubstLhs, LeanModels.Sv.Kernel.coreMemSubstDecl,
      LeanModels.Sv.Kernel.coreMemSubstType, LeanModels.Sv.Kernel.coreMemSubstDim, and_assoc] at $h:ident)

/-- The arithmetic pass after `sv_seq_inst_pass2`: the unsigned 32-bit wraps and the generate conditions, by `omega`
from the context. -/
macro "sv_seq_arith_pass2" " at " h:ident : tactic =>
  `(tactic| simp (disch := omega) only [LeanModels.Sv.CombView.canonInt32_of_bounds,
      LeanModels.Sv.CombView.convertConst32, LeanModels.Sv.CombView.convertConst1_ite,
      LeanModels.Sv.Kernel.seqE_ite_ne_zero, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, if_pos, if_neg,
      LeanModels.Sv.Kernel.seqE_canonU32_of_bounds, LeanModels.Sv.Kernel.seqE_convertU32_of_bounds,
      LeanModels.Sv.Kernel.seqE_natAbs_sub_one_add_one, LeanModels.Sv.Kernel.seqE_natAbs_sub_one,
      LeanModels.Sv.Kernel.seqE_natAbs_add_sub_one_add_one, Nat.sub_add_cancel] at $h:ident)

open Lean Elab Tactic Meta in
/-- Succeeds when `h` is an instantiation in normal form, `<the design as a structure literal> = E` (then no further
instantiation pass is run: a design without a conditional generate construct costs one pass, as before). -/
elab "sv_seq_inst_done " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let t := (← instantiateMVars d.type).consumeMData
  unless t.isAppOfArity ``Eq 3 &&
      (t.getArg! 1).consumeMData.isAppOf ``LeanModels.Sv.Kernel.CoreMemDesign.mk do
    throwError "sv_seq_inst: the instantiation is not in normal form"

/-- **`sv_seq_inst [X.e, X.pdesign] at hE`**: `hE : X.e P… = .ok E` becomes `hE : <normal form> = E`. -/
macro "sv_seq_inst" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" " at " h:ident : tactic =>
  `(tactic| (
    simp only [LeanModels.Sv.Kernel.PDesign.instantiateE2, LeanModels.Sv.Kernel.PDesign.instantiateCoreMem,
      LeanModels.Sv.Kernel.PDesign.instantiateCoreMemFrom, $ls,*] at $h:ident
    sv_seq_inst_pass [$ls,*] at $h:ident
    (try sv_seq_arith_pass at $h:ident)
    -- short of the normal form: the sized constant expressions and the conditional generate constructs (a condition,
    -- decided by the arithmetic pass, opens the chosen arm to the next round)
    repeat (
      fail_if_success (sv_seq_inst_done $h:ident)
      sv_seq_inst_pass2 [$ls,*] at $h:ident
      (try sv_seq_arith_pass2 at $h:ident))))

/-! The profile's conjuncts on a normal form (the arguments of `SeqProfile.of_B` / `SeqProfileI.of_B` after the edge
view's `rfl`), one tactic each: `sv_seq_profile`, `sv_seq_profileI` and the structure stage's diagnosis
(`SeqCycleStages.runProfile`, which names the conjunct that fails) use the same ones. -/

/-- The memories of the profile (`memOkB`). -/
macro "sv_seq_prof_mems" : tactic =>
  `(tactic| simp (config := {decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.memOkB])

/-- Distinct declaration names. -/
macro "sv_seq_prof_names" : tactic => `(tactic| simp)

/-- Every declaration 4-state (`AllFour`). -/
macro "sv_seq_prof_four" : tactic => `(tactic| simp [LeanModels.Sv.Kernel.AllFour])

/-- No resolved net (`resolvedNets = []`). -/
macro "sv_seq_prof_resolved" : tactic => `(tactic| simp [LeanModels.Sv.Kernel.coreMemResolvedNetNames])

/-- Every process in the single-clock profile (`procsOkFrom`); a supported loop header is evaluated in closed form
(`Loop2.forValues2_slt`/`_sle`) and its runtime fuel is allocated by the executor. -/
macro "sv_seq_prof_procs" : tactic =>
  `(tactic| (simp (config := {decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.procsOkFrom,
      LeanModels.Sv.Kernel.CoreMemDesign.procOkB, LeanModels.Sv.Kernel.coreMemEventEdge?, LeanModels.Sv.Kernel.CoreMemEvent.clockEdge?,
      LeanModels.Sv.PStmt.edgeOkB, LeanModels.Sv.PStmt.optEdgeOkB,
      LeanModels.Sv.PLhs.hasCall, LeanModels.Sv.PLhs.hasCallList,
      LeanModels.Sv.PStmt.listEdgeOkB, LeanModels.Sv.PStmt.itemsEdgeOkB, LeanModels.Sv.PStmt.need,
      LeanModels.Sv.PStmt.optNeed, LeanModels.Sv.PStmt.listNeed, LeanModels.Sv.PStmt.itemsNeed,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead, LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCallList, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
      LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf,
      LeanModels.Sv.PStmt.loopBodyB, LeanModels.Sv.PStmt.optLoopBodyB, LeanModels.Sv.PStmt.listLoopBodyB,
      LeanModels.Sv.PStmt.itemsLoopBodyB, LeanModels.Sv.Kernel.loopTrips, LeanModels.Sv.Loop2.forValues2_slt,
      LeanModels.Sv.Loop2.forValues2_sle,
      LeanModels.Sv.Loop2.forValues2_slt_nval, LeanModels.Sv.Loop2.forValues2_sle_nval,
      LeanModels.Sv.Loop2.forValues2_slt_nval_add, LeanModels.Sv.Loop2.forValues2_sle_nval_add,
      LeanModels.Sv.Loop2.forValues2_slt_add, LeanModels.Sv.Loop2.forValues2_sle_add, LeanModels.Sv.Loop2.nvalOf, LeanModels.Sv.Loop2.nvalInt, LeanModels.Sv.Loop2.envVal, LeanModels.Sv.intRange_length, List.lookup]
    <;> omega))

/-- Every process in the instant profile (`procsOkIFrom`). -/
macro "sv_seq_prof_procsI" : tactic =>
  `(tactic| (simp (config := {decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.procsOkIFrom,
      LeanModels.Sv.Kernel.CoreMemDesign.procOkIB, LeanModels.Sv.Kernel.coreMemEventEdge?, LeanModels.Sv.Kernel.CoreMemEvent.clockEdge?,
      LeanModels.Sv.PStmt.edgeOkB, LeanModels.Sv.PStmt.optEdgeOkB,
      LeanModels.Sv.PLhs.hasCall, LeanModels.Sv.PLhs.hasCallList,
      LeanModels.Sv.PStmt.listEdgeOkB, LeanModels.Sv.PStmt.itemsEdgeOkB, LeanModels.Sv.PStmt.need,
      LeanModels.Sv.PStmt.optNeed, LeanModels.Sv.PStmt.listNeed, LeanModels.Sv.PStmt.itemsNeed,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead, LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCallList, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
      LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf,
      LeanModels.Sv.PStmt.loopBodyB, LeanModels.Sv.PStmt.optLoopBodyB, LeanModels.Sv.PStmt.listLoopBodyB,
      LeanModels.Sv.PStmt.itemsLoopBodyB, LeanModels.Sv.Kernel.loopTrips, LeanModels.Sv.Loop2.forValues2_slt,
      LeanModels.Sv.Loop2.forValues2_sle,
      LeanModels.Sv.Loop2.forValues2_slt_nval, LeanModels.Sv.Loop2.forValues2_sle_nval,
      LeanModels.Sv.Loop2.forValues2_slt_nval_add, LeanModels.Sv.Loop2.forValues2_sle_nval_add,
      LeanModels.Sv.Loop2.forValues2_slt_add, LeanModels.Sv.Loop2.forValues2_sle_add, LeanModels.Sv.Loop2.nvalOf, LeanModels.Sv.Loop2.nvalInt, LeanModels.Sv.Loop2.envVal, LeanModels.Sv.intRange_length, List.lookup]
    <;> omega))

/-- **`sv_seq_profile`**: the clocked profile of a normal form, decided by `simp` (any number of processes). -/
macro "sv_seq_profile" : tactic =>
  `(tactic| exact LeanModels.Sv.Kernel.CoreMemDesign.SeqProfile.of_B (by sv_seq_prof_mems) rfl
      (by sv_seq_prof_names) (by sv_seq_prof_four) (by sv_seq_prof_resolved) (by sv_seq_prof_procs))

/-- **`sv_seq_profileI`**: the instant profile (any clocks, either edge) of a normal form, decided by `simp`. -/
macro "sv_seq_profileI" : tactic =>
  `(tactic| exact LeanModels.Sv.Kernel.CoreMemDesign.SeqProfileI.of_B (by sv_seq_prof_mems) rfl
      (by sv_seq_prof_names) (by sv_seq_prof_four) (by sv_seq_prof_resolved) (by sv_seq_prof_procsI))

/-- **`sv_seq_obligations`**: the obligations of the clocked profile (`seqOblB`) on a normal form, decided by `simp`
(the topological order on the compiled expressions: `instExpr2` evaluated, `Expr2.idents` read). -/
macro "sv_seq_obligations" : tactic =>
  `(tactic| simp (config := {maxSteps := 4000000, decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.seqOblB,
      LeanModels.Sv.Kernel.CoreMemDesign.seqOblI, LeanModels.Sv.Kernel.CoreMemDesign.oblInputsUndriven,
      LeanModels.Sv.Kernel.CoreMemDesign.oblSources, LeanModels.Sv.Kernel.CoreMemDesign.oblNoSourceRead,
      LeanModels.Sv.Kernel.CoreMemProc.sourceReadOk, LeanModels.Sv.Kernel.CoreMemDesign.sources,
      LeanModels.Sv.Kernel.CoreMemDesign.events, LeanModels.Sv.Kernel.CoreMemProc.events,
      LeanModels.Sv.Kernel.coreMemEventEdge?, LeanModels.Sv.Kernel.CoreMemEvent.clockEdge?,
      LeanModels.Sv.Kernel.CoreMemEdge.events, LeanModels.Sv.Kernel.CoreMemEdge.clockEvent,
      LeanModels.Sv.Kernel.CoreMemEdge.resetEvent?, LeanModels.Sv.Kernel.CoreMemDesign.inputPorts,
      LeanModels.Sv.Kernel.CoreMemDesign.driven, LeanModels.Sv.Kernel.CoreMemDesign.inputNamesL,
      LeanModels.Sv.Kernel.CoreMemDesign.oblDrivers, LeanModels.Sv.Kernel.CoreMemDesign.oblNoInputWrite,
      LeanModels.Sv.Kernel.CoreMemDesign.oblNoClockRead, LeanModels.Sv.Kernel.CoreMemDesign.oblReset,
      LeanModels.Sv.Kernel.CoreMemDesign.oblEdgeOrder, LeanModels.Sv.Kernel.CoreMemDesign.oblConverted,
      LeanModels.Sv.Kernel.CoreMemDesign.oblClockInput,
      LeanModels.Sv.Kernel.CoreMemProc.targets, LeanModels.Sv.Kernel.CoreMemProc.reads,
      LeanModels.Sv.Kernel.CoreMemProc.reset?, LeanModels.Sv.Kernel.CoreMemProc.blocking,
      LeanModels.Sv.Kernel.CoreMemProc.isEdge, LeanModels.Sv.Kernel.CoreMemProc.nbaWholeP,
      LeanModels.Sv.PStmt.nbaWhole, LeanModels.Sv.PStmt.optNbaWhole, LeanModels.Sv.PStmt.listNbaWhole,
      LeanModels.Sv.PStmt.itemsNbaWhole, LeanModels.Sv.Kernel.CoreMemDesign.topoC,
      LeanModels.Sv.Kernel.CoreMemDesign.topoFrom, LeanModels.Sv.Kernel.assignTargets,
      LeanModels.Sv.Kernel.CoreMemDesign.compileAssigns, LeanModels.Sv.Expr2.idents, LeanModels.Sv.Expr2.listIdents,
      LeanModels.Sv.PExpr.sigNames, LeanModels.Sv.PExpr.sigNamesList, LeanModels.Sv.PLhs.baseNames,
      LeanModels.Sv.PLhs.baseNamesList, LeanModels.Sv.PLhs.indexNames, LeanModels.Sv.PLhs.indexNamesList,
      LeanModels.Sv.PStmt.writes, LeanModels.Sv.PStmt.optWrites, LeanModels.Sv.PStmt.listWrites,
      LeanModels.Sv.PStmt.itemsWrites, LeanModels.Sv.PStmt.hasBlocking, LeanModels.Sv.PStmt.optHasBlocking,
      LeanModels.Sv.PStmt.listHasBlocking, LeanModels.Sv.PStmt.itemsHasBlocking,
      LeanModels.Sv.PStmt.readNames, LeanModels.Sv.PStmt.optReadNames, LeanModels.Sv.PStmt.listReadNames,
      LeanModels.Sv.PStmt.itemsReadNames,
      LeanModels.Sv.Kernel.CoreMemProc.unconverted, LeanModels.Sv.PExpr.unconverted, LeanModels.Sv.PExpr.unconvertedList,
      LeanModels.Sv.PStmt.unconverted, LeanModels.Sv.PStmt.optUnconverted, LeanModels.Sv.PStmt.listUnconverted,
      LeanModels.Sv.PStmt.itemsUnconverted, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
      LeanModels.Sv.Kernel.CoreMemDesign.readsV, LeanModels.Sv.Kernel.CoreMemDesign.readsIdxV,
      LeanModels.Sv.Kernel.CoreMemDesign.readsListV, LeanModels.Sv.Kernel.CoreMemDesign.memDecl?,
      LeanModels.Sv.Kernel.CoreMemDesign.widthsOf, LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCallList,
      LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf,
      LeanModels.Sv.instExpr2, LeanModels.Sv.dynPartPlan, LeanModels.Sv.evalInt,
      LeanModels.Sv.arrayPartRead, LeanModels.Sv.arrayPartGeom, LeanModels.Sv.arrayDims,
      LeanModels.Sv.walkIndices, LeanModels.Sv.partLabels, LeanModels.Sv.labelOffset, LeanModels.Sv.dimsStride,
      LeanModels.Sv.dimCount, List.lookup, LeanModels.Sv.ctxOpWidth2, LeanModels.Sv.rigidMax2,
      LeanModels.Sv.selfWidth2, LeanModels.Sv.fitExpr2, LeanModels.Sv.rigidExpr,
      LeanModels.Sv.PExpr.ctxPropagates, LeanModels.Sv.PExpr.constLeaf, LeanModels.Sv.PExpr.negGenvarWidened,
      LeanModels.Sv.PExpr.signedCast, LeanModels.Sv.Kernel.seqE_except_ok_bind,
      LeanModels.Sv.Kernel.seqE_except_pure])

/-- **`sv_seq_ports`**: the ports of a normal form. -/
macro "sv_seq_ports" : tactic =>
  `(tactic| simp [LeanModels.Sv.Kernel.CoreMemDesign.inputPorts, LeanModels.Sv.Kernel.CoreMemDesign.outputPorts])

/-- The evaluation pass of a cycle at a side-condition search depth: the view functions and the route's evaluator
unfolded. -/
macro "sv_seq_eval_pass_at " d:num " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : conv =>
  `(conv| simp (config := {maxSteps := 4000000, decide := true, maxDischargeDepth := $d})
      [-LeanModels.Sv.Res.bind_eq_ok,
      LeanModels.Sv.Kernel.CoreMemDesign.cycleV, LeanModels.Sv.Kernel.CoreMemDesign.slotV,
      LeanModels.Sv.Kernel.CoreMemDesign.settleV, LeanModels.Sv.Kernel.CoreMemDesign.settleRaw,
      LeanModels.Sv.Kernel.CoreMemDesign.matV, LeanModels.Sv.Kernel.CoreMemDesign.edgesV,
      LeanModels.Sv.Kernel.coreMemEventEdge?, LeanModels.Sv.Kernel.CoreMemEvent.clockEdge?,
      LeanModels.Sv.Kernel.CoreMemEdge.fires, LeanModels.Sv.Kernel.CoreMemDesign.execV,
      LeanModels.Sv.Kernel.CoreMemDesign.execListV, LeanModels.Sv.Kernel.CoreMemDesign.execOptV,
      LeanModels.Sv.Kernel.CoreMemDesign.execItemsV, LeanModels.Sv.Kernel.CoreMemDesign.caseHitsV,
      LeanModels.Sv.Kernel.CoreMemDesign.setV, LeanModels.Sv.Kernel.CoreMemDesign.writeLhsV,
      LeanModels.Sv.caseHit, LeanModels.Sv.Kernel.caseClaimOk, LeanModels.Sv.Kernel.scalarNbaWindows,
      LeanModels.Sv.Kernel.scalarNbaWindows.go, LeanModels.Sv.resolveConcatLhs2, LeanModels.Sv.resolveLhs2,
      LeanModels.Sv.writeConcatLhs2, LeanModels.Sv.writeConcatLhs2.go,
      LeanModels.Sv.Kernel.CoreMemDesign.scalarLhs2, LeanModels.Sv.instLhs2, LeanModels.Sv.instLhsLeaf2,
      LeanModels.Sv.Kernel.CoreMemDesign.evalV, LeanModels.Sv.Kernel.CoreMemDesign.evalListV,
      LeanModels.Sv.Kernel.CoreMemDesign.evalIdxV, LeanModels.Sv.Kernel.CoreMemDesign.evalScalarV,
      LeanModels.Sv.Kernel.CoreMemDesign.widthsOf, LeanModels.Sv.Kernel.CoreMemDesign.scalarTarget,
      LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?, LeanModels.Sv.Kernel.Elab.resolve,
      LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf, LeanModels.Sv.applyInputs2,
      LeanModels.Sv.Kernel.Elab.toDesign2, LeanModels.Sv.Kernel.lowEntry, LeanModels.Sv.Kernel.highEntry,
      LeanModels.Sv.Kernel.seqE_commit_nil, LeanModels.Sv.Kernel.seqE_commit_cons, LeanModels.Sv.Kernel.Val.ofLVec, LeanModels.Sv.Kernel.VType.ofDecl,
      LeanModels.Sv.Kernel.VType.conv, LeanModels.Sv.Kernel.declFallback, LeanModels.Sv.Res.ok_bind,
      LeanModels.Sv.Kernel.seqE_except_ok_bind, LeanModels.Sv.SvState.lookup, LeanModels.Sv.SvState.set,
      LeanModels.Sv.readSignal, LeanModels.Sv.SvState.bit0, LeanModels.Sv.evalPure2_ident,
      LeanModels.Sv.evalPure2_slice, LeanModels.Sv.instExpr2, LeanModels.Sv.dynPartPlan, LeanModels.Sv.evalInt,
      LeanModels.Sv.arrayPartRead, LeanModels.Sv.arrayPartGeom, LeanModels.Sv.arrayDims,
      LeanModels.Sv.walkIndices, LeanModels.Sv.partLabels, LeanModels.Sv.labelOffset, LeanModels.Sv.dimsStride,
      LeanModels.Sv.dimCount, List.lookup, LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList, LeanModels.Sv.Kernel.seqE_isPosedge_l0,
      LeanModels.Sv.Kernel.seqE_bit0_zero, LeanModels.Sv.Kernel.seqE_bit0_one,
      LeanModels.Sv.Kernel.seqE_resizeU_resizeU, LeanModels.Sv.Kernel.seqE_resizeU_l0,
      LeanModels.Sv.Kernel.seqE_resizeU_l1, LeanModels.Sv.LVec.resizeU_of_width,
      LeanModels.Sv.Kernel.seqE_width_bit, LeanModels.Sv.ctxOpWidth2, LeanModels.Sv.rigidMax2,
      LeanModels.Sv.selfWidth2, LeanModels.Sv.fitExpr2, LeanModels.Sv.rigidExpr,
      LeanModels.Sv.PExpr.ctxPropagates, LeanModels.Sv.PExpr.constLeaf, LeanModels.Sv.PExpr.negGenvarWidened,
      LeanModels.Sv.PExpr.signedCast, LeanModels.Sv.Kernel.seqE_ite_ok, LeanModels.Sv.Kernel.seqE_ite_pair,
      LeanModels.Sv.Kernel.seqE_ite_cons, LeanModels.Sv.Kernel.seqE_commit_ite, LeanModels.Sv.Kernel.seqE_append_ite,
      LeanModels.Sv.Kernel.seqE_ite_append, LeanModels.Sv.Kernel.seqE_ite_fst, LeanModels.Sv.Kernel.seqE_ite_snd,
      LeanModels.Sv.Kernel.seqE_resizeU_ite, LeanModels.Sv.Kernel.seqE_width_ite,
      LeanModels.Sv.Kernel.seqE_insertAt_zero, LeanModels.Sv.Kernel.seqE_width_lit,
      LeanModels.Sv.Kernel.seqE_replVec_bit, LeanModels.Sv.LVec.replicate_l0, LeanModels.Sv.LVec.replicate_l1,
      LeanModels.Sv.LVec.width_replicate,
      LeanModels.Sv.Kernel.seqE_width_add, LeanModels.Sv.Kernel.CoreMemDesign.cycleMV,
      LeanModels.Sv.Kernel.CoreMemDesign.dataV, LeanModels.Sv.Kernel.CoreMemDesign.tick,
      LeanModels.Sv.Kernel.Instant.row, LeanModels.Sv.Kernel.Instant.rise, LeanModels.Sv.Kernel.Instant.fall,
      LeanModels.Sv.Kernel.CoreMemDesign.memDecl?, List.find?, LeanModels.Sv.Kernel.CoreMemDecl.readV,
      LeanModels.Sv.Kernel.CoreMemDecl.issueV, LeanModels.Sv.Kernel.memNone, LeanModels.Sv.Kernel.commitMemV_nil,
      LeanModels.Sv.Kernel.commitMemV_memIss, LeanModels.Sv.Kernel.seqE_commitMemV_memIss,
      LeanModels.Sv.Kernel.seqE_commitMemV_ite, LeanModels.Sv.Kernel.seqE_memRd_ite,
      LeanModels.Sv.Kernel.seqE_memIss_ite, LeanModels.Sv.Kernel.memRd_memWrite,
      LeanModels.Sv.Kernel.MemShape.convert, LeanModels.Sv.Kernel.seqE_memRd_width,
      -LeanModels.Sv.evalPure2_index, LeanModels.Sv.Kernel.seqE_evalPure2_index,
      LeanModels.Sv.Kernel.seqE_resolveLhs2_index, LeanModels.Sv.evalExpr2_eq_evalPure2, LeanModels.Sv.Expr2.size,
      LeanModels.Sv.instIndex2,
      LeanModels.Sv.PStmt.loopBodyB, LeanModels.Sv.PStmt.optLoopBodyB, LeanModels.Sv.PStmt.listLoopBodyB,
      LeanModels.Sv.PStmt.itemsLoopBodyB, LeanModels.Sv.Loop2.forValues2_slt, LeanModels.Sv.Loop2.forValues2_sle,
      LeanModels.Sv.Loop2.forValues2_slt_nval, LeanModels.Sv.Loop2.forValues2_sle_nval,
      LeanModels.Sv.Loop2.forValues2_slt_nval_add, LeanModels.Sv.Loop2.forValues2_sle_nval_add,
      LeanModels.Sv.Loop2.forValues2_slt_add, LeanModels.Sv.Loop2.forValues2_sle_add, LeanModels.Sv.Loop2.nvalOf, LeanModels.Sv.Loop2.nvalInt,
      LeanModels.Sv.Loop2.envVal, LeanModels.Sv.IEnv.bindVal, LeanModels.Sv.Kernel.execLoopV_ok,
      LeanModels.Sv.Kernel.seqE_flatMap_nil,
      LeanModels.Sv.Kernel.commitMemV_flatMap_memIss, LeanModels.Sv.Kernel.commitMemV_flatMap_memIss_append,
      $ls,*])

/-- The evaluation pass of a cycle: the view functions and the route's evaluator unfolded. -/
macro "sv_seq_eval_pass" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : conv =>
  `(conv| sv_seq_eval_pass_at 2 [$ls,*])

open Lean Elab Tactic Conv in
/-- Succeeds when the term under `conv` holds a loop's write equation (`memWriteL`): the pass below runs only then, so
a cycle without a loop costs what it did. -/
elab "sv_seq_has_loop" : conv => do
  let lhs ← instantiateMVars (← getLhs)
  unless (lhs.find? (·.isConstOf ``LeanModels.Sv.Kernel.memWriteL)).isSome do
    throwError "sv_seq_cycle: no loop write equation in the cycle"

/-- The pass after a loop's write equation: a read of a memory a loop wrote (`memRd (memWriteL …)`) is of the element
width, from the width facts given; that needs a deeper side-condition search than the evaluation pass's (the widths of
the written memory, of the memory before it, of each written value). -/
macro "sv_seq_eval_loop" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : conv =>
  `(conv| (sv_seq_has_loop
           sv_seq_eval_pass_at 6 [$ls,*, LeanModels.Sv.Kernel.seqE_resizeU_memRd_memWriteL,
             LeanModels.Sv.Kernel.seqE_memWriteL_width, LeanModels.Sv.Kernel.seqE_memWrite_width, implies_true]))

/-- The arithmetic pass of a cycle: conditions and bounds on the parameters, by `omega`. -/
macro "sv_seq_eval_arith" : conv =>
  `(conv| simp (disch := omega) only [if_pos, if_neg, Nat.max_eq_left, Nat.max_eq_right, Int.min_eq_left,
      Int.min_eq_right, Int.max_eq_left,
      Int.max_eq_right, LeanModels.Sv.CombView.canonInt32_of_bounds,
      LeanModels.Sv.Kernel.seqE_canonU32_of_bounds, LeanModels.Sv.Kernel.seqE_convertU32_of_bounds,
      LeanModels.Sv.Kernel.seqE_natAbs_sub_one_add_one, LeanModels.Sv.Kernel.seqE_natAbs_sub_one,
      LeanModels.Sv.Kernel.seqE_natAbs_add_sub_one_add_one, Nat.sub_add_cancel])

/-- **`sv_seq_cycle h : E.cycleV clk v d using hE [facts]`**: `h : E.cycleV clk v d = <the computed pre and post
views>`, where `hE : <normal form> = E` comes from `sv_seq_inst`. -/
macro "sv_seq_cycle " h:ident " : " t:term " using " hE:ident " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    have $h := (rfl : $t = $t)
    conv at $h:ident =>
      rhs
      rw [← $hE:ident]
      try sv_seq_eval_pass [$ls,*]
      try sv_seq_eval_arith
      try sv_seq_eval_pass [$ls,*]
      try sv_seq_eval_arith
      try sv_seq_eval_pass [$ls,*]
      try sv_seq_eval_arith
      try sv_seq_eval_pass [$ls,*]
      try sv_seq_eval_loop [$ls,*]))
