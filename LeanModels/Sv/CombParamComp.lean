import Lean
import LeanModels.Sv.CombGenGuard

/-!
# The parameter stage, node by node (tac10)

At a symbolic parameter the tactics show the instantiation's environment (`PDesign.paramEnv2`) to agree with the
summary's valuation. The general route (`closeParamEnv`, CombViewTactic.lean) evaluates the whole stage symbolically and
rewrites the goal at every value it cannot compute: one decision of a `?:`, one wrapped intermediate value at a time, each
step rewriting the whole goal. For a localparam that is a sum of many `?:` (the Dadda record's stage count, 51 of them)
that is quadratic in the expression and ran out of every budget.

Here the localparams of a design are evaluated NODE BY NODE instead: for each node of an `int` localparam's initializer a
lemma states the instantiation's value of the node from the values of its operands (`evalAt` at the signed 32-bit type,
IEEE 1800-2023 §11.8.2, and the exact evaluator `evalIntExactRec` of an `int` target), each with the fact that the
node's value is a 32-bit value; the tactic (`closeParamEnvComp`) composes them bottom-up, sharing every sub-result, so the
cost is linear in the size of the expression. A 32-bit fact comes from numeric bounds of the node (`Bnd`), composed by
interval arithmetic from the operands' bounds (a parameter's bounds are shown by `omega` from the hypotheses in context).

The fragment: integer literals, parameters and earlier localparams bound as 32-bit `int`s (`IntB`), `+`, `-`, `*`
(the summary's `CE` admits a product only with a literal factor), `?:` whose condition is a comparison
`s< s<= s> s>= == !=` of two such expressions or such an expression itself. Everything else goes through the general
route. Each lemma is proved against `ctype`, `evalAt` and `evalIntExactRec` themselves; nothing about the instantiation is
assumed. Every arm of a `?:` is owed in the 32-bit range (the instantiation evaluates only the chosen one: a sufficient
condition, never an approximation of the value).

The values the lemmas produce are the summary's own terms (`CE.eval`'s unfolding, as `ceTerm` writes them), so the
agreement `hag` of each localparam is closed by the definitional check alone.
-/

namespace LeanModels.Sv
namespace CombView

/-- A value of the signed 32-bit range. -/
abbrev InR32 (v : Int) : Prop := -2147483648 ≤ v ∧ v < 2147483648

/-- `n` is bound in `env` as a 32-bit signed `int` of value `v`: in `vals` (a loop binding, or an `int` parameter outside
the exact mode), or in `nvals` at `(32, signed)` and not stale (how `paramEnv2` binds an `int` parameter or localparam). -/
def IntB (env : IEnv) (n : String) (v : Int) : Prop :=
  env.vals.lookup n = some v ∨ (env.vals.lookup n = none ∧ env.nvals.lookup n = some (v, 32, true) ∧ n ∉ env.stale)

theorem IntB.intVal {env : IEnv} {n : String} {v : Int} (h : IntB env n v) : env.intVal? n = some v := by
  rcases h with h | ⟨hv, hn, hs⟩
  · simp [IEnv.intVal?, h]
  · simp [IEnv.intVal?, hv, hn, hs]

/-- `IntB` from the environment's own lookups (the tactic shows them by `rfl` on the concrete environment) and an equation
of the bound value (a parameter's `canonInt 32 true x` is `x` in range). -/
theorem IntB.of_nvals (env : IEnv) (n : String) (x v : Int) (hv : env.vals.lookup n = none)
    (hn : env.nvals.lookup n = some (x, 32, true)) (hs : env.stale = []) (hx : x = v) : IntB env n v := by
  subst hx
  refine Or.inr ⟨hv, hn, ?_⟩
  rw [hs]
  simp

/-! ## The lemmas of the nodes -/

/-- The value of an `int` expression at the signed 32-bit type (`evalAt`), its type that type, and the expression of the
INT class (`isIntExact`, `isInt`). -/
def EA (env : IEnv) (e : PExpr) (v : Int) : Prop :=
  ctype env e = .ok (32, true) ∧ evalAt env (32, true) e = .ok v ∧ e.isIntExact env = true ∧ e.isInt env = true

/-- The value of the condition of a `?:` at its own type (a comparison at its 1-bit unsigned type, IEEE 1800-2023
§11.4.4; an `int` at the signed 32-bit type). -/
def EC (env : IEnv) (e : PExpr) (v : Int) : Prop :=
  ∃ ty, ctype env e = .ok ty ∧ evalAt env ty e = .ok v

/-- The value of an `int` expression in the exact evaluator of an `int` target (`evalIntExactRec`). -/
def EI (env : IEnv) (e : PExpr) (v : Int) : Prop :=
  e.isIntExact env = true ∧ e.isInt env = true ∧ evalIntExactRec env e = .ok v

private theorem max32 : max (32 : Nat) 32 = 32 := rfl

theorem cc1_one : convertConst 1 1 false 1 = 1 := by decide
theorem cc1_zero : convertConst 1 1 false 0 = 0 := by decide

theorem EA.int (env : IEnv) (v : Int) (h : InR32 v) : EA env (.int v) v := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  simp only [evalAt, convertConst32 h]

theorem EA.ref (env : IEnv) (n : String) (v : Int) (hb : IntB env n v) (h : InR32 v) :
    EA env (.paramRef n none) v := by
  rcases hb with hv | ⟨hv, hn, -⟩
  · exact ⟨by simp [ctype, hv], by simp [evalAt, hv, convertConst32 h], by simp [PExpr.isIntExact, hv],
      by simp [PExpr.isInt, hv]⟩
  · exact ⟨by simp [ctype, hv, hn], by simp [evalAt, hv, hn, convertConst32 h], by simp [PExpr.isIntExact, hv, hn],
      by simp [PExpr.isInt, hv, hn]⟩

/-- `+` of two `int`s (IEEE 1800-2023 §11.4.3): the sum, wrapped to 32 bits (`constArith`), is the sum in range. -/
theorem EA.add (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) (h : InR32 (a + b)) :
    EA env (.binary (.m0 .add) l r) (a + b) := by
  obtain ⟨hcl, hel, hil, hnl⟩ := hl
  obtain ⟨hcr, her, hir, hnr⟩ := hr
  refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]; rfl, ?_,
    by simp [PExpr.isIntExact, hil, hir], by simp [PExpr.isInt, hnl, hnr]⟩
  simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
  unfold_param_private
  rw [canonInt32_id h]

theorem EA.sub (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) (h : InR32 (a - b)) :
    EA env (.binary (.m0 .sub) l r) (a - b) := by
  obtain ⟨hcl, hel, hil, hnl⟩ := hl
  obtain ⟨hcr, her, hir, hnr⟩ := hr
  refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]; rfl, ?_,
    by simp [PExpr.isIntExact, hil, hir], by simp [PExpr.isInt, hnl, hnr]⟩
  simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
  unfold_param_private
  rw [canonInt32_id h]

/-- `*` of two `int`s, the envelope's `.m0 .mul` spelling. -/
theorem EA.mul0 (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) (h : InR32 (a * b)) :
    EA env (.binary (.m0 .mul) l r) (a * b) := by
  obtain ⟨hcl, hel, hil, hnl⟩ := hl
  obtain ⟨hcr, her, hir, hnr⟩ := hr
  refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]; rfl, ?_,
    by simp [PExpr.isIntExact, hil, hir], by simp [PExpr.isInt, hnl, hnr]⟩
  simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
  unfold_param_private
  rw [canonInt32_id h]

/-- `*` of two `int`s, the envelope's `.mul` spelling. -/
theorem EA.mul (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) (h : InR32 (a * b)) :
    EA env (.binary .mul l r) (a * b) := by
  obtain ⟨hcl, hel, hil, hnl⟩ := hl
  obtain ⟨hcr, her, hir, hnr⟩ := hr
  refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]; rfl, ?_,
    by simp [PExpr.isIntExact, hil, hir], by simp [PExpr.isInt, hnl, hnr]⟩
  simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
  unfold_param_private
  rw [canonInt32_id h]

/-- `c ? t : e` of two `int` arms (IEEE 1800-2023 §11.4.11): the condition at its own type, then only the arm it selects,
at the 32-bit type (`evalAt`). The value is the summary's `CE.eval` of a `cond`. -/
theorem EA.tern (env : IEnv) (c t e : PExpr) (x a b : Int) (hc : EC env c x) (ht : EA env t a) (he : EA env e b) :
    EA env (.ternary c t e) (if x = 0 then b else a) := by
  obtain ⟨ty, hcc, hec⟩ := hc
  obtain ⟨hct, het, hit, hnt⟩ := ht
  obtain ⟨hce, hee, hie, hne⟩ := he
  refine ⟨by simp only [ctype, hct, hce, Gen2.except_ok_bind]; rfl, ?_, by simp [PExpr.isIntExact, hit, hie],
    by simp [PExpr.isInt, hnt, hne]⟩
  simp only [evalAt, hcc, hec, Gen2.except_ok_bind]
  by_cases hx : x = 0
  · simp [hx, hee]
  · simp [hx, het, bne_iff_ne]

theorem EC.ofEA {env : IEnv} {e : PExpr} {v : Int} (h : EA env e v) : EC env e v := ⟨(32, true), h.1, h.2.1⟩

/-! A comparison of two `int`s (IEEE 1800-2023 §11.4.4, §11.4.5): both operands at their common type, the signed 32-bit
one (§11.8.1), the result 1 or 0 at the comparison's 1-bit unsigned type. The values are the summary's `CE.eval` of a
`cmp` (`s>` is `b < a`, `!=` is `if a = b then 0 else 1`). -/

theorem EC.slt (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) :
    EC env (.binary .slt l r) (if a < b then 1 else 0) := by
  obtain ⟨hcl, hel, -, -⟩ := hl
  obtain ⟨hcr, her, -, -⟩ := hr
  refine ⟨(1, false), by simp only [ctype, SymBinOp.constClass], ?_⟩
  simp only [evalAt, ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]
  unfold_param_private
  by_cases hh : a < b <;> simp [hh, hel, her, max32, Gen2.except_ok_bind, cc1_one, cc1_zero]

theorem EC.sle (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) :
    EC env (.binary .sle l r) (if a ≤ b then 1 else 0) := by
  obtain ⟨hcl, hel, -, -⟩ := hl
  obtain ⟨hcr, her, -, -⟩ := hr
  refine ⟨(1, false), by simp only [ctype, SymBinOp.constClass], ?_⟩
  simp only [evalAt, ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]
  unfold_param_private
  by_cases hh : a ≤ b <;> simp [hh, hel, her, max32, Gen2.except_ok_bind, cc1_one, cc1_zero]

theorem EC.sgt (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) :
    EC env (.binary .sgt l r) (if b < a then 1 else 0) := by
  obtain ⟨hcl, hel, -, -⟩ := hl
  obtain ⟨hcr, her, -, -⟩ := hr
  refine ⟨(1, false), by simp only [ctype, SymBinOp.constClass], ?_⟩
  simp only [evalAt, ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]
  unfold_param_private
  by_cases hh : b < a <;> simp [hh, hel, her, max32, Gen2.except_ok_bind, cc1_one, cc1_zero]

theorem EC.sge (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) :
    EC env (.binary .sge l r) (if b ≤ a then 1 else 0) := by
  obtain ⟨hcl, hel, -, -⟩ := hl
  obtain ⟨hcr, her, -, -⟩ := hr
  refine ⟨(1, false), by simp only [ctype, SymBinOp.constClass], ?_⟩
  simp only [evalAt, ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]
  unfold_param_private
  by_cases hh : b ≤ a <;> simp [hh, hel, her, max32, Gen2.except_ok_bind, cc1_one, cc1_zero]

theorem EC.eq (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) :
    EC env (.binary (.m0 .eq) l r) (if a = b then 1 else 0) := by
  obtain ⟨hcl, hel, -, -⟩ := hl
  obtain ⟨hcr, her, -, -⟩ := hr
  refine ⟨(1, false), by simp only [ctype, SymBinOp.constClass], ?_⟩
  simp only [evalAt, ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]
  unfold_param_private
  by_cases hh : a = b <;> simp [hh, hel, her, max32, Gen2.except_ok_bind, cc1_one, cc1_zero]

theorem EC.ne (env : IEnv) (l r : PExpr) (a b : Int) (hl : EA env l a) (hr : EA env r b) :
    EC env (.binary (.m0 .ne) l r) (if a = b then 0 else 1) := by
  obtain ⟨hcl, hel, -, -⟩ := hl
  obtain ⟨hcr, her, -, -⟩ := hr
  refine ⟨(1, false), by simp only [ctype, SymBinOp.constClass], ?_⟩
  simp only [evalAt, ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind]
  unfold_param_private
  by_cases hh : a = b <;> simp [hh, hel, her, max32, Gen2.except_ok_bind, cc1_one, cc1_zero]

/-! The exact evaluator of an `int` target (`evalIntExactRec`): every node wrapped to 32 bits, a `?:` through the
width-exact evaluator (`evalSized`, the `evalAt` above). -/

theorem EI.int (env : IEnv) (v : Int) (h : InR32 v) : EI env (.int v) v :=
  ⟨rfl, rfl, by simp only [evalIntExactRec, canonInt32_id h]⟩

theorem EI.ref (env : IEnv) (n : String) (v : Int) (hb : IntB env n v) (h : InR32 v) :
    EI env (.paramRef n none) v := by
  obtain ⟨-, -, hix, hin⟩ := EA.ref env n v hb h
  exact ⟨hix, hin, by simp only [evalIntExactRec, hb.intVal, canonInt32_id h]⟩

theorem EI.add (env : IEnv) (l r : PExpr) (a b : Int) (hl : EI env l a) (hr : EI env r b) (h : InR32 (a + b)) :
    EI env (.binary (.m0 .add) l r) (a + b) := by
  obtain ⟨hil, hnl, hel⟩ := hl
  obtain ⟨hir, hnr, her⟩ := hr
  refine ⟨by simp [PExpr.isIntExact, hil, hir], by simp [PExpr.isInt, hnl, hnr], ?_⟩
  simp only [evalIntExactRec, hil, hir, hel, her, SymBinOp.intArith, Bool.and_self, ↓reduceIte, Gen2.except_ok_bind,
    canonInt32_id h]

theorem EI.sub (env : IEnv) (l r : PExpr) (a b : Int) (hl : EI env l a) (hr : EI env r b) (h : InR32 (a - b)) :
    EI env (.binary (.m0 .sub) l r) (a - b) := by
  obtain ⟨hil, hnl, hel⟩ := hl
  obtain ⟨hir, hnr, her⟩ := hr
  refine ⟨by simp [PExpr.isIntExact, hil, hir], by simp [PExpr.isInt, hnl, hnr], ?_⟩
  simp only [evalIntExactRec, hil, hir, hel, her, SymBinOp.intArith, Bool.and_self, ↓reduceIte, Gen2.except_ok_bind,
    canonInt32_id h]

theorem EI.mul0 (env : IEnv) (l r : PExpr) (a b : Int) (hl : EI env l a) (hr : EI env r b) (h : InR32 (a * b)) :
    EI env (.binary (.m0 .mul) l r) (a * b) := by
  obtain ⟨hil, hnl, hel⟩ := hl
  obtain ⟨hir, hnr, her⟩ := hr
  refine ⟨by simp [PExpr.isIntExact, hil, hir], by simp [PExpr.isInt, hnl, hnr], ?_⟩
  simp only [evalIntExactRec, hil, hir, hel, her, SymBinOp.intArith, Bool.and_self, ↓reduceIte, Gen2.except_ok_bind,
    canonInt32_id h]

theorem EI.mul (env : IEnv) (l r : PExpr) (a b : Int) (hl : EI env l a) (hr : EI env r b) (h : InR32 (a * b)) :
    EI env (.binary .mul l r) (a * b) := by
  obtain ⟨hil, hnl, hel⟩ := hl
  obtain ⟨hir, hnr, her⟩ := hr
  refine ⟨by simp [PExpr.isIntExact, hil, hir], by simp [PExpr.isInt, hnl, hnr], ?_⟩
  simp only [evalIntExactRec, hil, hir, hel, her, SymBinOp.intArith, Bool.and_self, ↓reduceIte, Gen2.except_ok_bind,
    canonInt32_id h]

/-- A `?:` in the exact evaluator: `evalIntExactRec` has no case of its own for it and evaluates it width-exactly
(`evalSized`: its type, then `evalAt` at that type, no assignment target to check). -/
theorem EI.tern (env : IEnv) (c t e : PExpr) (v : Int) (h : EA env (.ternary c t e) v) :
    EI env (.ternary c t e) v := by
  obtain ⟨hc, he, hi, hn⟩ := h
  refine ⟨hi, hn, ?_⟩
  unfold evalIntExactRec
  simp only [evalSized, hc, he, Gen2.except_ok_bind] <;> rfl

/-! ## A localparam, the localparams, the stage -/

/-- **An `int` localparam binds its value** (`bindLocal`): a localparam of a declared packed type that is the INT class
(`declConstType` none: 32 bits, signed), in the exact mode, whose initializer the exact evaluator gives `v` in range,
is bound in `nvals` at `v`, `(32, signed)`. -/
theorem cf_bindLocal (env : IEnv) (lp : PLocalParam) (ds : List PDim) (rs : Option Nat) (v : Int)
    (hty : lp.type? = some (.packed ds rs)) (hdc : declConstType env (some (.packed ds rs)) lp.signed? = .ok none)
    (hi : env.int32 = true) (h : EI env lp.expr v) (hr : InR32 v) :
    bindLocal env lp = .ok (env.bindNVal lp.name v 32 true) := by
  obtain ⟨hix, hin, hev⟩ := h
  have ht : evalIntTarget env lp.expr = .ok v := by
    simp only [evalIntTarget, hin, hi, ↓reduceIte, evalIntExact, Bool.not_true, Bool.false_eq_true, hev]
  unfold bindLocal
  rw [hty]
  simp only [hdc, Gen2.except_ok_bind, ht, hi, ↓reduceIte]
  split
  · rfl
  · rw [canonInt32_id hr]

theorem bindLocals_cons_ok {env env' : IEnv} {lp : PLocalParam} {rest : List PLocalParam}
    (h : bindLocal env lp = .ok env') : bindLocals env (lp :: rest) = bindLocals env' rest := by
  simp only [bindLocals, h]

theorem bindLocals_nil (env : IEnv) : bindLocals env [] = .ok env := rfl

/-- The part of `paramEnv2` after the localparams (verbatim the rest of its `do` block). -/
def paramTail (d : PDesign) (env1 : IEnv) : Res IEnv := do
  let env2 ← bindEnums env1 d.enums
  let pws ← (d.params.map (fun p => (p.name, p.type?))
              ++ d.localParams.map (fun lp => (lp.name, lp.type?))).filterMapM
    fun (n, ty?) =>
      match ty? with
      | none => pure none
      | some ty =>
          match ty.width env2 with
          | .ok w => pure (some (n, w))
          | .error e => Res.unsupported s!"parameter '{n}' type: {e}"
  let env2 := { env2 with pwidths := pws }
  .ok { env2 with dims := dimTable env2 d.decls, functions := d.functions }

/-- **`paramEnv2` with the localparams' environment given**: the packages, enums and parameters bound as the stage binds
them, then the localparams (`hL`, shown node by node), then the rest of the stage. -/
theorem paramEnv2_of_locals {d : PDesign} {args : List Int} {envP envE env0 env1 : IEnv}
    (hP : bindPackageParams { int32 := true } d.packageParams = .ok envP)
    (hE : bindPackageEnums envP d.enums = .ok envE)
    (hB : bindParamsRes envE d.params args = .ok env0)
    (hL : bindLocals env0 d.localParams = .ok env1) :
    d.paramEnv2 args = paramTail d env1 := by
  unfold PDesign.paramEnv2 paramTail
  simp only [hP, hE, hB, hL, Res.ok_bind]
  rfl

/-! ## Bounds: interval arithmetic on the values -/

/-- `x` lies in `[lo, hi]`. -/
def Bnd (lo hi x : Int) : Prop := lo ≤ x ∧ x ≤ hi

theorem bnd_eq (x lo : Int) (h : x = lo) : Bnd lo lo x := by
  subst h; exact ⟨Int.le_refl _, Int.le_refl _⟩

theorem bnd_add (lo1 hi1 lo2 hi2 lo hi a b : Int) (h1 : Bnd lo1 hi1 a) (h2 : Bnd lo2 hi2 b)
    (hlo : lo1 + lo2 = lo) (hhi : hi1 + hi2 = hi) : Bnd lo hi (a + b) := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  subst hlo hhi
  exact ⟨by omega, by omega⟩

theorem bnd_sub (lo1 hi1 lo2 hi2 lo hi a b : Int) (h1 : Bnd lo1 hi1 a) (h2 : Bnd lo2 hi2 b)
    (hlo : lo1 - hi2 = lo) (hhi : hi1 - lo2 = hi) : Bnd lo hi (a - b) := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  subst hlo hhi
  exact ⟨by omega, by omega⟩

/-- A product with a non-negative literal factor on the left. -/
theorem bnd_mul_l (k lo1 hi1 lo hi b : Int) (hk : 0 ≤ k) (h : Bnd lo1 hi1 b) (hlo : k * lo1 = lo)
    (hhi : k * hi1 = hi) : Bnd lo hi (k * b) := by
  obtain ⟨ha, hb⟩ := h
  subst hlo hhi
  exact ⟨Int.mul_le_mul_of_nonneg_left ha hk, Int.mul_le_mul_of_nonneg_left hb hk⟩

/-- A product with a negative literal factor on the left. -/
theorem bnd_mul_l_neg (k lo1 hi1 lo hi b : Int) (hk : k < 0) (h : Bnd lo1 hi1 b) (hlo : k * hi1 = lo)
    (hhi : k * lo1 = hi) : Bnd lo hi (k * b) := by
  obtain ⟨ha, hb⟩ := h
  subst hlo hhi
  exact ⟨Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hk) hb, Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hk) ha⟩

theorem bnd_mul_r (k lo1 hi1 lo hi b : Int) (hk : 0 ≤ k) (h : Bnd lo1 hi1 b) (hlo : k * lo1 = lo)
    (hhi : k * hi1 = hi) : Bnd lo hi (b * k) := by
  rw [Int.mul_comm]
  exact bnd_mul_l k lo1 hi1 lo hi b hk h hlo hhi

theorem bnd_mul_r_neg (k lo1 hi1 lo hi b : Int) (hk : k < 0) (h : Bnd lo1 hi1 b) (hlo : k * hi1 = lo)
    (hhi : k * lo1 = hi) : Bnd lo hi (b * k) := by
  rw [Int.mul_comm]
  exact bnd_mul_l_neg k lo1 hi1 lo hi b hk h hlo hhi

theorem bnd_ite (p : Prop) [Decidable p] (lo hi a b : Int) (ha : Bnd lo hi a) (hb : Bnd lo hi b) :
    Bnd lo hi (if p then a else b) := by
  split
  · exact ha
  · exact hb

theorem bnd_widen (lo1 hi1 lo hi x : Int) (h : Bnd lo1 hi1 x) (hlo : lo ≤ lo1) (hhi : hi1 ≤ hi) : Bnd lo hi x := by
  obtain ⟨ha, hb⟩ := h
  exact ⟨Int.le_trans hlo ha, Int.le_trans hb hhi⟩

theorem bnd_of (lo hi x : Int) (h1 : lo ≤ x) (h2 : x ≤ hi) : Bnd lo hi x := ⟨h1, h2⟩

theorem inR_of_bnd (lo hi x : Int) (h : Bnd lo hi x) (hlo : -2147483648 ≤ lo) (hhi : hi < 2147483648) : InR32 x := by
  obtain ⟨ha, hb⟩ := h
  exact ⟨Int.le_trans hlo ha, Int.lt_of_le_of_lt hb hhi⟩

/-- A parameter bound as `canonInt 32 true x` (`bindParams` in the exact mode) is `x` where `x` is in range. -/
theorem canon_of_inR (x : Int) (h : InR32 x) : canonInt 32 true x = x := canonInt32_id h

end CombView
end LeanModels.Sv
