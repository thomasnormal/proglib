import Lean
import LeanModels.Sv.CombView

/-!
# `sv_structure`: the condition of a conditional generate construct, as the instantiation evaluates it

`GenItem.expand2` selects an arm of `if (c) … else …` by `evalGenGuard env c` (`Param.lean`): the condition typed
(`ctype`) and evaluated at its type (`evalAt`), IEEE 1800-2023 §11.6.1, §11.8.2. For a comparison `l op r` of two `int`
operands (a guard, `guardOf?`) that is the comparison of the operands evaluated at the signed 32-bit type, each
operation wrapped to 32 bits; `guard_eval` shows it is the guard's comparison of the operands' affine values, where the
genvars and parameters the operands read have their values in the environment and every subterm's affine value is a
32-bit value (`Guard.rngs`, owed by `AutoObl`). Nothing about the instantiation is assumed: the lemmas compute
`evalGenGuard` itself.

`evalAt` computes through helpers that `Param.lean` keeps private (`constArith`, `constCompare`, `b2i`, the signedness
checks of a comparison); `unfold_param_private` unfolds them definitionally by name, as the tactics' `liftCond` does.
-/

namespace LeanModels.Sv
namespace CombView

open Lean Meta Elab Tactic in
/-- Unfold, definitionally, the private helpers of `Param.lean` that `evalAt` computes through: the arithmetic and the
comparison of a constant expression and the signedness checks of a comparison. -/
elab "unfold_param_private" : tactic => do
  let nms := [`LeanModels.Sv.constArith, `LeanModels.Sv.constCompare, `LeanModels.Sv.b2i,
      `LeanModels.Sv.SymBinOp.signedOrder, `LeanModels.Sv.SymBinOp.unsignedOrder, `LeanModels.Sv.constShift].map fun n =>
    Name.append ((`_private ++ `LeanModels.Sv.Param).num 0) n
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (pre := fun e => do
    if nms.any (e.isAppOf ·) then
      if let some e' ← unfoldDefinition? e then return .visit (← whnfCore e')
    return .continue)
  replaceMainGoal [← g.change t']

theorem canonInt_emod32 (v : Int) : canonInt 32 true (v.emod ((2 : Int) ^ 32)) = canonInt 32 true v := by
  have e : Int.emod (Int.emod v ((2 : Int) ^ 32)) ((2 : Int) ^ 32) = Int.emod v ((2 : Int) ^ 32) :=
    Int.emod_emod v _
  unfold canonInt
  rw [e]

theorem canonInt32_id {v : Int} (h : -2147483648 ≤ v ∧ v < 2147483648) : canonInt 32 true v = v :=
  canonInt32_of_range h

/-- A 32-bit value converted to the signed 32-bit type is itself. -/
theorem convertConst32 {v : Int} (h : -2147483648 ≤ v ∧ v < 2147483648) : convertConst 32 32 true v = v := by
  unfold convertConst
  simp only [if_true, canonInt_emod32, canonInt32_id h]

/-- A 0/1 value converted to the 1-bit unsigned type is itself. -/
theorem convertConst1_ite (p : Prop) [Decidable p] :
    convertConst 1 1 false (if p then 1 else 0) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h, convertConst, canonInt] <;> decide

/-- The operand form of a named constant. -/
theorem opdAffs?_name {e : PExpr} {n : String} (h : nameOf? e = some n) : opdAffs? e = some (Aff.var n, [Aff.var n]) := by
  rcases nameOf?_cases h with rfl | rfl <;> rfl

/-- The operand form of `m >> n`. -/
theorem opdAffs?_shr {l r : PExpr} {m n : String} (hl : nameOf? l = some m) (hr : nameOf? r = some n) :
    opdAffs? (.binary .shr l r) =
      some (Aff.atom (.shr m n), [Aff.var m, Aff.var n, Aff.atom (.shr m n)]) := by
  simp only [opdAffs?, opdAffs?_name hl, opdAffs?_name hr, opdBin, xatOf?, hl, hr]
  rfl

/-- **A shift or power atom of a generate condition's operand evaluates to its value** at the signed 32-bit type
(`evalAt`), from its operands' values, where it is in its range and its value is a 32-bit value. -/
theorem opd_eval_xat {E : IEnv} {σ : String → Int} {op : SymBinOp} {l r : PExpr} {x : XAt} {al ar : Aff}
    {ral rar : List Aff} (hx : xatOf? op l r = some x)
    (hla : opdAffs? l = some (al, ral)) (hra : opdAffs? r = some (ar, rar))
    (hl : ctype E l = .ok (32, true) ∧ evalAt E (32, true) l = .ok (al.eval σ))
    (hr : ctype E r = .ok (32, true) ∧ evalAt E (32, true) r = .ok (ar.eval σ))
    (hok : x.Ok σ) (hrng : -2147483648 ≤ x.eval σ ∧ x.eval σ < 2147483648) :
    ctype E (.binary op l r) = .ok (32, true) ∧ evalAt E (32, true) (.binary op l r) = .ok (x.eval σ) := by
  obtain ⟨hcl, hel⟩ := hl
  obtain ⟨hcr, her⟩ := hr
  unfold xatOf? at hx
  split at hx
  · -- `1 << n`
    rename_i v
    by_cases hv : v = 1
    · subst hv
      rw [if_pos rfl] at hx
      rcases hn : nameOf? r with _ | n
      · simp [hn] at hx
      · simp only [hn, Option.map_some, Option.some.injEq] at hx
        subst hx
        rw [opdAffs?_name hn, Option.some.injEq, Prod.mk.injEq] at hra
        obtain ⟨rfl, -⟩ := hra
        simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at hla
        obtain ⟨rfl, -⟩ := hla
        rw [Aff.eval_const] at hel
        rw [Aff.eval_var] at her
        obtain ⟨h0, h32, -⟩ := hok
        simp only [XAt.eval] at hrng ⊢
        have n1 : ¬ σ n < 0 := by omega
        have n2 : ¬ ((32 : Nat) : Int) ≤ σ n := by omega
        refine ⟨by rw [ctype]; simp only [SymBinOp.constClass, hcl], ?_⟩
        rw [evalAt]
        simp only [SymBinOp.constClass, hel, her, hcr, Gen2.except_ok_bind]
        unfold_param_private
        simp only [n1, n2, ↓reduceIte, Int.one_mul]
        rw [canonInt32_id hrng]
    · rw [if_neg hv] at hx; simp at hx
  · -- `b ** n`
    rename_i b
    by_cases hb : 2 ≤ b
    · rw [if_pos hb] at hx
      rcases hn : nameOf? r with _ | n
      · simp [hn] at hx
      · simp only [hn, Option.map_some, Option.some.injEq] at hx
        subst hx
        rw [opdAffs?_name hn, Option.some.injEq, Prod.mk.injEq] at hra
        obtain ⟨rfl, -⟩ := hra
        simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at hla
        obtain ⟨rfl, -⟩ := hla
        rw [Aff.eval_const] at hel
        rw [Aff.eval_var] at her
        obtain ⟨h0, h32, -⟩ := hok
        simp only [XAt.eval] at hrng ⊢
        have n1 : ¬ σ n < 0 := by omega
        have n2 : ¬ (4096 : Int) < σ n := by omega
        refine ⟨by rw [ctype]; simp only [SymBinOp.constClass, hcl], ?_⟩
        rw [evalAt]
        simp only [SymBinOp.constClass, hel, her, hcr, Gen2.except_ok_bind]
        unfold_param_private
        simp only [n1, n2, ↓reduceIte]
        rw [canonInt32_id hrng]
    · rw [if_neg hb] at hx; simp at hx
  · -- `m >> n`
    rcases hm : nameOf? l with _ | m <;> rcases hn : nameOf? r with _ | n <;> simp only [hm, hn, reduceCtorEq,
      Option.some.injEq] at hx
    subst hx
    rw [opdAffs?_name hn, Option.some.injEq, Prod.mk.injEq] at hra
    obtain ⟨rfl, -⟩ := hra
    rw [opdAffs?_name hm, Option.some.injEq, Prod.mk.injEq] at hla
    obtain ⟨rfl, -⟩ := hla
    rw [Aff.eval_var] at hel her
    obtain ⟨h0, h1, h2, h3⟩ := hok
    simp only [XAt.eval] at hrng ⊢
    have n1 : ¬ σ n < 0 := by omega
    have n2 : ¬ ((32 : Nat) : Int) ≤ σ n := by omega
    have e : (σ m).emod ((2 : Int) ^ 32) = σ m := Int.emod_eq_of_lt h0 (by omega)
    refine ⟨by rw [ctype]; simp only [SymBinOp.constClass, hcl], ?_⟩
    rw [evalAt]
    simp only [SymBinOp.constClass, hel, her, hcr, Gen2.except_ok_bind]
    unfold_param_private
    simp only [n1, n2, ↓reduceIte]
    rw [e, canonInt32_id hrng]
  · -- `(m >> n) << n`
    rename_i l' r'
    rcases hm : nameOf? l' with _ | m <;> rcases hn' : nameOf? r' with _ | n <;>
      rcases hn : nameOf? r with _ | n' <;> simp only [hm, hn', hn, reduceCtorEq] at hx
    by_cases he : n = n'
    · subst he
      rw [if_pos rfl, Option.some.injEq] at hx
      subst hx
      rw [opdAffs?_name hn, Option.some.injEq, Prod.mk.injEq] at hra
      obtain ⟨rfl, -⟩ := hra
      rw [opdAffs?_shr hm hn', Option.some.injEq, Prod.mk.injEq] at hla
      obtain ⟨rfl, -⟩ := hla
      rw [Aff.eval_atom] at hel
      rw [Aff.eval_var] at her
      obtain ⟨h0, h1, h2, h3⟩ := hok
      simp only [XAt.eval] at hrng hel ⊢
      have n1 : ¬ σ n < 0 := by omega
      have n2 : ¬ ((32 : Nat) : Int) ≤ σ n := by omega
      refine ⟨by rw [ctype]; simp only [SymBinOp.constClass, hcl], ?_⟩
      rw [evalAt]
      simp only [SymBinOp.constClass, hel, her, hcr, Gen2.except_ok_bind]
      unfold_param_private
      simp only [n1, n2, ↓reduceIte]
      rw [canonInt32_id hrng]
    · rw [if_neg he] at hx; simp at hx
  · -- `(m >> n) & 1`
    rename_i l' r'
    split at hx
    · rename_i v m n hm hn
      by_cases hv : v = 1
      · subst hv
        rw [if_pos rfl, Option.some.injEq] at hx
        subst hx
        simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at hra
        obtain ⟨rfl, -⟩ := hra
        rw [opdAffs?_shr hm hn, Option.some.injEq, Prod.mk.injEq] at hla
        obtain ⟨rfl, -⟩ := hla
        rw [Aff.eval_atom] at hel
        rw [Aff.eval_const] at her
        obtain ⟨h0, h1, h2, h3⟩ := hok
        simp only [XAt.eval] at hrng hel ⊢
        have hq0 : 0 ≤ σ m / 2 ^ (σ n).toNat := Int.ediv_nonneg h0 (Int.le_of_lt (Int.pow_pos (by decide)))
        have hq1 : σ m / 2 ^ (σ n).toNat ≤ σ m := Int.ediv_le_self _ h0
        have e1 : (σ m / 2 ^ (σ n).toNat).emod ((2 : Int) ^ 32) = σ m / 2 ^ (σ n).toNat :=
          Int.emod_eq_of_lt hq0 (by omega)
        have e2 : (1 : Int).emod ((2 : Int) ^ 32) = 1 := by decide
        refine ⟨by rw [ctype]; simp only [SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind] <;> rfl, ?_⟩
        rw [evalAt]
        simp only [SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
        unfold_param_private
        simp only [e1, e2, show (1 : Int).toNat = 1 from rfl]
        rw [ofNat_land_one hq0, canonInt32_id hrng]
      · rw [if_neg hv] at hx; simp at hx
    · simp at hx
  · simp at hx

/-- **An affine operand evaluates to its affine value at the signed 32-bit type**, where the genvars it reads are bound
in `vals`, the parameters agree, every subterm's value is a 32-bit value, and every atom is in its range. -/
theorem opd_eval {E : IEnv} {σ : String → Int} :
    ∀ (e : PExpr) (a : Aff) (rs : List Aff), opdAffs? e = some (a, rs) →
      (∀ n ∈ e.gvLeaves, E.vals.lookup n = some (σ n)) → (∀ n ∈ e.pLeaves, E.intVal? n = some (σ n)) →
      (∀ r ∈ rs, -2147483648 ≤ r.eval σ ∧ r.eval σ < 2147483648) → (∀ r ∈ rs, r.XOk σ) →
      ctype E e = .ok (32, true) ∧ evalAt E (32, true) e = .ok (a.eval σ)
  | .int v, a, rs, h, _, _, hr, _ => by
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hv := hr _ (List.mem_singleton_self _)
      simp only [Aff.eval_const] at hv ⊢
      refine ⟨rfl, ?_⟩
      simp only [evalAt, convertConst32 hv]
  | .genvarRef n, a, rs, h, hg, _, hr, _ => by
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hv := hr _ (List.mem_singleton_self _)
      simp only [Aff.eval_var] at hv ⊢
      have hl := hg n (by simp [PExpr.gvLeaves])
      refine ⟨rfl, ?_⟩
      simp only [evalAt, hl, convertConst32 hv]
  | .paramRef n none, a, rs, h, _, hp, hr, _ => by
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hv := hr _ (List.mem_singleton_self _)
      simp only [Aff.eval_var] at hv ⊢
      have hi := hp n (by simp [PExpr.pLeaves])
      cases hx : E.vals.lookup n with
      | some x =>
          have : x = σ n := by simpa [IEnv.intVal?, hx] using hi
          subst this
          exact ⟨by simp [ctype, hx], by simp [evalAt, hx, convertConst32 hv]⟩
      | none =>
          rcases IEnv.intVal?_cases hi with hl | ⟨w, s, hn, rfl, rfl⟩
          · rw [hx] at hl; cases hl
          · exact ⟨by simp [ctype, hx, hn], by simp [evalAt, hx, hn, convertConst32 hv]⟩
  | .binary op l r, a, rs, h, hg, hp, hr, hxk => by
      simp only [opdAffs?] at h
      rcases hla : opdAffs? l with _ | ⟨al, ral⟩
      · simp [hla] at h
      rcases hra : opdAffs? r with _ | ⟨ar, rar⟩
      · simp [hla, hra] at h
      simp only [hla, hra] at h
      have hgl : ∀ n ∈ l.gvLeaves, E.vals.lookup n = some (σ n) :=
        fun n hn => hg n (by simp [PExpr.gvLeaves, hn])
      have hgr : ∀ n ∈ r.gvLeaves, E.vals.lookup n = some (σ n) :=
        fun n hn => hg n (by simp [PExpr.gvLeaves, hn])
      have hpl : ∀ n ∈ l.pLeaves, E.intVal? n = some (σ n) :=
        fun n hn => hp n (by simp [PExpr.pLeaves, hn])
      have hpr : ∀ n ∈ r.pLeaves, E.intVal? n = some (σ n) :=
        fun n hn => hp n (by simp [PExpr.pLeaves, hn])
      -- the operands' subterms are among `rs`
      have hsub : ∀ {c : Aff}, rs = ral ++ rar ++ [c] →
          (ctype E l = .ok (32, true) ∧ evalAt E (32, true) l = .ok (al.eval σ)) ∧
          (ctype E r = .ok (32, true) ∧ evalAt E (32, true) r = .ok (ar.eval σ)) ∧
          (-2147483648 ≤ c.eval σ ∧ c.eval σ < 2147483648) ∧ c.XOk σ := by
        intro c hrs
        subst hrs
        exact ⟨opd_eval l al ral hla hgl hpl (fun x hx => hr x (by simp [hx])) (fun x hx => hxk x (by simp [hx])),
          opd_eval r ar rar hra hgr hpr (fun x hx => hr x (by simp [hx])) (fun x hx => hxk x (by simp [hx])),
          hr c (by simp), hxk c (by simp)⟩
      rcases hb : opdBin op al ar with _ | c
      · -- a shift or power atom
        rcases hxa : xatOf? op l r with _ | x <;>
          simp only [hb, hxa, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, hrs⟩ := h
        obtain ⟨hl, hr', hc, hck⟩ := hsub hrs.symm
        have hok : x.Ok σ := by
          simp only [Aff.XOk, Aff.atom, Aff.XOkL, and_true] at hck
          exact hck
        rw [Aff.eval_atom] at hc ⊢
        exact opd_eval_xat hxa hla hra hl hr' hok hc
      simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hrs⟩ := h
      obtain ⟨⟨hcl, hel⟩, ⟨hcr, her⟩, hc, -⟩ := hsub hrs.symm
      rcases opdBin_cases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hop, hm⟩
      · rw [Aff.eval_add] at hc ⊢
        refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr]; rfl, ?_⟩
        simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
        unfold_param_private
        rw [canonInt32_id hc]
      · rw [Aff.eval_sub] at hc ⊢
        refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr]; rfl, ?_⟩
        simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
        unfold_param_private
        rw [canonInt32_id hc]
      · rw [affMul_eval σ hm] at hc ⊢
        rcases hop with rfl | rfl
        · refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr]; rfl, ?_⟩
          simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
          unfold_param_private
          rw [canonInt32_id hc]
        · refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr]; rfl, ?_⟩
          simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
          unfold_param_private
          rw [canonInt32_id hc]
  | .paramRef _ (some _), _, _, h, _, _, _, _ => by simp [opdAffs?] at h
  | .lit _, _, _, h, _, _, _, _ | .ident _, _, _, h, _, _, _, _ | .enumRef .., _, _, h, _, _, _, _
  | .unary .., _, _, h, _, _, _, _ | .ternary .., _, _, h, _, _, _, _ | .bitSel .., _, _, h, _, _, _, _
  | .partSel .., _, _, h, _, _, _, _ | .arrayElem .., _, _, h, _, _, _, _ | .arrayPart .., _, _, h, _, _, _, _
  | .fill _, _, _, h, _, _, _, _ | .concat _, _, _, h, _, _, _, _ | .repl .., _, _, h, _, _, _, _
  | .reduce .., _, _, h, _, _, _, _ | .resize .., _, _, h, _, _, _, _ | .signedResize .., _, _, h, _, _, _, _
  | .squash2 .., _, _, h, _, _, _, _ | .sysCall .., _, _, h, _, _, _, _ | .cast .., _, _, h, _, _, _, _
  | .unsupported .., _, _, h, _, _, _, _ | .functionCall .., _, _, h, _, _, _, _ => by simp [opdAffs?] at h

/-- **The instantiation's value of a generate condition** (`evalGenGuard`): `1` where the guard holds, `0` where it
does not, when the genvars its operands read are bound in `vals`, the parameters agree, and every subterm of the
operands is a 32-bit value. -/
theorem guard_eval {E : IEnv} {σ : String → Int} {c : PExpr} {g : Guard} (hg : guardOf? c = some g)
    (hgv : ∀ n ∈ c.gvLeaves, E.vals.lookup n = some (σ n)) (hpv : ∀ n ∈ c.pLeaves, E.intVal? n = some (σ n))
    (hr : ∀ a ∈ g.rngs, -2147483648 ≤ a.eval σ ∧ a.eval σ < 2147483648) (hx : ∀ a ∈ g.rngs, a.XOk σ) :
    evalGenGuard E c = .ok (if g.holds σ then 1 else 0) := by
  cases c with
  | binary op l r =>
      simp only [guardOf?] at hg
      rcases hc : gcmpOf? op with _ | cmp
      · simp [hc] at hg
      rcases hla : opdAffs? l with _ | ⟨al, ral⟩
      · simp [hc, hla] at hg
      rcases hra : opdAffs? r with _ | ⟨ar, rar⟩
      · simp [hc, hla, hra] at hg
      simp only [hc, hla, hra, Option.some.injEq] at hg
      subst hg
      obtain ⟨hcl, hel⟩ := opd_eval l al ral hla (fun n hn => hgv n (by simp [PExpr.gvLeaves, hn]))
        (fun n hn => hpv n (by simp [PExpr.pLeaves, hn])) (fun x hx' => hr x (by simp [hx']))
        (fun x hx' => hx x (by simp [hx']))
      obtain ⟨hcr, her⟩ := opd_eval r ar rar hra (fun n hn => hgv n (by simp [PExpr.gvLeaves, hn]))
        (fun n hn => hpv n (by simp [PExpr.pLeaves, hn])) (fun x hx' => hr x (by simp [hx']))
        (fun x hx' => hx x (by simp [hx']))
      cases op with
      | slt =>
          simp only [gcmpOf?, Option.some.injEq] at hc
          subst hc
          simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
          unfold_param_private
          simp only [hel, her, Gen2.except_ok_bind]
          by_cases h : al.eval σ < ar.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
      | sle =>
          simp only [gcmpOf?, Option.some.injEq] at hc
          subst hc
          simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
          unfold_param_private
          simp only [hel, her, Gen2.except_ok_bind]
          by_cases h : al.eval σ ≤ ar.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
      | sgt =>
          simp only [gcmpOf?, Option.some.injEq] at hc
          subst hc
          simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
          unfold_param_private
          simp only [hel, her, Gen2.except_ok_bind]
          by_cases h : ar.eval σ < al.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
      | sge =>
          simp only [gcmpOf?, Option.some.injEq] at hc
          subst hc
          simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
          unfold_param_private
          simp only [hel, her, Gen2.except_ok_bind]
          by_cases h : ar.eval σ ≤ al.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
      | m0 bop =>
          cases bop with
          | eq =>
              simp only [gcmpOf?, Option.some.injEq] at hc
              subst hc
              simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
              unfold_param_private
              simp only [hel, her, Gen2.except_ok_bind]
              by_cases h : al.eval σ = ar.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
          | ne =>
              simp only [gcmpOf?, Option.some.injEq] at hc
              subst hc
              simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
              unfold_param_private
              simp only [hel, her, Gen2.except_ok_bind]
              by_cases h : al.eval σ = ar.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
          | _ => simp [gcmpOf?] at hc
      | _ => simp [gcmpOf?] at hc
  | _ => simp [guardOf?] at hg

end CombView
end LeanModels.Sv
