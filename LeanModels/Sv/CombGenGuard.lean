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

/-- The operand form of `m >> k`, `k` a literal amount (`shrK`). -/
theorem opdAffs?_shrK {l r : PExpr} {m : String} {k : Nat} (hl : nameOf? l = some m) (hnr : nameOf? r = none)
    (hk : litAmt? r = some k) :
    opdAffs? (.binary .shr l r) =
      some (Aff.atom (.shrK m k), [Aff.var m, Aff.const (k : Int), Aff.atom (.shrK m k)]) := by
  obtain ⟨rfl, -⟩ := litAmt?_eq hk
  simp only [opdAffs?, opdAffs?_name hl, opdBin, xatOf?, hl, hnr, hk, Option.map_some]
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
  · -- `m >> n`, `m >> k` of a literal `k`, and `m >> (n + c)` of an affine amount
    rcases hm : nameOf? l with _ | m <;> rcases hn : nameOf? r with _ | n <;> simp only [hm, hn, reduceCtorEq,
      Option.some.injEq] at hx
    · rcases hk : litAmt? r with _ | k <;> simp only [hk, reduceCtorEq, Option.some.injEq] at hx
      · rcases ha : affAmt? r with _ | ⟨n, c⟩ <;> simp only [ha, Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq] at hx
        subst hx
        have har : ar.eval σ = σ n + c := by
          obtain ⟨l0, hl0, rfl | rfl⟩ := affAmt?_cases ha
          · simp only [opdAffs?, opdAffs?_name hl0, opdBin, Option.some.injEq, Prod.mk.injEq] at hra
            obtain ⟨rfl, -⟩ := hra
            rw [Aff.eval_add, Aff.eval_var, Aff.eval_const]
          · simp only [opdAffs?, opdAffs?_name hl0, opdBin, Option.some.injEq, Prod.mk.injEq] at hra
            obtain ⟨rfl, -⟩ := hra
            rw [Aff.eval_sub, Aff.eval_var, Aff.eval_const, Int.sub_neg]
        rw [opdAffs?_name hm, Option.some.injEq, Prod.mk.injEq] at hla
        obtain ⟨rfl, -⟩ := hla
        rw [Aff.eval_var] at hel
        rw [har] at her
        obtain ⟨h0, h1, h2, h3⟩ := hok
        simp only [XAt.eval] at hrng ⊢
        have n1 : ¬ σ n + c < 0 := by omega
        have n2 : ¬ ((32 : Nat) : Int) ≤ σ n + c := by omega
        have e : (σ m).emod ((2 : Int) ^ 32) = σ m := Int.emod_eq_of_lt h0 (by omega)
        refine ⟨by rw [ctype]; simp only [SymBinOp.constClass, hcl], ?_⟩
        rw [evalAt]
        simp only [SymBinOp.constClass, hel, her, hcr, Gen2.except_ok_bind]
        unfold_param_private
        simp only [n1, n2, ↓reduceIte]
        rw [e, canonInt32_id hrng]
      subst hx
      obtain ⟨rfl, hk32⟩ := litAmt?_eq hk
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at hra
      obtain ⟨rfl, -⟩ := hra
      rw [opdAffs?_name hm, Option.some.injEq, Prod.mk.injEq] at hla
      obtain ⟨rfl, -⟩ := hla
      rw [Aff.eval_var] at hel
      rw [Aff.eval_const] at her
      obtain ⟨h0, h1, -⟩ := hok
      simp only [XAt.eval] at hrng ⊢
      have n1 : ¬ (k : Int) < 0 := by omega
      have n2 : ¬ ((32 : Nat) : Int) ≤ (k : Int) := by omega
      have e : (σ m).emod ((2 : Int) ^ 32) = σ m := Int.emod_eq_of_lt h0 (by omega)
      refine ⟨by rw [ctype]; simp only [SymBinOp.constClass, hcl], ?_⟩
      rw [evalAt]
      simp only [SymBinOp.constClass, hel, her, hcr, Gen2.except_ok_bind]
      unfold_param_private
      simp only [n1, n2, ↓reduceIte, Int.toNat_natCast]
      rw [e, canonInt32_id hrng]
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
  · -- `(m >> n) << n`, and `(m >> k) << k` of a literal `k`
    rename_i l' r'
    rcases hm : nameOf? l' with _ | m <;> rcases hn' : nameOf? r' with _ | n <;>
      rcases hn : nameOf? r with _ | n' <;> simp only [hm, hn', hn, reduceCtorEq] at hx
    · rcases hk : litAmt? r' with _ | k <;> rcases hk' : litAmt? r with _ | k' <;>
        simp only [hk, hk', reduceCtorEq] at hx
      by_cases he : k = k'
      · subst he
        rw [if_pos rfl, Option.some.injEq] at hx
        subst hx
        have hsh := opdAffs?_shrK hm hn' hk
        obtain ⟨rfl, hk32⟩ := litAmt?_eq hk'
        simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at hra
        obtain ⟨rfl, -⟩ := hra
        rw [hsh, Option.some.injEq, Prod.mk.injEq] at hla
        obtain ⟨rfl, -⟩ := hla
        rw [Aff.eval_atom] at hel
        rw [Aff.eval_const] at her
        obtain ⟨h0, h1, -⟩ := hok
        simp only [XAt.eval] at hrng hel ⊢
        have n1 : ¬ (k : Int) < 0 := by omega
        have n2 : ¬ ((32 : Nat) : Int) ≤ (k : Int) := by omega
        refine ⟨by rw [ctype]; simp only [SymBinOp.constClass, hcl], ?_⟩
        rw [evalAt]
        simp only [SymBinOp.constClass, hel, her, hcr, Gen2.except_ok_bind]
        unfold_param_private
        simp only [n1, n2, ↓reduceIte, Int.toNat_natCast]
        rw [canonInt32_id hrng]
      · rw [if_neg he] at hx; simp at hx
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

/-- The operators of a shift or power atom. -/
theorem xatOf?_op {op : SymBinOp} {l r : PExpr} {x : XAt} (h : xatOf? op l r = some x) :
    op = .shl ∨ op = .pow ∨ op = .shr ∨ op = .m0 .and := by
  rcases xatOf?_cases h with ⟨rfl, -⟩ | ⟨_, _, rfl, -⟩ | ⟨_, _, rfl, -⟩ | ⟨_, _, _, _, rfl, -⟩ | ⟨_, _, _, _, rfl, -⟩ |
    ⟨_, _, rfl, -⟩ | ⟨_, _, _, _, rfl, -⟩ | ⟨_, _, _, rfl, -⟩ <;> simp

/-- The operators of a linear step of an operand. -/
theorem opdBin_op {op : SymBinOp} {a b c : Aff} (h : opdBin op a b = some c) :
    op = .m0 .add ∨ op = .m0 .sub ∨ op = .mul ∨ op = .m0 .mul := by
  rcases opdBin_cases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl | rfl, -⟩ <;> simp

/-- **The two readings of an operand agree**: where both the conditional reading (`clOf?`) and the operand
reading (`opdAffs?`) accept an expression, they give it the same value, at every valuation. -/
theorem clOf?_opd_eval {σ : String → Int} :
    ∀ (e : PExpr) (x : CL) (a : Aff) (rs : List Aff), clOf? e = some x → opdAffs? e = some (a, rs) →
      x.eval σ = a.eval σ
  | .int v, x, a, rs, h1, h2 => by
      simp only [clOf?, Option.some.injEq] at h1
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      subst h1
      simp [CL.eval, CL.linEval, Aff.eval_const]
  | .genvarRef n, x, a, rs, h1, h2 => by
      simp only [clOf?, Option.some.injEq] at h1
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      subst h1
      simp [CL.eval, CL.linEval, Aff.eval_var]
  | .paramRef n none, x, a, rs, h1, h2 => by
      simp only [clOf?, Option.some.injEq] at h1
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      subst h1
      simp [CL.eval, CL.linEval, Aff.eval_var]
  | .binary op l r, x, a, rs, h1, h2 => by
      simp only [clOf?] at h1
      simp only [opdAffs?] at h2
      rcases hl : clOf? l with _ | xl
      · simp [hl] at h1
      rcases hr : clOf? r with _ | xr
      · simp [hl, hr] at h1
      rcases hla : opdAffs? l with _ | ⟨al, ral⟩
      · simp [hla] at h2
      rcases hra : opdAffs? r with _ | ⟨ar, rar⟩
      · simp [hla, hra] at h2
      simp only [hl, hr] at h1
      simp only [hla, hra] at h2
      have il := clOf?_opd_eval (σ := σ) l xl al ral hl hla
      have ir := clOf?_opd_eval (σ := σ) r xr ar rar hr hra
      rcases hob : opdBin op al ar with _ | c
      · -- the operand reading is an atom: the conditional reading's shift by a literal
        rcases hxa : xatOf? op l r with _ | y
        · simp [hob, hxa] at h2
        simp only [hob, hxa, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        rcases hb : clBin op xl xr with _ | c'
        · simp only [hb] at h1
          obtain ⟨m, k, hx, rfl⟩ := clShr_cases h1
          rw [hxa, Option.some.injEq] at hx
          subst hx
          simp [CL.eval, Aff.eval_atom, XAt.eval]
        · -- `clBin` applies to the linear operators only, none of which an atom has
          rcases clBin_cases hb with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨hop, -⟩
          · rcases xatOf?_op hxa with h | h | h | h <;> cases h
          · rcases xatOf?_op hxa with h | h | h | h <;> cases h
          · rcases hop with rfl | rfl <;> rcases xatOf?_op hxa with h | h | h | h <;> cases h
      · simp only [hob, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        rcases hb : clBin op xl xr with _ | c'
        · -- a shift by a literal is not a linear step
          simp only [hb] at h1
          obtain ⟨m, k, hx, rfl⟩ := clShr_cases h1
          rcases opdBin_op hob with rfl | rfl | rfl | rfl <;> rcases xatOf?_op hx with h | h | h | h <;> cases h
        simp only [hb, Option.some.injEq] at h1
        subst h1
        rcases clBin_cases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hop, ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩⟩
        · simp only [opdBin, Option.some.injEq] at hob
          subst hob
          simp only [CL.eval, il, ir, Aff.eval_add]
        · simp only [opdBin, Option.some.injEq] at hob
          subst hob
          simp only [CL.eval, il, ir, Aff.eval_sub]
          omega
        · simp only [CL.eval, CL.linEval, Int.zero_add] at il
          have hm : affMul al ar = some c := by
            rcases hop with rfl | rfl <;> simpa [opdBin] using hob
          rw [affMul_eval σ hm]
          simp only [CL.eval, ir, il]
        · simp only [CL.eval, CL.linEval, Int.zero_add] at ir
          have hm : affMul al ar = some c := by
            rcases hop with rfl | rfl <;> simpa [opdBin] using hob
          rw [affMul_eval σ hm]
          simp only [CL.eval, il, ← ir]
          exact Int.mul_comm _ _
  | .ternary c t e, x, a, rs, h1, h2 => by
      -- one conditional atom in both readings: the same `clOf?` value
      cases c with
      | binary cop l r =>
          simp only [opdAffs?] at h2
          rw [h1] at h2
          rcases hla : opdAffs? l with _ | ⟨al, ral⟩
          · simp [hla] at h2
          rcases hra : opdAffs? r with _ | ⟨ar, rar⟩
          · simp [hla, hra] at h2
          rcases hta : opdAffs? t with _ | ⟨at', rat⟩
          · simp [hla, hra, hta] at h2
          rcases hea : opdAffs? e with _ | ⟨ae, rae⟩
          · simp [hla, hra, hta, hea] at h2
          simp only [hla, hra, hta, hea, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨rfl, -⟩ := h2
          simp [Aff.eval_atom, XAt.eval]
      | _ => simp [opdAffs?] at h2
  | .paramRef _ (some _), _, _, _, _, h2 => by simp [opdAffs?] at h2
  | .lit _, _, _, _, _, h2 | .ident _, _, _, _, _, h2 | .enumRef .., _, _, _, _, h2 | .fill _, _, _, _, _, h2
  | .unary .., _, _, _, _, h2 | .concat _, _, _, _, _, h2 | .resize .., _, _, _, _, h2
  | .signedResize .., _, _, _, _, h2 | .squash2 .., _, _, _, _, h2 | .sysCall .., _, _, _, _, h2
  | .bitSel .., _, _, _, _, h2 | .partSel .., _, _, _, _, h2 | .repl .., _, _, _, _, h2 | .reduce .., _, _, _, _, h2
  | .cast .., _, _, _, _, h2 | .arrayElem .., _, _, _, _, h2 | .arrayPart .., _, _, _, _, h2
  | .unsupported .., _, _, _, _, h2 | .functionCall .., _, _, _, _, h2 => by simp [opdAffs?] at h2

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
  | .ternary (.binary cop l r) t e, a, rs, h, hg, hp, hr, hxk => by
      -- a `?:` operand, one conditional atom. `evalAt` evaluates the condition at its own type (a comparison of
      -- two `int` operands at the signed 32-bit type, IEEE 1800-2023 §11.8.1) and only the chosen arm at the context
      -- (§11.4.11); the atom's value is the same choice of the same values (`clOf?_opd_eval`)
      simp only [opdAffs?] at h
      rcases hx : clOf? (.ternary (.binary cop l r) t e) with _ | x
      · simp [hx] at h
      rcases hla : opdAffs? l with _ | ⟨al, ral⟩
      · simp [hx, hla] at h
      rcases hra : opdAffs? r with _ | ⟨ar, rar⟩
      · simp [hx, hla, hra] at h
      rcases hta : opdAffs? t with _ | ⟨at', rat⟩
      · simp [hx, hla, hra, hta] at h
      rcases hea : opdAffs? e with _ | ⟨ae, rae⟩
      · simp [hx, hla, hra, hta, hea] at h
      simp only [hx, hla, hra, hta, hea, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hx' := hx
      simp only [clOf?] at hx'
      rcases hc : ccmpOf? cop with _ | cc <;> rcases h1 : clOf? l with _ | xl <;> rcases h2 : clOf? r with _ | xr <;>
        rcases h3 : clOf? t with _ | xt <;> rcases h4 : clOf? e with _ | xe <;>
        simp only [hc, h1, h2, h3, h4, reduceCtorEq, Option.some.injEq] at hx'
      subst hx'
      obtain ⟨hcl, hel⟩ := opd_eval l al ral hla (fun n hn => hg n (by simp [PExpr.gvLeaves, hn]))
        (fun n hn => hp n (by simp [PExpr.pLeaves, hn])) (fun y hy => hr y (by simp [hy]))
        (fun y hy => hxk y (by simp [hy]))
      obtain ⟨hcr, her⟩ := opd_eval r ar rar hra (fun n hn => hg n (by simp [PExpr.gvLeaves, hn]))
        (fun n hn => hp n (by simp [PExpr.pLeaves, hn])) (fun y hy => hr y (by simp [hy]))
        (fun y hy => hxk y (by simp [hy]))
      obtain ⟨hct, het⟩ := opd_eval t at' rat hta (fun n hn => hg n (by simp [PExpr.gvLeaves, hn]))
        (fun n hn => hp n (by simp [PExpr.pLeaves, hn])) (fun y hy => hr y (by simp [hy]))
        (fun y hy => hxk y (by simp [hy]))
      obtain ⟨hce, hee⟩ := opd_eval e ae rae hea (fun n hn => hg n (by simp [PExpr.gvLeaves, hn]))
        (fun n hn => hp n (by simp [PExpr.pLeaves, hn])) (fun y hy => hr y (by simp [hy]))
        (fun y hy => hxk y (by simp [hy]))
      have el := clOf?_opd_eval (σ := σ) l xl al ral h1 hla
      have er := clOf?_opd_eval (σ := σ) r xr ar rar h2 hra
      have et := clOf?_opd_eval (σ := σ) t xt at' rat h3 hta
      have ee := clOf?_opd_eval (σ := σ) e xe ae rae h4 hea
      refine ⟨by simp only [ctype, hct, hce, Gen2.except_ok_bind]; rfl, ?_⟩
      rw [Aff.eval_atom]
      simp only [XAt.eval, CL.eval, el, er, et, ee]
      rcases ccmpOf?_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [evalAt, ctype, SymBinOp.constClass, hcl, hcr, Gen2.except_ok_bind] <;>
        unfold_param_private
      · by_cases hh : al.eval σ < ar.eval σ <;>
          simp [hh, hel, her, het, hee, Gen2.except_ok_bind, CCmp.holds, convertConst, canonInt] <;>
            first | rfl | (intro hm; exact absurd hm (by decide))
      · by_cases hh : al.eval σ ≤ ar.eval σ <;>
          simp [hh, hel, her, het, hee, Gen2.except_ok_bind, CCmp.holds, convertConst, canonInt] <;>
            first | rfl | (intro hm; exact absurd hm (by decide))
      · by_cases hh : ar.eval σ < al.eval σ <;>
          simp [hh, hel, her, het, hee, Gen2.except_ok_bind, CCmp.holds, convertConst, canonInt] <;>
            first | rfl | (intro hm; exact absurd hm (by decide))
      · by_cases hh : ar.eval σ ≤ al.eval σ <;>
          simp [hh, hel, her, het, hee, Gen2.except_ok_bind, CCmp.holds, convertConst, canonInt] <;>
            first | rfl | (intro hm; exact absurd hm (by decide))
      · by_cases hh : al.eval σ = ar.eval σ <;>
          simp [hh, hel, her, het, hee, Gen2.except_ok_bind, CCmp.holds, convertConst, canonInt] <;>
            first | rfl | (intro hm; exact absurd hm (by decide))
      · by_cases hh : al.eval σ = ar.eval σ <;>
          simp [hh, hel, her, het, hee, Gen2.except_ok_bind, CCmp.holds, convertConst, canonInt] <;>
            first | rfl | (intro hm; exact absurd hm (by decide))
  | .ternary (.int _) _ _, _, _, h, _, _, _, _ | .ternary (.lit _) _ _, _, _, h, _, _, _, _
  | .ternary (.ident _) _ _, _, _, h, _, _, _, _ | .ternary (.genvarRef _) _ _, _, _, h, _, _, _, _
  | .ternary (.paramRef _ _) _ _, _, _, h, _, _, _, _ | .ternary (.enumRef _ _ _) _ _, _, _, h, _, _, _, _
  | .ternary (.fill _) _ _, _, _, h, _, _, _, _ | .ternary (.unary _ _) _ _, _, _, h, _, _, _, _
  | .ternary (.ternary _ _ _) _ _, _, _, h, _, _, _, _ | .ternary (.concat _) _ _, _, _, h, _, _, _, _
  | .ternary (.resize _ _) _ _, _, _, h, _, _, _, _ | .ternary (.signedResize _ _) _ _, _, _, h, _, _, _, _
  | .ternary (.squash2 _ _) _ _, _, _, h, _, _, _, _ | .ternary (.sysCall _ _) _ _, _, _, h, _, _, _, _
  | .ternary (.bitSel _ _) _ _, _, _, h, _, _, _, _ | .ternary (.partSel _ _ _) _ _, _, _, h, _, _, _, _
  | .ternary (.repl _ _) _ _, _, _, h, _, _, _, _ | .ternary (.reduce _ _) _ _, _, _, h, _, _, _, _
  | .ternary (.cast _ _) _ _, _, _, h, _, _, _, _ | .ternary (.arrayElem _ _) _ _, _, _, h, _, _, _, _
  | .ternary (.arrayPart _ _ _ _ _) _ _, _, _, h, _, _, _, _ | .ternary (.unsupported _ _) _ _, _, _, h, _, _, _, _
  | .ternary (.functionCall _ _) _ _, _, _, h, _, _, _, _ => by simp [opdAffs?] at h
  | .paramRef _ (some _), _, _, h, _, _, _, _ => by simp [opdAffs?] at h
  | .lit _, _, _, h, _, _, _, _ | .ident _, _, _, h, _, _, _, _ | .enumRef .., _, _, h, _, _, _, _
  | .unary .., _, _, h, _, _, _, _ | .bitSel .., _, _, h, _, _, _, _
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
