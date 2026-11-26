import LeanModels.Sv.Kernel.CoreMemExec

namespace LeanModels.Sv.Kernel
open LeanModels.Sv

private theorem beq_false_of_ne {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) :
    (a == b) = false := by
  rw [Bool.eq_false_iff]
  intro hab
  exact h (LawfulBEq.eq_of_beq hab)

/-! A successful quiescence result is independent of extra iteration fuel.
The zero-fuel branch is an implementation refusal, so these bridges state the
property needed by the fuel-free relation for `.ok` results. -/

theorem runImplicitQuiesce_mono {limit limit' : Nat} (h : limit ≤ limit')
    (E : CoreMemDesign) (before current : CoreMemState) (procs : List CoreMemProc)
    (result : CoreMemState)
    (hr : E.runImplicitQuiesce limit before current procs = .ok result) :
    E.runImplicitQuiesce limit' before current procs = .ok result := by
  induction limit generalizing limit' before current result with
  | zero => simp [CoreMemDesign.runImplicitQuiesce] at hr
  | succ limit ih =>
      cases limit' with
      | zero => omega
      | succ limit' =>
          cases hn : E.runImplicitPass before current procs with
          | timeout => simp [CoreMemDesign.runImplicitQuiesce, hn] at hr
          | unsupported msg => simp [CoreMemDesign.runImplicitQuiesce, hn] at hr
          | ok next =>
              by_cases hv : E.scalar.view before.scalar = E.scalar.view next.scalar
              · simp [CoreMemDesign.runImplicitQuiesce, hn, hv] at hr ⊢
                exact hr
              · have hvb := beq_false_of_ne hv
                simp only [CoreMemDesign.runImplicitQuiesce, hn, Res.ok_bind,
                  hvb, Bool.false_eq_true, ↓reduceIte] at hr ⊢
                exact ih (Nat.le_of_succ_le_succ h) current next result hr

theorem runCombInitialQuiesce_mono {limit limit' : Nat} (h : limit ≤ limit')
    (E : CoreMemDesign) (current : CoreMemState) (procs : List CoreMemProc)
    (result : CoreMemState)
    (hr : E.runCombInitialQuiesce limit current procs = .ok result) :
    E.runCombInitialQuiesce limit' current procs = .ok result := by
  induction limit generalizing limit' current result with
  | zero => simp [CoreMemDesign.runCombInitialQuiesce] at hr
  | succ limit ih =>
      cases limit' with
      | zero => omega
      | succ limit' =>
          cases hn : E.runCombInitial current procs with
          | timeout => simp [CoreMemDesign.runCombInitialQuiesce, hn] at hr
          | unsupported msg => simp [CoreMemDesign.runCombInitialQuiesce, hn] at hr
          | ok next =>
              by_cases hv : E.scalar.view current.scalar = E.scalar.view next.scalar
              · simp [CoreMemDesign.runCombInitialQuiesce, hn, hv] at hr ⊢
                exact hr
              · have hvb := beq_false_of_ne hv
                simp only [CoreMemDesign.runCombInitialQuiesce, hn, Res.ok_bind,
                  hvb, Bool.false_eq_true, ↓reduceIte] at hr ⊢
                exact ih (Nat.le_of_succ_le_succ h) next result hr

theorem runCombQuiesce_mono {limit limit' : Nat} (h : limit ≤ limit')
    (E : CoreMemDesign) (before current : CoreMemState) (procs : List CoreMemProc)
    (result : CoreMemState)
    (hr : E.runCombQuiesce limit before current procs = .ok result) :
    E.runCombQuiesce limit' before current procs = .ok result := by
  induction limit generalizing limit' before current result with
  | zero => simp [CoreMemDesign.runCombQuiesce] at hr
  | succ limit ih =>
      cases limit' with
      | zero => omega
      | succ limit' =>
          cases hn : E.runCombPass before current procs with
          | timeout => simp [CoreMemDesign.runCombQuiesce, hn] at hr
          | unsupported msg => simp [CoreMemDesign.runCombQuiesce, hn] at hr
          | ok next =>
              by_cases hv : E.scalar.view before.scalar = E.scalar.view next.scalar
              · simp [CoreMemDesign.runCombQuiesce, hn, hv] at hr ⊢
                exact hr
              · have hvb := beq_false_of_ne hv
                simp only [CoreMemDesign.runCombQuiesce, hn, Res.ok_bind,
                  hvb, Bool.false_eq_true, ↓reduceIte] at hr ⊢
                exact ih (Nat.le_of_succ_le_succ h) current next result hr

theorem settleAssignQuiesce_mono {limit limit' : Nat} (h : limit ≤ limit')
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (procs : List CoreMemProc) (result : CoreMemState)
    (hr : E.settleAssignQuiesce limit env elems st procs = .ok result) :
    E.settleAssignQuiesce limit' env elems st procs = .ok result := by
  induction limit generalizing limit' st result with
  | zero => simp [CoreMemDesign.settleAssignQuiesce] at hr
  | succ limit ih =>
      cases limit' with
      | zero => omega
      | succ limit' =>
          cases hn : E.settleAssign env elems st procs with
          | timeout => simp [CoreMemDesign.settleAssignQuiesce, hn] at hr
          | unsupported msg => simp [CoreMemDesign.settleAssignQuiesce, hn] at hr
          | ok next =>
              by_cases hv : E.scalar.view st.scalar = E.scalar.view next.scalar
              · simp [CoreMemDesign.settleAssignQuiesce, hn, hv] at hr ⊢
                exact hr
              · have hvb := beq_false_of_ne hv
                simp only [CoreMemDesign.settleAssignQuiesce, hn, Res.ok_bind,
                  hvb, Bool.false_eq_true, ↓reduceIte] at hr ⊢
                exact ih (Nat.le_of_succ_le_succ h) next result hr

theorem runCombSettleQuiesce_mono {limit limit' : Nat} (h : limit ≤ limit')
    (E : CoreMemDesign) (before current : CoreMemState) (procs : List CoreMemProc)
    (result : CoreMemState)
    (hr : E.runCombSettleQuiesce limit before current procs = .ok result) :
    E.runCombSettleQuiesce limit' before current procs = .ok result := by
  induction limit generalizing limit' before current result with
  | zero => simp [CoreMemDesign.runCombSettleQuiesce] at hr
  | succ limit ih =>
      cases limit' with
      | zero => omega
      | succ limit' =>
          cases hc : E.runComb before current procs with
          | timeout => simp [CoreMemDesign.runCombSettleQuiesce, hc] at hr
          | unsupported msg => simp [CoreMemDesign.runCombSettleQuiesce, hc] at hr
          | ok combed =>
              cases hs : E.settleCanonical E.env E.elems combed procs with
              | timeout => simp [CoreMemDesign.runCombSettleQuiesce, hc, hs] at hr
              | unsupported msg =>
                  simp [CoreMemDesign.runCombSettleQuiesce, hc, hs] at hr
              | ok settled =>
                  by_cases hv : E.scalar.view current.scalar = E.scalar.view settled.scalar
                  · simp [CoreMemDesign.runCombSettleQuiesce, hc, hs, hv] at hr ⊢
                    exact hr
                  · have hvb := beq_false_of_ne hv
                    simp only [CoreMemDesign.runCombSettleQuiesce, hc, hs,
                      Res.ok_bind, hvb, Bool.false_eq_true, ↓reduceIte] at hr ⊢
                    exact ih (Nat.le_of_succ_le_succ h) combed settled result hr

theorem edgeQuiesce_mono {limit limit' : Nat} (h : limit ≤ limit')
    (E : CoreMemDesign) (st : CoreMemState) (before after : SvState)
    (combBefore : CoreMemState) (result : CoreMemState)
    (hr : E.edgeQuiesce limit st before after combBefore = .ok result) :
    E.edgeQuiesce limit' st before after combBefore = .ok result := by
  induction limit generalizing limit' st before after combBefore result with
  | zero => simp [CoreMemDesign.edgeQuiesce] at hr
  | succ limit ih =>
      cases limit' with
      | zero => omega
      | succ limit' =>
          cases hp : E.edgePass st before after combBefore with
          | timeout => simp [CoreMemDesign.edgeQuiesce, hp] at hr
          | unsupported msg => simp [CoreMemDesign.edgeQuiesce, hp] at hr
          | ok next =>
              by_cases hc : E.processes.toList.any
                  (CoreMemProc.firesIn after (E.scalar.view next.scalar)) = true
              · simp only [CoreMemDesign.edgeQuiesce, hp, Res.ok_bind, hc,
                  ↓reduceIte] at hr ⊢
                exact ih (Nat.le_of_succ_le_succ h) next after
                  (E.scalar.view next.scalar) next result hr
              · simp only [CoreMemDesign.edgeQuiesce, hp, Res.ok_bind, hc,
                  Bool.false_eq_true, ↓reduceIte] at hr ⊢
                exact hr

/-! The top-level step carries the event-slot limit through the same
successful-result monotonicity seam.  Inner statement and quiescence calls
remain the existing trusted route, while this theorem makes the outer fuel
parameter available to the fuel-free relation bridge. -/

theorem stepFuel_mono {limit limit' : Nat} (h : limit ≤ limit')
    (E : CoreMemDesign) (st : CoreMemState) (entry : SvState)
    (result : CoreMemState)
    (hr : E.stepFuel limit st entry = .ok result) :
    E.stepFuel limit' st entry = .ok result := by
  unfold CoreMemDesign.stepFuel at hr ⊢
  cases hp : E.prepareStep st entry with
  | timeout => simp [hp] at hr
  | unsupported msg => simp [hp] at hr
  | ok triple =>
      obtain ⟨pre, before, after⟩ := triple
      simp only [hp, Res.ok_bind] at hr ⊢
      exact edgeQuiesce_mono h E pre before after pre result hr

end LeanModels.Sv.Kernel
