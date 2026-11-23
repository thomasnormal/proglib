import LeanModels.Sv.SeqCycleObl
import LeanModels.Sv.Kernel.EdgePhaseConfluence
import LeanModels.Sv.Kernel.EdgeConfluence

/-!
# Concrete retained-resume frame

This module connects the parser-native evaluator frames to the retained
blocking cursor.  It is deliberately a two-leaf theorem.  The scheduler
relation and its progress argument remain in `EdgePhaseConfluence`.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

private theorem sv_set_commute_of_mem
    {st : SvState} {n m : String} {v w : LVec}
    (hn : n ∈ st.map Prod.fst) (hm : m ∈ st.map Prod.fst)
    (hneq : n ≠ m) (hnd : (st.map Prod.fst).Nodup) :
    SvState.set (SvState.set st n v) m w =
      SvState.set (SvState.set st m w) n v := by
  apply SvState.ext
  · have hm' : m ∈ (SvState.set st n v).map Prod.fst := by
      rw [SvState.keys_set (v := v) (h := hn)]
      exact hm
    have hn' : n ∈ (SvState.set st m w).map Prod.fst := by
      rw [SvState.keys_set (v := w) (h := hm)]
      exact hn
    rw [SvState.keys_set (v := w) (h := hm'),
      SvState.keys_set (v := v) (h := hn),
      SvState.keys_set (v := v) (h := hn'),
      SvState.keys_set (v := w) (h := hm)]
  · have hm' : m ∈ (SvState.set st n v).map Prod.fst := by
      rw [SvState.keys_set (v := v) (h := hn)]
      exact hm
    have hleft : ((SvState.set st n v).set m w).map Prod.fst = st.map Prod.fst := by
      rw [SvState.keys_set (v := w) (h := hm'), SvState.keys_set (v := v) (h := hn)]
    rw [hleft]
    exact hnd
  · intro q
    by_cases hqn : n = q
    · subst q
      simp [SvState.lookup_set, hneq, Ne.symm hneq]
    · by_cases hqm : m = q
      · subst q
        simp [SvState.lookup_set, hneq, Ne.symm hneq]
      · simp [SvState.lookup_set, hqn, hqm, Ne.symm hqn, Ne.symm hqm]

theorem CombCursor.two_blocking_scalar_cross_resume
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hdecl : xN.decl ≠ xM.decl)
    (hn : n ∈ view.map Prod.fst)
    (hm : m ∈ view.map Prod.fst)
    (hneq : n ≠ m)
    (hkeys : (view.map Prod.fst).Nodup)
    (hlocalN : SvState.lookup locals n = none)
    (hlocalM : SvState.lookup locals m = none)
    (htargetN : E.scalarTarget n = some widthN)
    (htargetM : E.scalarTarget m = some widthM)
    (htestN : PExpr.hasTestPlusargs eN = false)
    (htestM : PExpr.hasTestPlusargs eM = false)
    (hmemN : PExpr.hasMemoryRead eN = false)
    (hcallN : PExpr.hasFunctionCall eN = false)
    (hmemM : PExpr.hasMemoryRead eM = false)
    (hcallM : PExpr.hasFunctionCall eM = false)
    (hne : E.elems ≠ [])
    (hvalN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hreadM : ∀ y ∈ E.readsV env E.elems (some widthM) eM, y ≠ n)
    (hreadN : ∀ y ∈ E.readsV env E.elems (some widthN) eN, y ≠ m) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    cM.resume E (E.setScalarState st n vN) (SvState.set view n vN) =
        .ok (E.setScalarState (E.setScalarState st n vN) m vM,
          SvState.set (SvState.set view n vN) m vM, { work := [], locals := locals }) ∧
      cN.resume E (E.setScalarState st m vM) (SvState.set view m vM) =
        .ok (E.setScalarState (E.setScalarState st m vM) n vN,
          SvState.set (SvState.set view m vM) n vN, { work := [], locals := locals }) ∧
      E.setScalarState (E.setScalarState st n vN) m vM =
        E.setScalarState (E.setScalarState st m vM) n vN ∧
      SvState.set (SvState.set view n vN) m vM =
        SvState.set (SvState.set view m vM) n vN := by
  dsimp
  have hcrossM :
      E.evalExprLocals env E.elems (E.setScalarState st n vN)
          (some widthM) locals eM = .ok vM := by
    have heq := CoreMemDesign.edge_evalExprLocals_frame_of_readsV
      (v := vN) (locals := locals) hc hxN hmemM hcallM hne hreadM
    rw [← heq]
    exact hvalM
  have hcrossN :
      E.evalExprLocals env E.elems (E.setScalarState st m vM)
          (some widthN) locals eN = .ok vN := by
    have heq := CoreMemDesign.edge_evalExprLocals_frame_of_readsV
      (v := vM) (locals := locals) hc hxM hmemN hcallN hne hreadN
    rw [← heq]
    exact hvalN
  have hstate := CoreMemDesign.edge_setScalarState_commute_of_disjoint
    (vN := vN) (vM := vM) hc hxN hxM hdecl
  have hview := sv_set_commute_of_mem (v := vN) (w := vM) hn hm hneq hkeys
  have hresumeM :
      ({ work := [.stmt env (.blockingAssign m eM)], locals := locals } : CombCursor).resume
          E (E.setScalarState st n vN) (SvState.set view n vN) =
        .ok (E.setScalarState (E.setScalarState st n vN) m vM,
          SvState.set (SvState.set view n vN) m vM,
          { work := [], locals := locals }) := by
    simp [CombCursor.resume, CombWork.openNode, CoreMemDesign.execCombStmtFuel,
      hlocalM, htargetM, htestM, hcrossM]
  have hresumeN :
      ({ work := [.stmt env (.blockingAssign n eN)], locals := locals } : CombCursor).resume
          E (E.setScalarState st m vM) (SvState.set view m vM) =
        .ok (E.setScalarState (E.setScalarState st m vM) n vN,
          SvState.set (SvState.set view m vM) n vN,
          { work := [], locals := locals }) := by
    simp [CombCursor.resume, CombWork.openNode, CoreMemDesign.execCombStmtFuel,
      hlocalN, htargetN, htestN, hcrossN]
  exact ⟨hresumeM, hresumeN, hstate, hview⟩

#print axioms CombCursor.two_blocking_scalar_cross_resume

/-! The same retained-resume diamond with source-shaped driver closures.  The
closure receipts are intentionally separate for the two expressions and are
translated by the evaluator adapter before the cursor proof is invoked. -/
theorem CombCursor.two_blocking_scalar_cross_resume_of_driver_closure
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {processes : List PProcess} {fuelN fuelM : Nat}
    {namesN namesM : List String}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hdecl : xN.decl ≠ xM.decl)
    (hn : n ∈ view.map Prod.fst)
    (hm : m ∈ view.map Prod.fst)
    (hneq : n ≠ m)
    (hkeys : (view.map Prod.fst).Nodup)
    (hlocalN : SvState.lookup locals n = none)
    (hlocalM : SvState.lookup locals m = none)
    (htargetN : E.scalarTarget n = some widthN)
    (htargetM : E.scalarTarget m = some widthM)
    (htestN : PExpr.hasTestPlusargs eN = false)
    (htestM : PExpr.hasTestPlusargs eM = false)
    (hmemN : PExpr.hasMemoryRead eN = false)
    (hcallN : PExpr.hasFunctionCall eN = false)
    (hmemM : PExpr.hasMemoryRead eM = false)
    (hcallM : PExpr.hasFunctionCall eM = false)
    (hne : E.elems ≠ [])
    (hvalN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hclosureM : ∀ y ∈ E.readsV env E.elems (some widthM) eM,
      y ∈ coreMemReadNamesThroughDrivers processes fuelM namesM)
    (hclosureN : ∀ y ∈ E.readsV env E.elems (some widthN) eN,
      y ∈ coreMemReadNamesThroughDrivers processes fuelN namesN)
    (hguardM : ∀ y ∈ coreMemReadNamesThroughDrivers processes fuelM namesM, y ≠ n)
    (hguardN : ∀ y ∈ coreMemReadNamesThroughDrivers processes fuelN namesN, y ≠ m) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    cM.resume E (E.setScalarState st n vN) (SvState.set view n vN) =
        .ok (E.setScalarState (E.setScalarState st n vN) m vM,
          SvState.set (SvState.set view n vN) m vM, { work := [], locals := locals }) ∧
      cN.resume E (E.setScalarState st m vM) (SvState.set view m vM) =
        .ok (E.setScalarState (E.setScalarState st m vM) n vN,
          SvState.set (SvState.set view m vM) n vN, { work := [], locals := locals }) ∧
      E.setScalarState (E.setScalarState st n vN) m vM =
        E.setScalarState (E.setScalarState st m vM) n vN ∧
      SvState.set (SvState.set view n vN) m vM =
        SvState.set (SvState.set view m vM) n vN := by
  apply CombCursor.two_blocking_scalar_cross_resume
    hc hxN hxM hdecl hn hm hneq hkeys hlocalN hlocalM htargetN htargetM
    htestN htestM hmemN hcallN hmemM hcallM hne hvalN hvalM
  · exact fun y hy => by
      exact hguardM y (hclosureM y hy)
  · exact fun y hy => by
      exact hguardN y (hclosureN y hy)

/-! The concrete frame instantiates the retained scheduler's local diamond.
The only scheduler fact used here is the existing `CombPhaseStep` relation.
-/
theorem CombPhaseStep.two_blocking_scalar_diamond
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hdecl : xN.decl ≠ xM.decl)
    (hn : n ∈ view.map Prod.fst)
    (hm : m ∈ view.map Prod.fst)
    (hneq : n ≠ m)
    (hkeys : (view.map Prod.fst).Nodup)
    (hlocalN : SvState.lookup locals n = none)
    (hlocalM : SvState.lookup locals m = none)
    (htargetN : E.scalarTarget n = some widthN)
    (htargetM : E.scalarTarget m = some widthM)
    (htestN : PExpr.hasTestPlusargs eN = false)
    (htestM : PExpr.hasTestPlusargs eM = false)
    (hmemN : PExpr.hasMemoryRead eN = false)
    (hcallN : PExpr.hasFunctionCall eN = false)
    (hmemM : PExpr.hasMemoryRead eM = false)
    (hcallM : PExpr.hasFunctionCall eM = false)
    (hne : E.elems ≠ [])
    (hvalN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hreadM : ∀ y ∈ E.readsV env E.elems (some widthM) eM, y ≠ n)
    (hreadN : ∀ y ∈ E.readsV env E.elems (some widthN) eN, y ≠ m) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    ∃ u₁ u₂ z,
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₁ ∧
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₂ ∧
      CombPhaseStep E u₁ z ∧ CombPhaseStep E u₂ z := by
  dsimp
  let cN : CombCursor :=
    { work := [.stmt env (.blockingAssign n eN)], locals := locals }
  let cM : CombCursor :=
    { work := [.stmt env (.blockingAssign m eM)], locals := locals }
  have hfirstN : cN.resume E st view =
      .ok (E.setScalarState st n vN, SvState.set view n vN,
        { work := [], locals := locals }) := by
    exact CombCursor.resume_blocking_scalar hlocalN htargetN htestN hvalN
  have hfirstM : cM.resume E st view =
      .ok (E.setScalarState st m vM, SvState.set view m vM,
        { work := [], locals := locals }) := by
    exact CombCursor.resume_blocking_scalar hlocalM htargetM htestM hvalM
  have hcross := CombCursor.two_blocking_scalar_cross_resume
    hc hxN hxM hdecl hn hm hneq hkeys hlocalN hlocalM htargetN htargetM
    htestN htestM hmemN hcallN hmemM hcallM hne hvalN hvalM hreadM hreadN
  rcases hcross with ⟨h₂₁, h₁₂, hstate, hview⟩
  exact CombPhaseStep.two_cursor_commute
    (ha := rfl) hfirstN hfirstM h₂₁ h₁₂ hstate hview rfl rfl

#print axioms CombPhaseStep.two_blocking_scalar_diamond

end LeanModels.Sv.Kernel
