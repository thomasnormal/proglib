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
  dsimp
  have hcross := CoreMemDesign.edge_evalExprLocals_two_expr_cross_write_frame_of_driver_closure
    (processes := processes) (fuelN := fuelN) (fuelM := fuelM)
    (namesN := namesN) (namesM := namesM) (locals := locals) (vN := vN) (vM := vM)
    hc hxN hxM hmemN hcallN hmemM hcallM hne
    hclosureN hclosureM hguardM hguardN
  have hcrossM :
      E.evalExprLocals env E.elems (E.setScalarState st n vN)
          (some widthM) locals eM = .ok vM := by
    rw [hcross.1]
    exact hvalM
  have hcrossN :
      E.evalExprLocals env E.elems (E.setScalarState st m vM)
          (some widthN) locals eN = .ok vN := by
    rw [hcross.2]
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

theorem CombPhaseStep.two_blocking_scalar_diamond_of_driver_closure
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
    ∃ u₁ u₂ z,
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₁ ∧
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₂ ∧
      CombPhaseStep E u₁ z ∧ CombPhaseStep E u₂ z := by
  dsimp
  exact CombPhaseStep.two_blocking_scalar_diamond
    hc hxN hxM hdecl hn hm hneq hkeys hlocalN hlocalM htargetN htargetM
    htestN htestM hmemN hcallN hmemM hcallM hne hvalN hvalM
    (fun y hy => hguardM y (hclosureM y hy))
    (fun y hy => hguardN y (hclosureN y hy))

/-! The two-process parser guard can now feed the retained-resume diamond
    directly.  The write-membership premises identify the source targets, and
    the pair guard supplies the opposite-process exclusions for the evaluator
    closures. -/
theorem CombPhaseStep.two_blocking_scalar_diamond_of_two_process_guard
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {p q : PProcess}
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
      y ∈ coreMemReadNamesThroughDrivers [p, q] 3 (coreMemPProcessReadNames q))
    (hclosureN : ∀ y ∈ E.readsV env E.elems (some widthN) eN,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 3 (coreMemPProcessReadNames p))
    (hnwrites : n ∈ coreMemProcBlockingWrites p)
    (hmwrites : m ∈ coreMemProcBlockingWrites q)
    (hguard : coreMemEdgeBlockingReadRaceThroughAssign [p, q] = false)
    (hcommon : coreMemHasCommonEventSourceThroughAssign [p, q] p q = true) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    ∃ u₁ u₂ z,
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₁ ∧
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₂ ∧
      CombPhaseStep E u₁ z ∧ CombPhaseStep E u₂ z := by
  have hpair := coreMemEdgeBlockingReadRacePairThroughAssign_false_of_two hguard hcommon
  apply CombPhaseStep.two_blocking_scalar_diamond_of_driver_closure
    (processes := [p, q]) (fuelN := 3) (fuelM := 3)
    (namesN := coreMemPProcessReadNames p)
    (namesM := coreMemPProcessReadNames q)
    hc hxN hxM hdecl hn hm hneq hkeys hlocalN hlocalM htargetN htargetM
    htestN htestM hmemN hcallN hmemM hcallM hne hvalN hvalM hclosureM hclosureN
  · intro y hy hyn
    exact (hpair.1 n hnwrites) (by simpa [hyn] using hy)
  · intro y hy hym
    exact (hpair.2 m hmwrites) (by simpa [hym] using hy)

/-! The design-level wrapper consumes the complete parser guard.  It keeps the
same exact evaluator and cursor premises as the source-slice theorem while
obtaining the two directed read exclusions from `CombPhaseGuard` itself. -/
theorem CombPhaseStep.two_blocking_scalar_diamond_of_design_guard
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {d : PDesign} {p q : PProcess}
    (hg : CombPhaseGuard d)
    (hprocesses : d.processes = [p, q])
    (hcommon : coreMemHasCommonEventSourceThroughAssign [p, q] p q = true)
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
      y ∈ coreMemReadNamesThroughDrivers [p, q] 3
        (coreMemPProcessReadNames q))
    (hclosureN : ∀ y ∈ E.readsV env E.elems (some widthN) eN,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 3
        (coreMemPProcessReadNames p))
    (hnwrites : n ∈ coreMemProcBlockingWrites p)
    (hmwrites : m ∈ coreMemProcBlockingWrites q) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    ∃ u₁ u₂ z,
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₁ ∧
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₂ ∧
      CombPhaseStep E u₁ z ∧ CombPhaseStep E u₂ z := by
  apply CombPhaseStep.two_blocking_scalar_diamond_of_two_process_guard
    hc hxN hxM hdecl hn hm hneq hkeys hlocalN hlocalM htargetN htargetM
    htestN htestM hmemN hcallN hmemM hcallM hne hvalN hvalM
    hclosureM hclosureN hnwrites hmwrites
    (by simpa [hprocesses] using hg.no_blocking_read_after_closure)
    hcommon

/-! The two-process source route supplies the canonical runner result to the
concrete terminal path.  The runner equation is derived from the same
evaluator values and first compaction receipt used by the retained resumes.
The final compaction receipt is explicit because the terminal path stores the
uncompacted scalar state while `runCombInitialWithView` returns its compacted
state. -/
theorem CombPhaseTerminalPath.two_blocking_scalar_executor_endpoint
    {E : CoreMemDesign} {st : CoreMemState} {view : SvState}
    {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hdecl : xN.decl ≠ xM.decl)
    (hn : n ∈ view.map Prod.fst)
    (hm : m ∈ view.map Prod.fst)
    (hneq : n ≠ m)
    (hkeys : (view.map Prod.fst).Nodup)
    (htargetN : E.scalarTarget n = some widthN)
    (htargetM : E.scalarTarget m = some widthM)
    (htestN : PExpr.hasTestPlusargs eN = false)
    (htestM : PExpr.hasTestPlusargs eM = false)
    (hmemN : PExpr.hasMemoryRead eN = false)
    (hcallN : PExpr.hasFunctionCall eN = false)
    (hmemM : PExpr.hasMemoryRead eM = false)
    (hcallM : PExpr.hasFunctionCall eM = false)
    (hne : E.elems ≠ [])
    (hvalueN : E.evalExprLocals E.env E.elems st (some widthN) [] eN = .ok vN)
    (hvalueM : E.evalExprLocals E.env E.elems st (some widthM) [] eM = .ok vM)
    (hreadM : ∀ y ∈
      (instExpr2 E.env (if E.elems.isEmpty then E.elems else E.elems)
        (some widthM) eM).idents, y ≠ n)
    (hreadN : ∀ y ∈
      (instExpr2 E.env (if E.elems.isEmpty then E.elems else E.elems)
        (some widthN) eN).idents, y ≠ m)
    (hcompactN : E.compactScalar (E.setScalarState st n vN)
        (SvState.set view n vN) = E.setScalarState st n vN)
    (hcompactFinal : E.compactScalar
        (E.setScalarState (E.setScalarState st n vN) m vM)
        (SvState.set (SvState.set view n vN) m vM) =
      E.setScalarState (E.setScalarState st n vN) m vM) :
    ∃ k t,
      CombPhaseTerminalPath E k
          { state := st, view := view,
            active := [
              { work := [.stmt E.env (.blockingAssign n eN)], locals := [] },
              { work := [.stmt E.env (.blockingAssign m eM)], locals := [] }] } t ∧
      t = { state := E.setScalarState (E.setScalarState st n vN) m vM,
            view := SvState.set (SvState.set view n vN) m vM, active := [] } ∧
      E.runCombInitialWithView st view
          [.comb (.blockingAssign n eN), .comb (.blockingAssign m eM)] =
        .ok (E.setScalarState (E.setScalarState st n vN) m vM,
          SvState.set (SvState.set view n vN) m vM) := by
  let cN : CombCursor :=
    { work := [.stmt E.env (.blockingAssign n eN)], locals := [] }
  let cM : CombCursor :=
    { work := [.stmt E.env (.blockingAssign m eM)], locals := [] }
  let s : CombPhaseState := { state := st, view := view, active := [cN, cM] }
  have hfirstN : cN.resume E st view =
      .ok (E.setScalarState st n vN, SvState.set view n vN,
        { work := [], locals := [] }) := by
    exact CombCursor.resume_blocking_scalar rfl htargetN htestN hvalueN
  have hfirstM : cM.resume E st view =
      .ok (E.setScalarState st m vM, SvState.set view m vM,
        { work := [], locals := [] }) := by
    exact CombCursor.resume_blocking_scalar rfl htargetM htestM hvalueM
  have hreadMV : ∀ y ∈ E.readsV E.env E.elems (some widthM) eM, y ≠ n := by
    intro y hy
    rw [CoreMemDesign.edge_readsV_eq_instantiated_idents_of_pure hmemM hne] at hy
    exact hreadM y hy
  have hreadNV : ∀ y ∈ E.readsV E.env E.elems (some widthN) eN, y ≠ m := by
    intro y hy
    rw [CoreMemDesign.edge_readsV_eq_instantiated_idents_of_pure hmemN hne] at hy
    exact hreadN y hy
  have hcross := CombCursor.two_blocking_scalar_cross_resume
    (env := E.env) (locals := []) hc hxN hxM hdecl hn hm hneq hkeys
    rfl rfl htargetN htargetM htestN htestM hmemN hcallN hmemM hcallM hne
    hvalueN hvalueM hreadMV hreadNV
  rcases hcross with ⟨h₂₁, h₁₂, hstate, hview⟩
  have hpaths := CombPhaseTerminalPath.two_cursor_terminal
    (s := s) (c₁ := cN) (c₂ := cM) (ha := rfl)
    (h₁ := hfirstN) (h₂ := hfirstM)
    (h₂₁ := h₂₁) (h₁₂ := h₁₂) hstate hview rfl rfl
  rcases hpaths with ⟨k, t, k₂, t₂, hp₁, hp₂, ht_endpoint, ht₂_endpoint⟩
  have hvalueM' : E.evalExprLocals E.env E.elems
      (E.setScalarState st n vN) (some widthM) [] eM = .ok vM := by
    have hframe := CoreMemDesign.edge_evalExprLocals_frame_of_instantiated_reads
      (v := vN) (locals := []) hc hxN hmemM hcallM hne hreadM
    rw [← hframe]
    exact hvalueM
  have hrun := CoreMemDesign.runCombInitialWithView_two_blocking_scalar
    htargetN htargetM htestN htestM hvalueN hcompactN hvalueM'
  rw [hcompactFinal] at hrun
  refine ⟨k, t, ?_, ?_, hrun⟩
  · simpa [s, cN, cM] using hp₁
  · simpa [hstate, hview] using ht_endpoint

#print axioms CombPhaseStep.two_blocking_scalar_diamond_of_design_guard
#print axioms CombPhaseTerminalPath.two_blocking_scalar_executor_endpoint

end LeanModels.Sv.Kernel
