import LeanModels.Sv.Kernel.CombPhaseFrame

/-!
# Conditional observation confluence

This module records the semantic conditional form separately from the
whole-state NBA and blocking diamonds.  A hidden-name predicate identifies
the values a specification deliberately does not observe.  The evaluator
frame still comes from parser-native reads, including the continuous-driver
closure supplied by `EdgeConfluence`.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

def SvState.agreesOutside (hidden : List String) (left right : SvState) : Prop :=
  ∀ name, name ∉ hidden → SvState.lookup left name = SvState.lookup right name

theorem SvState.agreesOutside_two_set_of_mem
    {hidden : List String} {state : SvState}
    {n m : String} {valueN valueM valueN' valueM' : LVec}
    (hn : n ∈ hidden) (hm : m ∈ hidden) :
    SvState.agreesOutside hidden
      (SvState.set (SvState.set state n valueN) m valueM)
      (SvState.set (SvState.set state m valueM') n valueN') := by
  intro queried hqueried
  rw [SvState.lookup_set, SvState.lookup_set,
    SvState.lookup_set, SvState.lookup_set]
  have hnq : n ≠ queried := by
    intro heq
    subst queried
    exact hqueried hn
  have hmq : m ≠ queried := by
    intro heq
    subst queried
    exact hqueried hm
  simp [hnq, hmq]

theorem SvState.agreesOutside_set_of_mem
    {hidden : List String} {state : SvState} {value : LVec} {name : String}
    (hname : name ∈ hidden) :
    SvState.agreesOutside hidden state (SvState.set state name value) := by
  intro queried hqueried
  rw [SvState.lookup_set]
  by_cases hq : name = queried
  · exact False.elim (hqueried (hq ▸ hname))
  · simp [hq]

/-! The real retained resume and the observation frame can be packaged at one
    blocking scalar leaf. This is the smallest concrete bridge into the
    generic admission's per-step premise. -/
theorem CombCursor.resume_blocking_scalar_hidden_observation
    {E : CoreMemDesign} {hidden : List String}
    {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n : String} {value : PExpr} {width : Nat}
    {tail : List CombWork} {v : LVec}
    (hlocal : SvState.lookup locals n = none)
    (htarget : E.scalarTarget n = some width)
    (htest : PExpr.hasTestPlusargs value = false)
    (hvalue : E.evalExprLocals env E.elems st (some width) locals value = .ok v)
    (hname : n ∈ hidden) :
    ∃ next,
      CombCursor.resume E st view
          { work := .stmt env (.blockingAssign n value) :: tail, locals := locals } =
        .ok (E.setScalarState st n v, SvState.set view n v, next) ∧
      SvState.agreesOutside hidden view (SvState.set view n v) := by
  refine ⟨{ work := tail, locals := locals }, ?_, ?_⟩
  · exact CombCursor.resume_blocking_scalar hlocal htarget htest hvalue
  · exact SvState.agreesOutside_set_of_mem hname

#print axioms CombCursor.resume_blocking_scalar_hidden_observation

/-! The local two-process theorem quantifies both legal first selections and
their second selections.  It proves progress to empty active work and equality
of the observation outside the hidden targets.  It does not assert equality of
the hidden values or of the full `CoreMemState`. -/
theorem CombPhaseStep.two_blocking_scalar_hidden_observation_diamond
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {hidden : List String}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
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
    (hvalueN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalueM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hreadM : ∀ name ∈ E.readsV env E.elems (some widthM) eM, name ≠ n)
    (hreadN : ∀ name ∈ E.readsV env E.elems (some widthN) eN, name ≠ m)
    (hnHidden : n ∈ hidden) (hmHidden : m ∈ hidden) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    let s : CombPhaseState := { state := st, view := view, active := [cN, cM] }
    ∃ uN uM zN zM,
      CombPhaseStep E s uN ∧ CombPhaseStep E s uM ∧
      CombPhaseStep E uN zN ∧ CombPhaseStep E uM zM ∧
      zN.active = [] ∧ zM.active = [] ∧
      SvState.agreesOutside hidden zN.view zM.view := by
  dsimp
  let cN : CombCursor :=
    { work := [.stmt env (.blockingAssign n eN)], locals := locals }
  let cM : CombCursor :=
    { work := [.stmt env (.blockingAssign m eM)], locals := locals }
  let s : CombPhaseState := { state := st, view := view, active := [cN, cM] }
  let stN := E.setScalarState st n vN
  let stM := E.setScalarState st m vM
  let stNM := E.setScalarState stN m vM
  let stMN := E.setScalarState stM n vN
  let viewN := SvState.set view n vN
  let viewM := SvState.set view m vM
  let viewNM := SvState.set viewN m vM
  let viewMN := SvState.set viewM n vN
  have hvalueM' : E.evalExprLocals env E.elems stN (some widthM) locals eM = .ok vM := by
    have hframe := CoreMemDesign.edge_evalExprLocals_frame_of_readsV
      (elems := E.elems) (locals := locals) (v := vN)
      hc hxN hmemM hcallM hne hreadM
    rw [← hframe]
    exact hvalueM
  have hvalueN' : E.evalExprLocals env E.elems stM (some widthN) locals eN = .ok vN := by
    have hframe := CoreMemDesign.edge_evalExprLocals_frame_of_readsV
      (elems := E.elems) (locals := locals) (v := vM)
      hc hxM hmemN hcallN hne hreadN
    rw [← hframe]
    exact hvalueN
  have hresumeN : cN.resume E st view =
      .ok (stN, viewN, { work := [], locals := locals }) := by
    exact CombCursor.resume_blocking_scalar hlocalN htargetN htestN hvalueN
  have hresumeM : cM.resume E st view =
      .ok (stM, viewM, { work := [], locals := locals }) := by
    exact CombCursor.resume_blocking_scalar hlocalM htargetM htestM hvalueM
  have hresumeM' : cM.resume E stN viewN =
      .ok (stNM, viewNM, { work := [], locals := locals }) := by
    exact CombCursor.resume_blocking_scalar hlocalM htargetM htestM hvalueM'
  have hresumeN' : cN.resume E stM viewM =
      .ok (stMN, viewMN, { work := [], locals := locals }) := by
    exact CombCursor.resume_blocking_scalar hlocalN htargetN htestN hvalueN'
  let uN := s.after stN viewN { work := [], locals := locals } [] [cM]
  let uM := s.after stM viewM { work := [], locals := locals } [cN] []
  let zN := uN.after stNM viewNM { work := [], locals := locals } [] []
  let zM := uM.after stMN viewMN { work := [], locals := locals } [] []
  have hsN : CombPhaseStep E s uN := by
    apply CombPhaseStep.select (cursor := cN) (before := []) (after := [cM])
    · simp [s, cN, cM]
    · simpa [uN] using hresumeN
  have hsM : CombPhaseStep E s uM := by
    apply CombPhaseStep.select (cursor := cM) (before := [cN]) (after := [])
    · simp [s, cN, cM]
    · simpa [uM] using hresumeM
  have huN : CombPhaseStep E uN zN := by
    change CombPhaseStep E uN
      (uN.after stNM viewNM { work := [], locals := locals } [] [])
    apply CombPhaseStep.select (cursor := cM) (before := []) (after := [])
    · simp [uN, CombPhaseState.after]
    · change cM.resume E stN viewN =
        .ok (stNM, viewNM, { work := [], locals := locals })
      exact hresumeM'
  have huM : CombPhaseStep E uM zM := by
    change CombPhaseStep E uM
      (uM.after stMN viewMN { work := [], locals := locals } [] [])
    apply CombPhaseStep.select (cursor := cN) (before := []) (after := [])
    · simp [uM, CombPhaseState.after]
    · change cN.resume E stM viewM =
        .ok (stMN, viewMN, { work := [], locals := locals })
      exact hresumeN'
  have hobs : SvState.agreesOutside hidden viewNM viewMN := by
    dsimp [viewNM, viewMN, viewN, viewM]
    exact SvState.agreesOutside_two_set_of_mem hnHidden hmHidden
  refine ⟨uN, uM, zN, zM, hsN, hsM, huN, huM, ?_, ?_, ?_⟩
  · simp [zN, uN, CombPhaseState.after]
  · simp [zM, uM, CombPhaseState.after]
  · simpa [zN, zM, uN, uM, CombPhaseState.after] using hobs

#print axioms CombPhaseStep.two_blocking_scalar_hidden_observation_diamond

/-! The closure-backed adapter keeps the parser-native dependency walk at the
admission boundary.  The evaluator frame is reached only after every
`readsV` name is shown to lie in the transitive driver closure. -/
theorem CombPhaseStep.two_blocking_scalar_hidden_observation_diamond_of_driver_closure
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {hidden : List String} {processes : List PProcess}
    {fuelN fuelM : Nat} {namesN namesM : List String}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
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
    (hvalueN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalueM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hclosureM : ∀ y ∈ E.readsV env E.elems (some widthM) eM,
      y ∈ coreMemReadNamesThroughDrivers processes fuelM namesM)
    (hclosureN : ∀ y ∈ E.readsV env E.elems (some widthN) eN,
      y ∈ coreMemReadNamesThroughDrivers processes fuelN namesN)
    (hguardM : ∀ y ∈ coreMemReadNamesThroughDrivers processes fuelM namesM,
      y ≠ n)
    (hguardN : ∀ y ∈ coreMemReadNamesThroughDrivers processes fuelN namesN,
      y ≠ m)
    (hnHidden : n ∈ hidden) (hmHidden : m ∈ hidden) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    let s : CombPhaseState := { state := st, view := view, active := [cN, cM] }
    ∃ uN uM zN zM,
      CombPhaseStep E s uN ∧ CombPhaseStep E s uM ∧
      CombPhaseStep E uN zN ∧ CombPhaseStep E uM zM ∧
      zN.active = [] ∧ zM.active = [] ∧
      SvState.agreesOutside hidden zN.view zM.view := by
  have hreadM : ∀ y ∈ E.readsV env E.elems (some widthM) eM, y ≠ n := by
    intro y hy hneq
    exact (hguardM y (hclosureM y hy)) hneq
  have hreadN : ∀ y ∈ E.readsV env E.elems (some widthN) eN, y ≠ m := by
    intro y hy hneq
    exact (hguardN y (hclosureN y hy)) hneq
  exact CombPhaseStep.two_blocking_scalar_hidden_observation_diamond
    hc hxN hxM hlocalN hlocalM htargetN htargetM htestN htestM
    hmemN hcallN hmemM hcallM hne hvalueN hvalueM hreadM hreadN
    hnHidden hmHidden

#print axioms CombPhaseStep.two_blocking_scalar_hidden_observation_diamond_of_driver_closure

/-! The complete parser guard can feed the hidden-observation diamond for a
    two-process source slice.  The guard supplies only the directed race
    exclusions.  Evaluator values, closure receipts, and hidden targets remain
    explicit premises of this theorem. -/
theorem CombPhaseStep.two_blocking_scalar_hidden_observation_diamond_of_design_guard
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {hidden : List String} {p q : PProcess} {d : PDesign}
    (hg : CombPhaseGuard d)
    (hprocesses : d.processes = [p, q])
    (hcommon : coreMemHasCommonEventSourceThroughAssign [p, q] p q = true)
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
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
    (hvalueN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalueM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hclosureM : ∀ y ∈ E.readsV env E.elems (some widthM) eM,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames q))
    (hclosureN : ∀ y ∈ E.readsV env E.elems (some widthN) eN,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames p))
    (hnwrites : n ∈ coreMemProcBlockingWrites p)
    (hmwrites : m ∈ coreMemProcBlockingWrites q)
    (hnHidden : n ∈ hidden) (hmHidden : m ∈ hidden) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    let s : CombPhaseState := { state := st, view := view, active := [cN, cM] }
    ∃ uN uM zN zM,
      CombPhaseStep E s uN ∧ CombPhaseStep E s uM ∧
      CombPhaseStep E uN zN ∧ CombPhaseStep E uM zM ∧
      zN.active = [] ∧ zM.active = [] ∧
      SvState.agreesOutside hidden zN.view zM.view := by
  have hpair := CombPhaseGuard.two_process_read_write_exclusions
    (d := d) hg hprocesses hcommon
  apply CombPhaseStep.two_blocking_scalar_hidden_observation_diamond_of_driver_closure
    (processes := [p, q]) (fuelN := 32) (fuelM := 32)
    (namesN := coreMemPProcessReadNames p)
    (namesM := coreMemPProcessReadNames q)
    hc hxN hxM hlocalN hlocalM htargetN htargetM htestN htestM
    hmemN hcallN hmemM hcallM hne hvalueN hvalueM hclosureM hclosureN
  · intro y hy hyn
    exact (hpair.1 n hnwrites) (by simpa [hyn] using hy)
  · intro y hy hym
    exact (hpair.2 m hmwrites) (by simpa [hym] using hy)
  · exact hnHidden
  · exact hmHidden

#print axioms CombPhaseStep.two_blocking_scalar_hidden_observation_diamond_of_design_guard


/-! For the two-process class the local diamond can be folded into the actual
terminal-path relation.  The two paths have the same settled observation
outside the hidden names, while their hidden state may differ. -/
theorem CombPhaseTerminalPath.two_blocking_scalar_hidden_observation
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {hidden : List String} {processes : List PProcess}
    {fuelN fuelM : Nat} {namesN namesM : List String}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
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
    (hvalueN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalueM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hclosureM : ∀ y ∈ E.readsV env E.elems (some widthM) eM,
      y ∈ coreMemReadNamesThroughDrivers processes fuelM namesM)
    (hclosureN : ∀ y ∈ E.readsV env E.elems (some widthN) eN,
      y ∈ coreMemReadNamesThroughDrivers processes fuelN namesN)
    (hguardM : ∀ y ∈ coreMemReadNamesThroughDrivers processes fuelM namesM,
      y ≠ n)
    (hguardN : ∀ y ∈ coreMemReadNamesThroughDrivers processes fuelN namesN,
      y ≠ m)
    (hnHidden : n ∈ hidden) (hmHidden : m ∈ hidden) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    let s : CombPhaseState := { state := st, view := view, active := [cN, cM] }
    ∃ kN tN kM tM,
      CombPhaseTerminalPath E kN s tN ∧
      CombPhaseTerminalPath E kM s tM ∧
      SvState.agreesOutside hidden tN.view tM.view := by
  dsimp
  let cN : CombCursor :=
    { work := [.stmt env (.blockingAssign n eN)], locals := locals }
  let cM : CombCursor :=
    { work := [.stmt env (.blockingAssign m eM)], locals := locals }
  let s : CombPhaseState := { state := st, view := view, active := [cN, cM] }
  obtain ⟨uN, uM, zN, zM, hsN, hsM, huN, huM, hzN, hzM, hobs⟩ :=
    CombPhaseStep.two_blocking_scalar_hidden_observation_diamond_of_driver_closure
      hc hxN hxM hlocalN hlocalM htargetN htargetM htestN htestM
      hmemN hcallN hmemM hcallM hne hvalueN hvalueM hclosureM hclosureN
      hguardM hguardN hnHidden hmHidden
  have hstart : ¬ CombPhaseQuiescent s := by
    simp [CombPhaseQuiescent, s, cN, cM]
  have hmidN : ¬ CombPhaseQuiescent uN := by
    cases huN with
    | select hactive _ => simp [CombPhaseQuiescent, hactive]
  have hmidM : ¬ CombPhaseQuiescent uM := by
    cases huM with
    | select hactive _ => simp [CombPhaseQuiescent, hactive]
  have htermN : CombPhaseQuiescent zN := by simpa [CombPhaseQuiescent] using hzN
  have htermM : CombPhaseQuiescent zM := by simpa [CombPhaseQuiescent] using hzM
  refine ⟨2, zN, 2, zM, ?_, ?_, hobs⟩
  · exact .head hstart hsN (.head hmidN huN (.terminal htermN))
  · exact .head hstart hsM (.head hmidM huM (.terminal htermM))

#print axioms CombPhaseTerminalPath.two_blocking_scalar_hidden_observation

/-! The design-guard terminal adapter exposes the same conditional result at
    the retained terminal-path boundary.  It derives the two directed read
    exclusions from the complete parser guard and leaves all evaluator and
    closure receipts explicit. -/
theorem CombPhaseTerminalPath.two_blocking_scalar_hidden_observation_of_design_guard
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {hidden : List String} {p q : PProcess} {d : PDesign}
    (hg : CombPhaseGuard d)
    (hprocesses : d.processes = [p, q])
    (hcommon : coreMemHasCommonEventSourceThroughAssign [p, q] p q = true)
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
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
    (hvalueN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalueM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hclosureM : ∀ y ∈ E.readsV env E.elems (some widthM) eM,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames q))
    (hclosureN : ∀ y ∈ E.readsV env E.elems (some widthN) eN,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames p))
    (hnwrites : n ∈ coreMemProcBlockingWrites p)
    (hmwrites : m ∈ coreMemProcBlockingWrites q)
    (hnHidden : n ∈ hidden) (hmHidden : m ∈ hidden) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    let s : CombPhaseState := { state := st, view := view, active := [cN, cM] }
    ∃ kN tN kM tM,
      CombPhaseTerminalPath E kN s tN ∧
      CombPhaseTerminalPath E kM s tM ∧
      SvState.agreesOutside hidden tN.view tM.view := by
  have hpair := CombPhaseGuard.two_process_read_write_exclusions
    (d := d) hg hprocesses hcommon
  apply CombPhaseTerminalPath.two_blocking_scalar_hidden_observation
    (processes := [p, q]) (fuelN := 32) (fuelM := 32)
    (namesN := coreMemPProcessReadNames p)
    (namesM := coreMemPProcessReadNames q)
    hc hxN hxM hlocalN hlocalM htargetN htargetM htestN htestM
    hmemN hcallN hmemM hcallM hne hvalueN hvalueM hclosureM hclosureN
  · intro y hy hyn
    exact (hpair.1 n hnwrites) (by simpa [hyn] using hy)
  · intro y hy hym
    exact (hpair.2 m hmwrites) (by simpa [hym] using hy)
  · exact hnHidden
  · exact hmHidden

#print axioms CombPhaseTerminalPath.two_blocking_scalar_hidden_observation_of_design_guard

/-! A global conditional observation admission separates the two obligations
that are often accidentally conflated.  `resume_ok` and
`continuation_empty` establish progress for every active cursor.  The
per-step `preserves` field is a semantic observation invariant, so it does not
state terminal schedule independence as its own premise. -/
structure CombPhaseHiddenObservationAdmission
    (E : CoreMemDesign) (hidden : List String) where
  resume_ok : ∀ (s : CombPhaseState) (cursor : CombCursor), cursor ∈ s.active →
    ∃ state view next, cursor.resume E s.state s.view = .ok (state, view, next)
  continuation_empty : ∀ (s : CombPhaseState) (cursor : CombCursor)
    (state : CoreMemState) (view : SvState) (next : CombCursor),
    cursor ∈ s.active →
    cursor.resume E s.state s.view = .ok (state, view, next) → next.work = []
  preserves : ∀ {s t : CombPhaseState}, CombPhaseStep E s t →
    SvState.agreesOutside hidden s.view t.view

/-! This receipt form makes the per-step observation premise constructive for
    scalar leaves. Each active cursor supplies its own hidden target and exact
    view-update equation. No terminal-path equality is part of the receipt. -/
structure CombPhaseScalarHiddenResumeReceipt
    (E : CoreMemDesign) (hidden : List String) where
  resume_hidden : ∀ (s : CombPhaseState) (cursor : CombCursor), cursor ∈ s.active →
    ∃ state view next name value,
      cursor.resume E s.state s.view = .ok (state, view, next) ∧
      next.work = [] ∧ name ∈ hidden ∧
      view = SvState.set s.view name value

theorem CombPhaseScalarHiddenResumeReceipt.toAdmission
    {E : CoreMemDesign} {hidden : List String}
    (receipt : CombPhaseScalarHiddenResumeReceipt E hidden) :
    CombPhaseHiddenObservationAdmission E hidden := by
  constructor
  · intro s cursor hcursor
    obtain ⟨state, view, next, name, value, hresume, _, _, _⟩ :=
      receipt.resume_hidden s cursor hcursor
    exact ⟨state, view, next, hresume⟩
  · intro s cursor state view next hcursor hresume
    obtain ⟨state', view', next', name, value, hresume', hempty, _, hview⟩ :=
      receipt.resume_hidden s cursor hcursor
    have : state = state' ∧ view = view' ∧ next = next' := by
      simpa [hresume] using hresume'
    exact this.2.2 ▸ hempty
  · intro s t hstep
    cases hstep with
    | @select before after cursor next state view hactive hresume =>
        obtain ⟨state', view', next', name, value, hresume', _, hname, hview⟩ :=
          receipt.resume_hidden s cursor (by simp [hactive])
        have hsame : state = state' ∧ view = view' ∧ next = next' := by
          simpa [hresume] using hresume'
        change SvState.agreesOutside hidden s.view view
        have hview_eq : view = SvState.set s.view name value := by
          exact hsame.2.1.trans hview
        rw [hview_eq]
        exact SvState.agreesOutside_set_of_mem hname

#print axioms CombPhaseScalarHiddenResumeReceipt.toAdmission

/-! The same frame at the scheduler boundary is stated directly over the real
    `CombPhaseStep.select` constructor. This keeps the selected cursor and its
    source-order position explicit. -/
theorem CombPhaseStep.select_blocking_scalar_hidden_observation
    {E : CoreMemDesign} {hidden : List String}
    {s : CombPhaseState} {before after : List CombCursor}
    {cursor next : CombCursor} {state : CoreMemState} {view : SvState}
    {env : IEnv} {n : String} {value : PExpr} {width : Nat}
    {tail : List CombWork} {locals : SvState} {v : LVec}
    (hactive : s.active = before ++ cursor :: after)
    (hwork : cursor.work = .stmt env (.blockingAssign n value) :: tail)
    (hlocals : cursor.locals = locals)
    (hlocal : SvState.lookup locals n = none)
    (htarget : E.scalarTarget n = some width)
    (htest : PExpr.hasTestPlusargs value = false)
    (hvalue : E.evalExprLocals env E.elems s.state (some width) locals value = .ok v)
    (hname : n ∈ hidden) :
    SvState.agreesOutside hidden s.view
      (s.after (E.setScalarState s.state n v) (SvState.set s.view n v)
        { work := tail, locals := locals } before after).view := by
  have hresume : cursor.resume E s.state s.view =
      .ok (E.setScalarState s.state n v, SvState.set s.view n v,
        { work := tail, locals := locals }) := by
    cases cursor with
    | mk cursorWork cursorLocals =>
        simp only at hwork hlocals ⊢
        subst cursorWork
        subst cursorLocals
        exact CombCursor.resume_blocking_scalar hlocal htarget htest hvalue
  have hstep := CombPhaseStep.select hactive hresume
  change SvState.agreesOutside hidden s.view (SvState.set s.view n v)
  exact SvState.agreesOutside_set_of_mem hname

#print axioms CombPhaseStep.select_blocking_scalar_hidden_observation

theorem CombPhaseHiddenObservationAdmission.progress
    {E : CoreMemDesign} {hidden : List String}
    (ad : CombPhaseHiddenObservationAdmission E hidden)
    {s : CombPhaseState} (hn : s.active ≠ []) :
    ∃ t, CombPhaseStep E s t := by
  cases hxs : s.active with
  | nil => exact False.elim (hn hxs)
  | cons cursor rest =>
      have hmem : cursor ∈ s.active := by simp [hxs]
      obtain ⟨state, view, next, hresume⟩ := ad.resume_ok s cursor hmem
      exact ⟨s.after state view next [] rest, .select hxs hresume⟩

theorem CombPhaseHiddenObservationAdmission.terminal_agreesOutside
    {E : CoreMemDesign} {hidden : List String}
    (ad : CombPhaseHiddenObservationAdmission E hidden)
    {s t : CombPhaseState} {n : Nat}
    (hp : CombPhaseTerminalPath E n s t) :
    SvState.agreesOutside hidden s.view t.view := by
  induction hp with
  | terminal hterm =>
      intro name hname
      rfl
  | @head n s u t hn hstep htail ih =>
      intro name hname
      have hfirst := ad.preserves hstep name hname
      have hrest := ih name hname
      exact hfirst.trans hrest

theorem CombPhaseHiddenObservationAdmission.exists_terminal
    {E : CoreMemDesign} {hidden : List String}
    (ad : CombPhaseHiddenObservationAdmission E hidden)
    (s : CombPhaseState) :
    ∃ n t, CombPhaseTerminalPath E n s t := by
  have aux : ∀ k, ∀ s : CombPhaseState, s.active.length = k →
      ∃ n t, CombPhaseTerminalPath E n s t := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro s hlen
        by_cases hempty : CombPhaseQuiescent s
        · exact ⟨0, s, .terminal hempty⟩
        · have hnonempty : s.active ≠ [] := by
            simpa [CombPhaseQuiescent] using hempty
          obtain ⟨cursor, rest, hsplit⟩ := List.exists_cons_of_ne_nil hnonempty
          have hmem : cursor ∈ s.active := by simp [hsplit]
          obtain ⟨state, view, next, hresume⟩ := ad.resume_ok s cursor hmem
          have hemptyNext := ad.continuation_empty s cursor state view next hmem hresume
          let u := s.after state view next [] rest
          have hstep : CombPhaseStep E s u := by
            exact .select (by simpa [hsplit, u]) hresume
          have hlt : u.active.length < k := by
            have hlen' : s.active.length = rest.length + 1 := by simp [hsplit]
            simp [u, CombPhaseState.after, hemptyNext]
            omega
          obtain ⟨n, t, htail⟩ := ih u.active.length hlt u rfl
          exact ⟨n + 1, t, .head hempty hstep htail⟩
  exact aux s.active.length s rfl

#print axioms CombPhaseHiddenObservationAdmission.progress
#print axioms CombPhaseHiddenObservationAdmission.terminal_agreesOutside
#print axioms CombPhaseHiddenObservationAdmission.exists_terminal

end LeanModels.Sv.Kernel
