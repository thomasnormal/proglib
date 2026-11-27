import LeanModels.Sv.Kernel.CoreMemExec

/-!
# What the clocked theory needs from the step (`LeanModels.Sv.Kernel`, the clocked tactics' theory)

**Status: derived from the ordinary E route.** The clocked theory (`SeqCycle.lean`, `SeqCycleObl.lean`,
`SeqCycleRuns.lean`, the clocked tactics) reads the route's slot function `CoreMemDesign.step`, its run
`runCoreMemRows` and its instantiation `PDesign.instantiateCoreMemFrom` ONLY through the lemmas of this file. They are
the interface between the semantics and the clocked views, and the specification a later definition of the slot (for
example one derived from a scheduler of IEEE 1800-2023 §4) must meet on the clocked fragment: when the step changes,
these lemmas are re-proved and nothing else of the clocked theory changes.

The statements (each proved once, below; nothing else in the clocked files unfolds `step`, `prepareStep`, `edgePass`,
`edgeQuiesce`, `settleCanonical` or `settleAssignQuiesce`):

* `CoreMemDesign.settleCanonical_of_fixpoint`: the continuous-assign region of a slot (`settleCanonical`, the route's
  quiesce loop over source-order passes, §4.5 and §10.3) returns the first pass's result, or the second's, whenever the
  second pass leaves the first pass's view unchanged (the first pass reached the fixpoint).
* `CoreMemDesign.step_of_onePass`: on a design with no `always_comb`, `always_latch` or `always @*` process, a slot whose
  first round (the inputs applied, the region settled twice, the edge processes whose event occurred between the slot's
  start view and the settled view run in source order, the nonblocking commit of their scalar and memory updates, the
  region settled twice) causes no further edge event (§4.4, §4.5) IS that round.
* `runCoreMemRows_cons`: the route's run of a nonempty row is the step on that row, then the run of the rest.
* `CoreMemDesign.initialState_of_quiet`: on a design with no `initial`, `always_comb` or `always_latch` process and no
  `$readmemh`, the route's time-zero state is one source-order pass of its continuous assigns (`settleAssign`, §10.3)
  from its declaration-initialized state `CoreMemDesign.initial` (no process body runs at time zero; the drivers are
  evaluated, §4.5). It is not `CoreMemDesign.initial` itself as soon as a continuous assign drives a value other than
  the target's x/z start (`assign y = 1'b1;`, the semantics lane's receipt `sem2/initial_quiet_assign`).
* `coreMemClockResetViol_none`: the route's clock and reset source check admits every design (the route iterates
  NBA-caused events in the slot instead); so an internally driven clock or reset is excluded by the clocked obligations
  (`oblNoInputWrite`, `oblReset`), not by the instantiation.

The step's present body reaches them through the semantics lane's conservativity theorem
`CoreMemDesign.step_eq_stepOnePass_of_no_followup`.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-- The state a slot starts its continuous-assign region from: the entry's inputs applied to the scalar store and to
the input memories, the store normalized to its cache. -/
def CoreMemDesign.inputState (E : CoreMemDesign) (st : CoreMemState) (entry : SvState) : CoreMemState :=
  E.normalizeScalar { st with memory := E.applyMemoryInputs entry st.memory } (E.scalar.applyInputs st.scalar entry)

/-- The state the edge round commits to: the scalar nonblocking updates committed on the store the edge bodies left, the
memory committed as given. -/
def CoreMemDesign.committedState (E : CoreMemDesign) (r : CoreMemExecResult) (m : MemState) : CoreMemState :=
  { E.normalizeScalar r.state (E.scalarEdge.commit r.state.scalar r.scalarQ) with memory := m }

/-- Some edge process of the design has its event from the view `a` to the view `b`. -/
def CoreMemDesign.firesAny (E : CoreMemDesign) (a b : SvState) : Bool :=
  E.processes.toList.any (CoreMemProc.firesIn a b)

/-- **The continuous-assign region of a slot**: when a second source-order pass leaves the first pass's view unchanged,
the route's quiesce loop returns the first pass's result or the second's. -/
theorem CoreMemDesign.settleCanonical_of_fixpoint {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st s1 s2 : CoreMemState} {procs : List CoreMemProc}
    (h1 : E.settleAssign env elems st procs = .ok s1) (h2 : E.settleAssign env elems s1 procs = .ok s2)
    (hv : E.scalar.view s2.scalar = E.scalar.view s1.scalar) :
    ∃ s, E.settleCanonical env elems st procs = .ok s ∧ (s = s1 ∨ s = s2) := by
  unfold CoreMemDesign.settleCanonical
  rw [show (4096 : Nat) = 4095 + 1 from rfl, CoreMemDesign.settleAssignQuiesce]
  simp only [h1, Res.ok_bind]
  cases hb : (E.scalar.view st.scalar == E.scalar.view s1.scalar) with
  | true => exact ⟨s1, by simp, Or.inl rfl⟩
  | false =>
      refine ⟨s2, ?_, Or.inr rfl⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show (4095 : Nat) = 4094 + 1 from rfl, CoreMemDesign.settleAssignQuiesce]
      simp [h2, hv]

#print axioms CoreMemDesign.settleCanonical_of_fixpoint

/-- **One round of a slot is the slot** when it causes no further edge event, on a design with no `always_comb`,
`always_latch` or `always @*` process. -/
theorem CoreMemDesign.step_of_onePass {E : CoreMemDesign} {st : CoreMemState} {entry : SvState}
    (hcomb : E.hasComb = false) (himp : E.hasImplicit = false)
    {pre0 pre s3 next : CoreMemState} {edge : CoreMemExecResult} {m : MemState}
    (h0 : E.settleCanonical E.env E.elems (E.inputState st entry) E.processes.toList = .ok pre0)
    (h1 : E.settleCanonical E.env E.elems pre0 E.processes.toList = .ok pre)
    (he : E.runEdges E.env E.elems pre (E.scalar.view st.scalar) (E.scalar.view pre.scalar) E.processes.toList =
      .ok edge)
    (hm : edge.state.memory.commitNba edge.memoryQ = some m)
    (h3 : E.settleCanonical E.env E.elems (E.committedState edge m) E.processes.toList = .ok s3)
    (h4 : E.settleCanonical E.env E.elems s3 E.processes.toList = .ok next)
    (hq : E.firesAny (E.scalar.view pre.scalar) (E.scalar.view next.scalar) = false) :
    E.step st entry = .ok next := by
  apply CoreMemDesign.step_eq_stepOnePass_of_no_followup
  have hp : E.prepareStep st entry = .ok (pre, E.scalar.view st.scalar, E.scalar.view pre.scalar) := by
    unfold CoreMemDesign.prepareStep
    simp only [CoreMemDesign.inputState] at h0
    simp [h0, hcomb, himp, h1]
  have hpass : E.edgePass pre (E.scalar.view st.scalar) (E.scalar.view pre.scalar) pre = .ok next := by
    unfold CoreMemDesign.edgePass
    simp only [CoreMemDesign.committedState] at h3
    simp [he, hm, h3, hcomb, himp, h4]
  unfold CoreMemDesign.stepOnePassTrace
  simp only [hp, hpass, Res.ok_bind, Res.ok.injEq, Prod.mk.injEq, eq_self_iff_true, true_and]
  refine Eq.trans ?_ hq
  exact congrArg E.processes.toList.any (funext fun p => by cases p <;> rfl)

#print axioms CoreMemDesign.step_of_onePass

/-! The comb-capable one-pass bridge keeps the source-shaped comb settlement
    equations explicit.  Unlike `step_of_onePass`, it does not infer a
    no-comb fact from the profile; callers provide the actual `prepareStep`
    and `edgePass` results produced by canonical E. -/
theorem CoreMemDesign.step_of_onePass_comb {E : CoreMemDesign} {st : CoreMemState} {entry : SvState}
    {pre : CoreMemState} {next : CoreMemState}
    (hprepare : E.prepareStep st entry =
      .ok (pre, E.scalar.view st.scalar, E.scalar.view pre.scalar))
    (hpass : E.edgePass pre (E.scalar.view st.scalar) (E.scalar.view pre.scalar) pre = .ok next)
    (hnoFollowup : E.processes.toList.any
      (CoreMemProc.firesIn (E.scalar.view pre.scalar) (E.scalar.view next.scalar)) = false) :
    E.step st entry = .ok next := by
  apply CoreMemDesign.step_eq_stepOnePass_of_no_followup
  unfold CoreMemDesign.stepOnePassTrace
  have hno : E.processes.any (CoreMemProc.firesIn
      (E.scalar.view pre.scalar) (E.scalar.view next.scalar)) = false := by
    rw [← Array.any_toList]
    exact hnoFollowup
  simp [hprepare, hpass, hno]

#print axioms CoreMemDesign.step_of_onePass_comb

theorem CoreMemDesign.runCombSettleQuiesce_succ {E : CoreMemDesign} {n : Nat}
    {before current : CoreMemState} {procs : List CoreMemProc} :
    E.runCombSettleQuiesce (n + 1) before current procs = (do
      let combed ← E.runComb before current procs
      let settled ← E.settleCanonical E.env E.elems combed procs
      let beforeView := E.scalar.view current.scalar
      let settledView := E.scalar.view settled.scalar
      if beforeView == settledView then
        .ok settled
      else
        E.runCombSettleQuiesce n combed settled procs) := by
  rfl

#print axioms CoreMemDesign.runCombSettleQuiesce_succ

/-- The source-shaped pre-edge active region when a design contains an
`always_comb` process.  This equation is deliberately stated at the ordinary
executor boundary: it does not lower the body to a continuous assignment. -/
theorem CoreMemDesign.comb_settle_pre {E : CoreMemDesign} {st : CoreMemState} {entry : SvState}
    (hcomb : E.hasComb = true) (himp : E.hasImplicit = false) :
    E.prepareStep st entry = (do
      let inputStore := E.scalar.applyInputs st.scalar entry
      let memoryInput := E.applyMemoryInputs entry st.memory
      let inputState := E.normalizeScalar { st with memory := memoryInput } inputStore
      let pre0 ← E.settleCanonical E.env E.elems inputState E.processes.toList
      let preComb ← E.runCombSettleQuiesce 4096 st pre0 E.processes.toList
      let pre ← E.settleCanonical E.env E.elems preComb E.processes.toList
      .ok (pre, E.scalar.view st.scalar, E.scalar.view pre.scalar)) := by
  simp [CoreMemDesign.prepareStep, hcomb, himp]

/-- The source-shaped post-edge active region when a design contains an
`always_comb` process.  The comb runner is after the NBA commit and after the
ordinary continuous-assignment settle, exactly as in `CoreMemDesign.edgePass`.
-/
theorem CoreMemDesign.comb_settle_post {E : CoreMemDesign} {st : CoreMemState}
    {before after : SvState} {combBefore : CoreMemState} (hcomb : E.hasComb = true) (himp : E.hasImplicit = false) :
    E.edgePass st before after combBefore = (do
      let edge ← E.runEdges E.env E.elems st before after E.processes.toList
      let committedStore := E.scalarEdge.commit edge.state.scalar edge.scalarQ
      let memory ← match edge.state.memory.commitNba edge.memoryQ with
        | some m => .ok m
        | none => .unsupported "10.4.2: memory NBA commit lost its declaration identity"
      let committed := E.normalizeScalar edge.state committedStore
      let settled ← E.settleCanonical E.env E.elems { committed with memory } E.processes.toList
      let combed ← E.runCombSettleQuiesce 4096 combBefore settled E.processes.toList
      .ok combed) := by
  simp [CoreMemDesign.edgePass, hcomb, himp]
  rfl

/-- Exact time-zero equation for a design with a retained combinational
region.  The declaration/continuous settle is followed by comb activation and
one final continuous settle; no fixed result is selected when the executor
refuses to quiesce. -/
theorem CoreMemDesign.initialState_of_quiet_comb {E : CoreMemDesign}
    (hni : ∀ p ∈ E.processes.toList, ∀ b, p ≠ .initial b)
    (hrm : E.readmemh = []) :
    E.initialState = (do
      let declared ← E.execDeclInitializers E.initial E.declInitializers
      let settled ← E.settleCanonical E.env E.elems declared E.processes.toList
      if !E.hasComb then
        .ok settled
      else
        let (settled, settledView) ←
          E.settleAssignWithView E.env E.elems settled (E.scalar.view settled.scalar) E.processes.toList
        let combed ← E.runCombInitialQuiesce 4096 settled E.processes.toList
        let combedView := E.scalar.view combed.scalar
        let (final, _) ← E.settleAssignWithView E.env E.elems combed combedView E.processes.toList
        .ok final) := by
  unfold CoreMemDesign.initialState
  rw [List.filterMap_eq_nil_iff.mpr (fun p hp => ?_)]
  · simp [hrm, CoreMemDesign.settleCanonical, CoreMemDesign.initialState]
  · cases p with
    | initial b => exact absurd rfl (hni _ hp b)
    | _ => rfl

/-- **The route's run of a nonempty row** is the step on it, then the run of the rest. -/
theorem runCoreMemRows_cons {E : CoreMemDesign} {st : CoreMemState} {row : SvState} {rest : List SvState}
    (hrow : row.isEmpty = false) :
    runCoreMemRows E st (row :: rest) = (do
      let st' ← E.step st row
      let tail ← runCoreMemRows E st' rest
      .ok (st' :: tail)) := by
  simp [runCoreMemRows, hrow]

#print axioms runCoreMemRows_cons

/-- **The route's time-zero state** on a design with no `initial`, `always_comb` or `always_latch` process and no
`$readmemh` is the canonical quiescent settle of its continuous assigns
(`settleCanonical`, §§4.5 and 10.3) from its declaration-initialized state
`CoreMemDesign.initial`. -/
theorem CoreMemDesign.initialState_of_quiet {E : CoreMemDesign}
    (hni : ∀ p ∈ E.processes.toList, ∀ b, p ≠ .initial b) (hcomb : E.hasComb = false) (hrm : E.readmemh = []) :
    E.initialState = (do
      let declared ← E.execDeclInitializers E.initial E.declInitializers
      E.settleCanonical E.env E.elems declared E.processes.toList) := by
  unfold CoreMemDesign.initialState
  rw [List.filterMap_eq_nil_iff.mpr (fun p hp => ?_)]
  · simp [hrm, hcomb, CoreMemDesign.settleCanonical]
    cases hdecl : E.execDeclInitializers E.initial E.declInitializers with
    | timeout => simp [hdecl]
    | unsupported msg => simp [hdecl]
    | ok declared =>
        cases hsettle : E.settleAssignQuiesce 4096 E.env E.elems declared E.processes.toList with
        | timeout => simp [hdecl, hsettle]
        | unsupported msg => simp [hdecl, hsettle]
        | ok settled => simp [hdecl, hsettle]
  · cases p with
    | initial b => exact absurd rfl (hni _ hp b)
    | _ => rfl

#print axioms CoreMemDesign.initialState_of_quiet

/-- **The route's clock and reset source check admits every design**: the route iterates NBA-caused events in the slot
(§4.4, §4.5); the clocked obligations exclude an internally driven clock or reset. -/
theorem coreMemClockResetViol_none (d : PDesign) (g : List PProcess) : coreMemClockResetViol d g = none := rfl

#print axioms coreMemClockResetViol_none

end LeanModels.Sv.Kernel
