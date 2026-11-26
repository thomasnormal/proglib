import LeanModels.Sv.Kernel.NdStep
import LeanModels.Sv.NbaCommit
import LeanModels.Sv.SeqCycle

/-! # The executor is one run of the choice-explicit relation (T2)

The relation of `NdStep.lean` is the meaning.  The function-based executor is
a tool; this file proves that, on a named syntactic fragment and from a start
store that satisfies two explicit hypotheses, what the executor returns is a
settled run of the relation.

## The theorem

`CoreMemDesign.step_sound`: for a design in `CoreMemDesign.NbaClocked`, a
start store `st` that is typed and whose control signals are known
(`CoreMemDesign.ControlsKnown`), if the executor's slot function returns
`E.step st entry = .ok next` and the controls are known in `next`, then
`Nd.EventSettles E st entry Oracle.zero t` for a settled `t` with
`t.store = next` and `t.oracle = Oracle.zero`.

`runCoreMemRows_sound` is the same for a list of input rows: the executor's
list of stores is a `Nd.Trace`, the multi-row closure with the oracle threaded
from one row to the next.

## What is and is not claimed (owner questions, not decided here)

* **The executor's own choices only.**  The run that is constructed takes the
  first runnable cursor to completion, in source order, under the always-0
  oracle (`Oracle.zero`, the executor's `condTrue` at an unknown `if`
  condition).  This is soundness for that one schedule and that one oracle.
  Completeness (every outcome of the relation is an executor outcome) is false
  in general and is not claimed.
* **Controls known at the start.**  The step refuses an x/z on a clock or
  event expression, so the relation has no run from a power-on store whose
  clocks are x.  The theorem is therefore about a start store whose control
  signals are known: `ControlsKnown st`, a `Bool` test on the store's scalar
  view.  The executor does not make that test, so the hypothesis cannot be
  dropped.  `ControlsKnown next` is the same test on the executor's result; in
  this fragment it is equivalent to "the controls are known after the inputs
  of the row are applied" (`CoreMemDesign.step_input_controls`), because no
  process writes a control signal.
* Operand reads of an unknown are not oracle sites (only `if` conditions are);
  nothing here says otherwise.

## The fragment, exactly (`CoreMemDesign.NbaClocked`)

Four fields, each a `Bool` test or a structural equation on the design; none
is a statement about runs.

* `admitted`: `E.ndAdmitted` (every process is an edge or event process; no
  resolved net, no `$readmemh`, no declaration initializer).
* `bodies`: every process body is `PStmt.nbaPlain E.ndEventSources`: built
  from `begin ... end`, `if` (condition without `===`, `!==`, `==?`, `!=?`),
  counted `for`, nonblocking AND BLOCKING assignments to a WHOLE declared
  signal (`x <= e`, `x = e`, with `e` free of those observers) that is not a
  clock or event source of any process, and declarations of static locals
  (`logic t;` in a block: the local is a declared signal of the design).
  A blocking target need not be local to its process for THIS theorem: the
  run that is constructed is the executor's own schedule (first runnable
  cursor to completion), under which a later process reads what an earlier
  one wrote, in the relation as in the executor.  Process-locality matters
  for non-interference (`NdFootprint.lean`), not for soundness.  The step
  refuses a blocking write that changes a clock or event source; the
  fragment excludes such a target syntactically.
* `fourState`: every scalar declaration is four-state.
* `edgeBase`: `E.scalarEdge.base = E.scalar` (the NBA commit and the view use
  the same declaration table; `rfl` on a loaded design).

## The gap, exactly

* automatic procedural declarations (`automatic logic t;`: the cursor's
  locals), and blocking assignments to them (the relation has them; this
  theorem does not);
* blocking or nonblocking assignments to a bit select, part select,
  concatenation, array element or memory word (the relation checks their
  index values, the executor does not; the frame lemma for their queue
  entries is not proved);
* a nonblocking assignment to a clock or event source (a derived clock): the
  slot may then take a second round, and control knownness after the commit
  is no longer implied by the start hypotheses;
* two-state variables;
* `case`, continuous assignments, `always_comb`, `always_latch`, `always @*`,
  primitives, time zero: refused by the relation.

The executor's budgets (`execStmtFuel ... 4096`, `edgeQuiesce 4096`) appear
only in the hypothesis "the executor returned `.ok`".  No statement here has a
fuel or step bound of its own.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## The fragment -/

/-- The initializer of a procedural declaration has no x observer. -/
def ndInitPlain : Option PExpr → Bool
  | none => true
  | some e => (ndXObserver? e).isNone

mutual

/-- A clocked body of the fragment: blocks, `if`, counted `for`, nonblocking
and blocking assignments to a whole signal that is not in `srcs`, and
declarations of static locals; no x observer in a condition, a right-hand
side or an initializer. -/
def _root_.LeanModels.Sv.PStmt.nbaPlain (srcs : List String) : PStmt → Bool
  | .nbaAssign t v => decide (t ∉ srcs) && (ndXObserver? v).isNone
  | .nbaAssignL (.ident t) v => decide (t ∉ srcs) && (ndXObserver? v).isNone
  | .blockingAssign t v => decide (t ∉ srcs) && (ndXObserver? v).isNone
  | .blockingAssignL (.ident t) v => decide (t ∉ srcs) && (ndXObserver? v).isNone
  | .localDecl _ _ init => ndInitPlain init
  | .block body => PStmt.nbaPlainList srcs body
  | .ifStmt c yes no =>
      (ndXObserver? c).isNone && PStmt.nbaPlain srcs yes && PStmt.nbaPlainOpt srcs no
  | .forLoop _ _ _ _ body => PStmt.nbaPlain srcs body
  | _ => false

/-- `nbaPlain` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.nbaPlainOpt (srcs : List String) : Option PStmt → Bool
  | none => true
  | some s => PStmt.nbaPlain srcs s

/-- `nbaPlain` of every statement of a list. -/
def _root_.LeanModels.Sv.PStmt.nbaPlainList (srcs : List String) : List PStmt → Bool
  | [] => true
  | s :: ss => PStmt.nbaPlain srcs s && PStmt.nbaPlainList srcs ss

end

/-- The body of an edge or event process is `nbaPlain`; other processes carry
no obligation here (the admission predicate excludes them). -/
def CoreMemProc.nbaBody (srcs : List String) : CoreMemProc → Bool
  | .edge p => PStmt.nbaPlain srcs p.body
  | .event _ body => PStmt.nbaPlain srcs body
  | _ => true

/-- **The fragment of the soundness theorem.**  Every field is a `Bool` test
or a structural equation on the design. -/
structure CoreMemDesign.NbaClocked (E : CoreMemDesign) : Prop where
  admitted : E.ndAdmitted = true
  bodies : E.processes.toList.all (CoreMemProc.nbaBody E.ndEventSources) = true
  fourState : E.scalar.decls.toList.all (fun dc => !dc.twoState) = true
  edgeBase : E.scalarEdge.base = E.scalar

theorem CoreMemDesign.NbaClocked.allFour {E : CoreMemDesign} (hE : E.NbaClocked) :
    AllFour E.scalar := by
  intro dc hdc
  simpa using List.all_eq_true.mp hE.fourState dc hdc

/-- **The start hypothesis on control signals.**  Every clock and event
source of the design has a value with no x/z bit in the scalar view of `st`.
A `Bool` test. -/
def CoreMemDesign.ControlsKnown (E : CoreMemDesign) (st : CoreMemState) : Prop :=
  E.ndControlsKnownIn (E.scalar.view st.scalar) = true

instance (E : CoreMemDesign) (st : CoreMemState) : Decidable (E.ControlsKnown st) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## Views that agree on the event sources -/

/-- Two scalar views give every clock and event source the same value. -/
def CoreMemDesign.SourcesAgree (E : CoreMemDesign) (a b : SvState) : Prop :=
  ∀ n ∈ E.ndEventSources, SvState.lookup a n = SvState.lookup b n

theorem bit0_congr_lookup {a b : SvState} {n : String}
    (h : SvState.lookup a n = SvState.lookup b n) : SvState.bit0 a n = SvState.bit0 b n := by
  unfold SvState.bit0
  rw [h]

theorem coreMemEventsFire_agree {a b : SvState} : ∀ (events : List CoreMemEvent),
    (∀ e ∈ events, SvState.lookup a e.signal = SvState.lookup b e.signal) →
      coreMemEventsFire a b events = false
  | [], _ => rfl
  | e :: rest, h => by
      have he := h e (List.mem_cons_self ..)
      have hb := bit0_congr_lookup he
      have ih := coreMemEventsFire_agree rest (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
      obtain ⟨signal, edge⟩ := e
      cases edge <;>
        simp_all [coreMemEventsFire, coreMemEventFires, isPosedge_self, isNegedge_self]

/-- A process whose clock and event sources read the same in two views does
not fire between them. -/
theorem CoreMemProc.firesIn_agree {a b : SvState} (p : CoreMemProc)
    (h : ∀ n ∈ p.ndEventSources, SvState.lookup a n = SvState.lookup b n) :
    p.firesIn a b = false := by
  cases p with
  | edge q =>
      obtain ⟨clock, edge, reset, resetHigh, body, style⟩ := q
      have hc : SvState.bit0 a clock = SvState.bit0 b clock :=
        bit0_congr_lookup (h clock (by simp [CoreMemProc.ndEventSources]))
      cases reset with
      | none =>
          cases edge <;>
            simp [CoreMemProc.firesIn, CoreMemEdge.fires, hc, isPosedge_self, isNegedge_self]
      | some r =>
          have hr : SvState.bit0 a r = SvState.bit0 b r :=
            bit0_congr_lookup (h r (by simp [CoreMemProc.ndEventSources]))
          cases edge <;> cases resetHigh <;>
            simp [CoreMemProc.firesIn, CoreMemEdge.fires, hc, hr, isPosedge_self, isNegedge_self]
  | event events body =>
      exact coreMemEventsFire_agree events (fun e he => h e.signal (by
        simp only [CoreMemProc.ndEventSources, List.mem_map]
        exact ⟨e, he, rfl⟩))
  | _ => rfl

theorem CoreMemDesign.any_firesIn_agree {E : CoreMemDesign} {a b : SvState}
    (h : E.SourcesAgree a b) : E.processes.toList.any (CoreMemProc.firesIn a b) = false := by
  rw [List.any_eq_false]
  intro p hp
  rw [CoreMemProc.firesIn_agree p (fun n hn => h n (List.mem_flatMap.mpr ⟨p, hp, hn⟩))]
  simp

private theorem all_congr_mem {α : Type} {p q : α → Bool} : ∀ (l : List α),
    (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.all_cons, h x (List.mem_cons_self ..),
        all_congr_mem xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Control knownness depends only on the values of the event sources. -/
theorem CoreMemDesign.ndControlsKnownIn_agree {E : CoreMemDesign} {a b : SvState}
    (h : E.SourcesAgree a b) : E.ndControlsKnownIn a = E.ndControlsKnownIn b := by
  unfold CoreMemDesign.ndControlsKnownIn
  exact all_congr_mem _ (fun n hn => by rw [h n hn])

@[simp] theorem CoreMemDesign.ndEventSourceChanged_self (E : CoreMemDesign) (v : SvState) :
    E.ndEventSourceChanged v v = false := by
  simp [CoreMemDesign.ndEventSourceChanged]

/-! ## No event between a view and itself -/

theorem coreMemEventsFire_self (v : SvState) (events : List CoreMemEvent) :
    coreMemEventsFire v v events = false :=
  coreMemEventsFire_agree events (fun _ _ => rfl)

@[simp] theorem CoreMemProc.firesIn_self (v : SvState) (p : CoreMemProc) :
    p.firesIn v v = false :=
  CoreMemProc.firesIn_agree p (fun _ _ => rfl)

/-! ## Waking and the executor's follow-up test agree -/

theorem ndWakeList_isEmpty (E : CoreMemDesign) (a b : SvState) :
    ∀ procs : List CoreMemProc,
      (E.ndWakeList a b procs).isEmpty = !(procs.any (CoreMemProc.firesIn a b))
  | [] => rfl
  | p :: rest => by
      have ih := ndWakeList_isEmpty E a b rest
      simp only [CoreMemDesign.ndWakeList] at ih ⊢
      cases p with
      | edge q =>
          by_cases hf : q.fires a b = true <;>
            simp [CoreMemProc.ndWake, CoreMemProc.firesIn, hf, ih]
      | event events body =>
          by_cases hf : coreMemEventsFire a b events = true <;>
            simp [CoreMemProc.ndWake, CoreMemProc.firesIn, hf, ih]
      | _ => simp [List.filterMap_cons, CoreMemProc.ndWake, CoreMemProc.firesIn, ih]

/-- Views that agree on the event sources wake no process. -/
theorem CoreMemDesign.ndWake_agree {E : CoreMemDesign} {a b : SvState}
    (h : E.SourcesAgree a b) : E.ndWake a b = [] := by
  have h1 := ndWakeList_isEmpty E a b E.processes.toList
  rw [CoreMemDesign.any_firesIn_agree h] at h1
  exact List.isEmpty_iff.mp (by simpa [CoreMemDesign.ndWake] using h1)

/-! ## `begin` and `commit` in closed form -/

/-- The store after the input row is applied. -/
def CoreMemDesign.ndInput (E : CoreMemDesign) (st : CoreMemState) (entry : SvState) :
    CoreMemState :=
  E.normalizeScalar { st with memory := E.applyMemoryInputs entry st.memory }
    (E.scalar.applyInputs st.scalar entry)

/-- The state `begin` produces when it does not refuse. -/
def CoreMemDesign.ndStart (E : CoreMemDesign) (st : CoreMemState) (entry : SvState)
    (o : Oracle) : NdState :=
  { store := E.ndInput st entry
    active := E.ndWake (E.scalar.view st.scalar) (E.scalar.view (E.ndInput st entry).scalar)
    scalarQ := []
    memoryQ := []
    base := E.scalar.view (E.ndInput st entry).scalar
    oracle := o
    settled := false }

theorem NdState.begin_eq_ite {E : CoreMemDesign} (hA : E.ndAdmitted = true) (st : CoreMemState)
    (entry : SvState) (o : Oracle) :
    NdState.begin E st entry o =
      if !E.ndControlsKnownIn (E.scalar.view st.scalar) ||
          !E.ndControlsKnownIn (E.scalar.view (E.ndInput st entry).scalar) then
        .refused "9.4.2: x/z on a clock or event expression is outside the choice-explicit relation"
      else .next (E.ndStart st entry o) := by
  unfold NdState.begin
  simp only [hA, ↓reduceIte]
  rfl

/-- `begin` succeeds exactly from known controls, and then gives `ndStart`. -/
theorem NdState.begin_eq_next {E : CoreMemDesign} (hA : E.ndAdmitted = true) {st : CoreMemState}
    {entry : SvState} (o : Oracle) (hk : E.ControlsKnown st)
    (hk' : E.ControlsKnown (E.ndInput st entry)) :
    NdState.begin E st entry o = .next (E.ndStart st entry o) := by
  unfold CoreMemDesign.ControlsKnown at hk hk'
  rw [NdState.begin_eq_ite hA, hk, hk']
  rfl

theorem NdState.begin_next_inv {E : CoreMemDesign} {st : CoreMemState} {entry : SvState}
    {o : Oracle} {s₀ : NdState} (h : NdState.begin E st entry o = .next s₀) :
    E.ndAdmitted = true ∧ s₀ = E.ndStart st entry o ∧ E.ControlsKnown st ∧
      E.ControlsKnown (E.ndInput st entry) := by
  cases hA : E.ndAdmitted with
  | false => simp [NdState.begin, hA] at h
  | true =>
      rw [NdState.begin_eq_ite hA] at h
      unfold CoreMemDesign.ControlsKnown
      cases hk : E.ndControlsKnownIn (E.scalar.view st.scalar) <;>
        cases hk' : E.ndControlsKnownIn (E.scalar.view (E.ndInput st entry).scalar) <;>
        simp [hk, hk'] at h
      exact ⟨rfl, h.symm, rfl, rfl⟩

/-- The store after the NBA commit of the queue `sQ` with committed memory `m`. -/
def CoreMemDesign.ndCommitted (E : CoreMemDesign) (st : CoreMemState) (sQ : NbaQueue2)
    (m : MemState) : CoreMemState :=
  { E.normalizeScalar st (E.scalarEdge.commit st.scalar sQ) with memory := m }

/-- The state the commit move produces when it does not refuse. -/
def NdState.committed (E : CoreMemDesign) (s : NdState) (m : MemState) : NdState :=
  { store := E.ndCommitted s.store s.scalarQ m
    active := E.ndWake s.base (E.scalar.view (E.ndCommitted s.store s.scalarQ m).scalar)
    scalarQ := []
    memoryQ := []
    base := E.scalar.view (E.ndCommitted s.store s.scalarQ m).scalar
    oracle := s.oracle
    settled := (E.ndWake s.base (E.scalar.view (E.ndCommitted s.store s.scalarQ m).scalar)).isEmpty }

theorem NdState.commit_eq_ite {E : CoreMemDesign} {s : NdState} {m : MemState}
    (hm : s.store.memory.commitNba s.memoryQ = some m) :
    s.commit E =
      if !E.ndControlsKnownIn s.base ||
          !E.ndControlsKnownIn (E.scalar.view (E.ndCommitted s.store s.scalarQ m).scalar) then
        .refused "9.4.2: x/z on a clock or event expression is outside the choice-explicit relation"
      else .next (s.committed E m) := by
  unfold NdState.commit
  simp only [hm]
  rfl

/-- The commit move, as a step of the relation. -/
theorem Nd.Step.commit {E : CoreMemDesign} (hA : E.ndAdmitted = true) {s : NdState} {m : MemState}
    (hs : s.settled = false) (ha : s.active = [])
    (hm : s.store.memory.commitNba s.memoryQ = some m)
    (hkb : E.ndControlsKnownIn s.base = true)
    (hkv : E.ndControlsKnownIn (E.scalar.view (E.ndCommitted s.store s.scalarQ m).scalar) = true) :
    Nd.Step E s (s.committed E m) := by
  refine ⟨0, ?_⟩
  simp only [ndStep, hA, hs, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil]
  rw [NdState.commit_eq_ite hm, hkb, hkv]
  rfl

/-- The scalar view of a committed store is the view-level commit. -/
theorem CoreMemDesign.ndCommitted_view {E : CoreMemDesign} (hbase : E.scalarEdge.base = E.scalar)
    (h4 : AllFour E.scalar) {st : CoreMemState} (hT : E.scalar.Typed st.scalar) (q : NbaQueue2)
    (m : MemState) :
    E.scalar.view (E.ndCommitted st q m).scalar = commitNba2 (E.scalar.view st.scalar) q := by
  have h1 : E.scalar.view (E.ndCommitted st q m).scalar =
      E.scalar.view (E.scalarEdge.commit st.scalar q) :=
    E.normalizeScalar_view st (E.scalarEdge.commit st.scalar q)
  rw [h1]
  have h4' : AllFour E.scalarEdge.base := by rw [hbase]; exact h4
  have hT' : E.scalarEdge.base.Typed st.scalar := by rw [hbase]; exact hT
  have h2 := Elab1.view_commit (E := E.scalarEdge) h4' q hT'
  rw [hbase] at h2
  exact h2

/-- A committed store is typed. -/
theorem CoreMemDesign.ndCommitted_typed {E : CoreMemDesign} (hbase : E.scalarEdge.base = E.scalar)
    {st : CoreMemState} (hT : E.scalar.Typed st.scalar) (q : NbaQueue2) (m : MemState) :
    E.scalar.Typed (E.ndCommitted st q m).scalar := by
  have hT' : E.scalarEdge.base.Typed st.scalar := by rw [hbase]; exact hT
  have h := Elab1.typed_commit (E := E.scalarEdge) q hT'
  rw [hbase] at h
  exact (E.normalizeScalar_coherent st h).typed

/-- **Control signals are preserved by a commit that does not target them.**
If no update of the queue names a clock or event source, the committed view
gives every such source the value it had. -/
theorem CoreMemDesign.ndCommitted_agree {E : CoreMemDesign} (hbase : E.scalarEdge.base = E.scalar)
    (h4 : AllFour E.scalar) {st : CoreMemState} (hT : E.scalar.Typed st.scalar) {q : NbaQueue2}
    (hq : ∀ u ∈ q, u.1 ∉ E.ndEventSources) (m : MemState) :
    E.SourcesAgree (E.scalar.view st.scalar) (E.scalar.view (E.ndCommitted st q m).scalar) := by
  intro n hn
  rw [CoreMemDesign.ndCommitted_view hbase h4 hT]
  exact (lookup_commitNba2_of_not_mem _ q (fun u hu heq => hq u hu (by rw [heq]; exact hn))).symm

/-- A committed store is coherent. -/
theorem CoreMemDesign.ndCommitted_coherent {E : CoreMemDesign}
    (hbase : E.scalarEdge.base = E.scalar) {st : CoreMemState} (hT : E.scalar.Typed st.scalar)
    (q : NbaQueue2) (m : MemState) : E.Coherent (E.ndCommitted st q m) := by
  have hT' : E.scalarEdge.base.Typed st.scalar := by rw [hbase]; exact hT
  have h := Elab1.typed_commit (E := E.scalarEdge) q hT'
  rw [hbase] at h
  have hc := E.normalizeScalar_coherent st h
  exact ⟨hc.store, hc.size, hc.typed⟩

theorem CoreMemDesign.ndInput_typed {E : CoreMemDesign} {st : CoreMemState}
    (hT : E.scalar.Typed st.scalar) (entry : SvState) :
    E.scalar.Typed (E.ndInput st entry).scalar :=
  (E.normalizeScalar_coherent _ (hT.applyInputs entry)).typed

/-! ## One cursor inside a context -/

/-- A state of the always-0 run: the cursor list is `before ++ mid ++ after`. -/
def ndCtx (st : CoreMemState) (before mid after : List EdgeCursor)
    (sQ : NbaQueue2) (mQ : MemNbaQueue) (base : SvState) : NdState :=
  { store := st, active := before ++ mid ++ after, scalarQ := sQ, memoryQ := mQ, base,
    oracle := Oracle.zero, settled := false }

theorem CoreMemDesign.SourcesAgree.refl (E : CoreMemDesign) (a : SvState) : E.SourcesAgree a a :=
  fun _ _ => rfl

theorem CoreMemDesign.SourcesAgree.trans {E : CoreMemDesign} {a b c : SvState}
    (h₁ : E.SourcesAgree a b) (h₂ : E.SourcesAgree b c) : E.SourcesAgree a c :=
  fun n hn => (h₁ n hn).trans (h₂ n hn)

/-- Views that agree on the event sources: no event source changed. -/
theorem CoreMemDesign.ndEventSourceChanged_agree {E : CoreMemDesign} {a b : SvState}
    (h : E.SourcesAgree a b) : E.ndEventSourceChanged a b = false := by
  unfold CoreMemDesign.ndEventSourceChanged
  rw [List.any_eq_false]
  intro n hn
  simp [h n hn]

/-- One node of one cursor, as a step of the relation.  The node may change
the store (a blocking write) as long as every clock and event source keeps its
value: then the step function's refusal for a blocking write that moves an
event source does not apply. -/
theorem fire_ndCtx {E : CoreMemDesign} (hA : E.ndAdmitted = true) {st : CoreMemState}
    {before after : List EdgeCursor}
    {w : EdgeWork} {tail : List EdgeWork} {locals : SvState} {sQ : NbaQueue2} {mQ : MemNbaQueue}
    {base : SvState} {r : CoreMemExecResult} {exposed : List EdgeWork}
    (h : w.ndOpen E st locals Oracle.zero = .ok (r, exposed, Oracle.zero))
    (hag : E.SourcesAgree (E.scalar.view st.scalar) (E.scalar.view r.state.scalar)) :
    Nd.Step E (ndCtx st before [⟨w :: tail, locals⟩] after sQ mQ base)
      (ndCtx r.state before (EdgeCursor.keep ⟨exposed ++ tail, r.locals⟩) after
        (sQ ++ r.scalarQ) (mQ ++ r.memoryQ) base) := by
  refine ⟨before.length, ?_⟩
  have hp := pickAt_append before (⟨w :: tail, locals⟩ : EdgeCursor) after
  simp [ndStep, hA, ndCtx, NdState.fire, hp, h, CoreMemDesign.any_firesIn_agree hag,
    CoreMemDesign.ndEventSourceChanged_agree hag]

/-- The executor's result `r` for the work item `w`, started in the store
`st` with no automatic local, is reproduced by the cursor in every context:
the cursor runs from `st` to the store `r.state` the executor reached, which
is coherent and gives every clock and event source the value it had; the
locals are still empty; no issued update names a clock or event source; and
the issued updates are appended to the queues. -/
def NdRuns (E : CoreMemDesign) (st : CoreMemState) (w : EdgeWork)
    (r : CoreMemExecResult) : Prop :=
  E.Coherent r.state ∧
    E.SourcesAgree (E.scalar.view st.scalar) (E.scalar.view r.state.scalar) ∧
    r.locals = [] ∧ (∀ u ∈ r.scalarQ, u.1 ∉ E.ndEventSources) ∧
    ∀ (before after : List EdgeCursor) (tail : List EdgeWork) (sQ : NbaQueue2) (mQ : MemNbaQueue)
      (base : SvState),
      Nd.Run E (ndCtx st before [⟨w :: tail, []⟩] after sQ mQ base)
        (ndCtx r.state before (EdgeCursor.keep ⟨tail, []⟩) after
          (sQ ++ r.scalarQ) (mQ ++ r.memoryQ) base)

theorem NdRuns.leaf {E : CoreMemDesign} (hA : E.ndAdmitted = true) {st : CoreMemState}
    {w : EdgeWork} {r : CoreMemExecResult}
    (h : w.ndOpen E st [] Oracle.zero = .ok (r, [], Oracle.zero))
    (hcoh : E.Coherent r.state)
    (hag : E.SourcesAgree (E.scalar.view st.scalar) (E.scalar.view r.state.scalar))
    (hl : r.locals = [])
    (hq : ∀ u ∈ r.scalarQ, u.1 ∉ E.ndEventSources) : NdRuns E st w r := by
  refine ⟨hcoh, hag, hl, hq, fun before after tail sQ mQ base => Nd.Run.single ?_⟩
  simpa [hl] using fire_ndCtx hA (before := before) (after := after) (tail := tail) (sQ := sQ)
    (mQ := mQ) (base := base) h hag

theorem NdRuns.open0 {E : CoreMemDesign} (hA : E.ndAdmitted = true) {st : CoreMemState}
    (hc : E.Coherent st) {w : EdgeWork}
    (h : w.ndOpen E st [] Oracle.zero = .ok (.idle st [], [], Oracle.zero)) :
    NdRuns E st w (.idle st []) :=
  NdRuns.leaf hA h hc (CoreMemDesign.SourcesAgree.refl E _) rfl
    (fun u hu => by simp [CoreMemExecResult.idle] at hu)

theorem NdRuns.open1 {E : CoreMemDesign} (hA : E.ndAdmitted = true) {st : CoreMemState}
    {w w₁ : EdgeWork} {r : CoreMemExecResult}
    (h : w.ndOpen E st [] Oracle.zero = .ok (.idle st [], [w₁], Oracle.zero))
    (h₁ : NdRuns E st w₁ r) : NdRuns E st w r := by
  refine ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, fun before after tail sQ mQ base => ?_⟩
  have hstep : Nd.Step E (ndCtx st before [⟨w :: tail, []⟩] after sQ mQ base)
      (ndCtx st before [⟨w₁ :: tail, []⟩] after sQ mQ base) := by
    simpa [EdgeCursor.keep, CoreMemExecResult.idle] using
      fire_ndCtx hA (before := before) (after := after) (tail := tail) (sQ := sQ) (mQ := mQ)
        (base := base) h (CoreMemDesign.SourcesAgree.refl E _)
  exact Nd.Run.head hstep (h₁.2.2.2.2 before after tail sQ mQ base)

theorem NdRuns.open2 {E : CoreMemDesign} (hA : E.ndAdmitted = true) {st : CoreMemState}
    {w w₁ w₂ : EdgeWork} {a b : CoreMemExecResult}
    (h : w.ndOpen E st [] Oracle.zero = .ok (.idle st [], [w₁, w₂], Oracle.zero))
    (h₁ : NdRuns E st w₁ a) (h₂ : NdRuns E a.state w₂ b) :
    NdRuns E st w (CoreMemExec.append a b) := by
  have hq : (CoreMemExec.append a b).scalarQ = a.scalarQ ++ b.scalarQ := rfl
  have hm : (CoreMemExec.append a b).memoryQ = a.memoryQ ++ b.memoryQ := rfl
  refine ⟨h₂.1, h₁.2.1.trans h₂.2.1, h₂.2.2.1, ?_, fun before after tail sQ mQ base => ?_⟩
  · intro u hu
    rw [hq] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact h₁.2.2.2.1 u hu
    · exact h₂.2.2.2.1 u hu
  have hstep : Nd.Step E (ndCtx st before [⟨w :: tail, []⟩] after sQ mQ base)
      (ndCtx st before [⟨w₁ :: w₂ :: tail, []⟩] after sQ mQ base) := by
    simpa [EdgeCursor.keep, CoreMemExecResult.idle] using
      fire_ndCtx hA (before := before) (after := after) (tail := tail) (sQ := sQ) (mQ := mQ)
        (base := base) h (CoreMemDesign.SourcesAgree.refl E _)
  have hr₁ := h₁.2.2.2.2 before after (w₂ :: tail) sQ mQ base
  have hk : EdgeCursor.keep ⟨w₂ :: tail, []⟩ = [⟨w₂ :: tail, []⟩] := rfl
  rw [hk] at hr₁
  have hr₂ := h₂.2.2.2.2 before after tail (sQ ++ a.scalarQ) (mQ ++ a.memoryQ) base
  rw [hq, hm, ← List.append_assoc, ← List.append_assoc]
  exact Nd.Run.head hstep (hr₁.trans hr₂)

/-! ## Leaf statements: the executor does not recurse; an NBA changes neither
the store nor the locals; a blocking write changes one signal -/

theorem withLocals_fromQueue_ok {locals : SvState} {st : CoreMemState} {q : Res CoreMemQueue}
    {r : CoreMemExecResult}
    (h : CoreMemExec.withLocals locals (CoreMemExec.fromQueue st q) = .ok r) :
    r.state = st ∧ r.locals = locals := by
  cases q with
  | ok p =>
      obtain ⟨a, b⟩ := p
      simp only [CoreMemExec.withLocals, CoreMemExec.fromQueue, Res.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  | timeout => simp [CoreMemExec.withLocals, CoreMemExec.fromQueue] at h
  | unsupported m => simp [CoreMemExec.withLocals, CoreMemExec.fromQueue] at h

/-- The fuel literal `1` in `ndLeaf` is not a bound: on a nonblocking
assignment `execStmtFuel` does not recurse, so every positive fuel gives the
same result. -/
theorem execStmtFuel_nbaAssign_fuel (E : CoreMemDesign) (env : IEnv) (st : CoreMemState)
    (locals : SvState) (fuel : Nat) (t : String) (v : PExpr) :
    E.execStmtFuel env E.elems st locals (fuel + 1) (.nbaAssign t v) =
      E.execStmtFuel env E.elems st locals 1 (.nbaAssign t v) := by
  rw [CoreMemDesign.execStmtFuel, CoreMemDesign.execStmtFuel]

/-- The same for the target-node form of a whole-signal nonblocking
assignment. -/
theorem execStmtFuel_nbaAssignIdent_fuel (E : CoreMemDesign) (env : IEnv) (st : CoreMemState)
    (locals : SvState) (fuel : Nat) (t : String) (v : PExpr) :
    E.execStmtFuel env E.elems st locals (fuel + 1) (.nbaAssignL (.ident t) v) =
      E.execStmtFuel env E.elems st locals 1 (.nbaAssignL (.ident t) v) := by
  rw [CoreMemDesign.execStmtFuel, CoreMemDesign.execStmtFuel]

/-- The same for a whole-signal blocking assignment. -/
theorem execStmtFuel_blockingAssign_fuel (E : CoreMemDesign) (env : IEnv) (st : CoreMemState)
    (locals : SvState) (fuel : Nat) (t : String) (v : PExpr) :
    E.execStmtFuel env E.elems st locals (fuel + 1) (.blockingAssign t v) =
      E.execStmtFuel env E.elems st locals 1 (.blockingAssign t v) := by
  rw [CoreMemDesign.execStmtFuel, CoreMemDesign.execStmtFuel]

/-- The same for the target-node form of a whole-signal blocking assignment. -/
theorem execStmtFuel_blockingAssignIdent_fuel (E : CoreMemDesign) (env : IEnv)
    (st : CoreMemState) (locals : SvState) (fuel : Nat) (t : String) (v : PExpr) :
    E.execStmtFuel env E.elems st locals (fuel + 1) (.blockingAssignL (.ident t) v) =
      E.execStmtFuel env E.elems st locals 1 (.blockingAssignL (.ident t) v) := by
  rw [CoreMemDesign.execStmtFuel, CoreMemDesign.execStmtFuel]

/-- A procedural declaration of a static local changes nothing, at every
positive fuel. -/
theorem execStmtFuel_localDecl (E : CoreMemDesign) (env : IEnv) (st : CoreMemState)
    (locals : SvState) (fuel : Nat) (name : String) (width : Nat) (init : Option PExpr) :
    E.execStmtFuel env E.elems st locals (fuel + 1) (.localDecl name width init) =
      .ok (.idle st locals) := by
  rw [CoreMemDesign.execStmtFuel]
  rfl

/-- What a whole-signal nonblocking assignment does in the executor: the
store and the locals are unchanged and every queued update names the target. -/
theorem issueIdent_ok {E : CoreMemDesign} {env : IEnv} {st : CoreMemState} {locals : SvState}
    {t : String} {val : LVec} {r : CoreMemExecResult}
    (h : CoreMemExec.withLocals locals
      (CoreMemExec.fromQueue st (E.issueTarget env E.elems st (.ident t) val)) = .ok r) :
    r.state = st ∧ r.locals = locals ∧ ∀ u ∈ r.scalarQ, u.1 = t := by
  refine ⟨(withLocals_fromQueue_ok h).1, (withLocals_fromQueue_ok h).2, ?_⟩
  unfold CoreMemDesign.issueTarget at h
  cases hs : E.scalarTarget t with
  | none => simp [hs, CoreMemExec.withLocals, CoreMemExec.fromQueue] at h
  | some w =>
      simp only [hs, CoreMemExec.withLocals, CoreMemExec.fromQueue, Res.ok.injEq] at h
      subst h
      simp

theorem execStmtFuel_nbaAssign_ok {E : CoreMemDesign} {env : IEnv} {st : CoreMemState}
    {locals : SvState} {fuel : Nat} {t : String} {v : PExpr} {r : CoreMemExecResult}
    (h : E.execStmtFuel env E.elems st locals (fuel + 1) (.nbaAssign t v) = .ok r) :
    r.state = st ∧ r.locals = locals ∧ ∀ u ∈ r.scalarQ, u.1 = t := by
  rw [CoreMemDesign.execStmtFuel] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | exact issueIdent_ok h
    | (obtain ⟨_, _, h'⟩ := Res.bind_eq_ok.mp h; exact issueIdent_ok h')

theorem execStmtFuel_nbaAssignIdent_ok {E : CoreMemDesign} {env : IEnv} {st : CoreMemState}
    {locals : SvState} {fuel : Nat} {t : String} {v : PExpr} {r : CoreMemExecResult}
    (h : E.execStmtFuel env E.elems st locals (fuel + 1) (.nbaAssignL (.ident t) v) = .ok r) :
    r.state = st ∧ r.locals = locals ∧ ∀ u ∈ r.scalarQ, u.1 = t := by
  rw [CoreMemDesign.execStmtFuel] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | exact issueIdent_ok h
    | (obtain ⟨_, _, h'⟩ := Res.bind_eq_ok.mp h; exact issueIdent_ok h')

/-- **What a whole-signal blocking assignment does in the executor**, from a
coherent store and with no automatic local: the result store is coherent,
the locals are still empty, and every signal other than the target reads as
before. -/
theorem execBlockingIdentLocal_ok {E : CoreMemDesign} {env : IEnv} {st : CoreMemState}
    (hc : E.Coherent st) {t : String} {v : PExpr} {p : CoreMemState × SvState}
    (h : E.execBlockingIdentLocal env E.elems st [] t v = .ok p) :
    p.2 = [] ∧ E.Coherent p.1 ∧ ∀ n, n ≠ t →
      SvState.lookup (E.scalar.view p.1.scalar) n = SvState.lookup (E.scalar.view st.scalar) n := by
  simp only [CoreMemDesign.execBlockingIdentLocal, SvState.lookup] at h
  obtain ⟨st', hst', h⟩ := Res.bind_eq_ok.mp h
  simp only [Res.ok.injEq] at h
  subst h
  simp only [CoreMemDesign.execBlockingTarget] at hst'
  cases hw : E.scalarTarget t with
  | none => simp [hw] at hst'
  | some width =>
      simp only [hw] at hst'
      obtain ⟨val, -, hval⟩ := Res.bind_eq_ok.mp hst'
      simp only [Res.ok.injEq] at hval
      subst hval
      obtain ⟨x, hx⟩ := CoreMemDesign.scalarWidth?_some (E := E) (n := t) (by
        have hw' : E.scalarWidth? t = some width := hw
        simp [hw'])
      obtain ⟨hview, hcoh⟩ := CoreMemDesign.setScalarState_spec hc hx val
      refine ⟨rfl, hcoh, fun n hn => ?_⟩
      rw [hview]
      exact SvState.lookup_set_ne _ _ (Ne.symm hn)

theorem execStmtFuel_blockingAssign_ok {E : CoreMemDesign} {env : IEnv} {st : CoreMemState}
    (hc : E.Coherent st) {fuel : Nat} {t : String} {v : PExpr} {r : CoreMemExecResult}
    (h : E.execStmtFuel env E.elems st [] (fuel + 1) (.blockingAssign t v) = .ok r) :
    E.Coherent r.state ∧ r.locals = [] ∧ r.scalarQ = [] ∧ ∀ n, n ≠ t →
      SvState.lookup (E.scalar.view r.state.scalar) n =
        SvState.lookup (E.scalar.view st.scalar) n := by
  rw [CoreMemDesign.execStmtFuel] at h
  obtain ⟨⟨st', l'⟩, hp, h⟩ := Res.bind_eq_ok.mp h
  obtain ⟨hl, hcoh, hv⟩ := execBlockingIdentLocal_ok hc hp
  simp only [Res.ok.injEq] at h
  subst h
  exact ⟨hcoh, hl, rfl, hv⟩

theorem execStmtFuel_blockingAssignIdent_ok {E : CoreMemDesign} {env : IEnv} {st : CoreMemState}
    (hc : E.Coherent st) {fuel : Nat} {t : String} {v : PExpr} {r : CoreMemExecResult}
    (h : E.execStmtFuel env E.elems st [] (fuel + 1) (.blockingAssignL (.ident t) v) = .ok r) :
    E.Coherent r.state ∧ r.locals = [] ∧ r.scalarQ = [] ∧ ∀ n, n ≠ t →
      SvState.lookup (E.scalar.view r.state.scalar) n =
        SvState.lookup (E.scalar.view st.scalar) n := by
  rw [CoreMemDesign.execStmtFuel] at h
  obtain ⟨⟨st', l'⟩, hp, h⟩ := Res.bind_eq_ok.mp h
  obtain ⟨hl, hcoh, hv⟩ := execBlockingIdentLocal_ok hc hp
  simp only [Res.ok.injEq] at h
  subst h
  exact ⟨hcoh, hl, rfl, hv⟩

/-! ## A clocked body: the executor's result is a run of the cursor -/

theorem exec_runs {E : CoreMemDesign} (hA : E.ndAdmitted = true) : ∀ fuel : Nat,
    (∀ stmt env st r, E.Coherent st → PStmt.nbaPlain E.ndEventSources stmt = true →
      E.execStmtFuel env E.elems st [] fuel stmt = .ok r →
        NdRuns E st (.edgeStmt env stmt) r) ∧
    (∀ stmts env st r, E.Coherent st → PStmt.nbaPlainList E.ndEventSources stmts = true →
      E.execStmtsFuel env E.elems st [] fuel stmts = .ok r →
        NdRuns E st (.edgeBlock env stmts) r) ∧
    (∀ values body iterator env st r, E.Coherent st →
      PStmt.nbaPlain E.ndEventSources body = true →
      E.execLoopValuesFuel env E.elems st [] fuel values body iterator = .ok r →
        NdRuns E st (.edgeLoop env iterator body values) r)
  | 0 => by
      refine ⟨?_, ?_, ?_⟩
      · intro stmt env st r _ _ h
        simp [CoreMemDesign.execStmtFuel] at h
      · intro stmts env st r _ _ h
        simp [CoreMemDesign.execStmtsFuel] at h
      · intro values body iterator env st r _ _ h
        simp [CoreMemDesign.execLoopValuesFuel] at h
  | fuel + 1 => by
      obtain ⟨ihS, ihL, ihV⟩ := exec_runs hA fuel
      refine ⟨?_, ?_, ?_⟩
      · intro stmt env st r hc hn h
        cases stmt with
        | nbaAssign t v =>
            simp only [PStmt.nbaPlain, Bool.and_eq_true, decide_eq_true_eq,
              Option.isNone_iff_eq_none] at hn
            obtain ⟨hst, hl, hq⟩ := execStmtFuel_nbaAssign_ok h
            rw [execStmtFuel_nbaAssign_fuel] at h
            exact NdRuns.leaf hA
              (by simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, hn.2, ndLeaf, h])
              (by rw [hst]; exact hc)
              (by rw [hst]; exact CoreMemDesign.SourcesAgree.refl E _)
              hl (fun u hu => by rw [hq u hu]; exact hn.1)
        | nbaAssignL t v =>
            cases t with
            | ident name =>
                simp only [PStmt.nbaPlain, Bool.and_eq_true, decide_eq_true_eq,
                  Option.isNone_iff_eq_none] at hn
                obtain ⟨hst, hl, hq⟩ := execStmtFuel_nbaAssignIdent_ok h
                rw [execStmtFuel_nbaAssignIdent_fuel] at h
                exact NdRuns.leaf hA
                  (by simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr,
                    CoreMemDesign.ndCheckTarget, ndIndexExprs, CoreMemDesign.ndCheckIndexExprs,
                    hn.2, ndLeaf, h])
                  (by rw [hst]; exact hc)
                  (by rw [hst]; exact CoreMemDesign.SourcesAgree.refl E _)
                  hl (fun u hu => by rw [hq u hu]; exact hn.1)
            | _ => simp [PStmt.nbaPlain] at hn
        | blockingAssign t v =>
            simp only [PStmt.nbaPlain, Bool.and_eq_true, decide_eq_true_eq,
              Option.isNone_iff_eq_none] at hn
            obtain ⟨hcoh, hl, hq, hv⟩ := execStmtFuel_blockingAssign_ok hc h
            rw [execStmtFuel_blockingAssign_fuel] at h
            exact NdRuns.leaf hA
              (by simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, hn.2, ndLeaf, h])
              hcoh (fun n hns => (hv n (by rintro rfl; exact hn.1 hns)).symm)
              hl (fun u hu => by rw [hq] at hu; simp at hu)
        | blockingAssignL t v =>
            cases t with
            | ident name =>
                simp only [PStmt.nbaPlain, Bool.and_eq_true, decide_eq_true_eq,
                  Option.isNone_iff_eq_none] at hn
                obtain ⟨hcoh, hl, hq, hv⟩ := execStmtFuel_blockingAssignIdent_ok hc h
                rw [execStmtFuel_blockingAssignIdent_fuel] at h
                exact NdRuns.leaf hA
                  (by simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr,
                    CoreMemDesign.ndCheckTarget, ndIndexExprs, CoreMemDesign.ndCheckIndexExprs,
                    hn.2, ndLeaf, h])
                  hcoh (fun n hns => (hv n (by rintro rfl; exact hn.1 hns)).symm)
                  hl (fun u hu => by rw [hq] at hu; simp at hu)
            | _ => simp [PStmt.nbaPlain] at hn
        | localDecl name width init =>
            rw [execStmtFuel_localDecl] at h
            simp only [Res.ok.injEq] at h
            subst h
            refine NdRuns.open0 hA hc ?_
            cases init with
            | none =>
                simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckOptionalExpr, ndLeaf,
                  execStmtFuel_localDecl]
            | some e =>
                simp only [PStmt.nbaPlain, ndInitPlain, Option.isNone_iff_eq_none] at hn
                simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckOptionalExpr,
                  CoreMemDesign.ndCheckExpr, hn, ndLeaf, execStmtFuel_localDecl]
        | block body =>
            rw [CoreMemDesign.execStmtFuel] at h
            exact NdRuns.open1 hA (w₁ := .edgeBlock env body) rfl
              (ihL body env st r hc (by simpa [PStmt.nbaPlain] using hn) h)
        | ifStmt c y n =>
            simp only [PStmt.nbaPlain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
            obtain ⟨⟨hobs, hy⟩, hno⟩ := hn
            simp only [CoreMemDesign.execStmtFuel] at h
            obtain ⟨cv, hcv, h⟩ := Res.bind_eq_ok.mp h
            by_cases hct : cv.condTrue = true
            · simp only [hct, ↓reduceIte] at h
              refine NdRuns.open1 hA (w₁ := .edgeStmt env y) ?_ (ihS y env st r hc hy h)
              simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, hobs, hcv,
                Oracle.zero_read_condTrue, Oracle.zero_read_snd, hct]
            · simp only [hct, Bool.false_eq_true, ↓reduceIte] at h
              cases n with
              | none =>
                  cases h
                  exact NdRuns.open0 hA hc (by
                    simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, hobs, hcv,
                      Oracle.zero_read_condTrue, Oracle.zero_read_snd, hct,
                      CoreMemExecResult.idle])
              | some s =>
                  refine NdRuns.open1 hA (w₁ := .edgeStmt env s) ?_
                    (ihS s env st r hc (by simpa [PStmt.nbaPlainOpt] using hno) h)
                  simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, hobs, hcv,
                    Oracle.zero_read_condTrue, Oracle.zero_read_snd, hct]
        | forLoop name init cond step body =>
            rw [CoreMemDesign.execStmtFuel] at h
            cases hfv : forValues2Int32 env name init cond step with
            | timeout => simp [hfv] at h
            | unsupported e => simp [hfv] at h
            | ok values =>
                simp only [hfv] at h
                have hlegacy := forValues2_of_forValues2Int32_ok env name init cond step hfv
                refine NdRuns.open1 hA (w₁ := .edgeLoop env name body values) ?_
                  (ihV values body name env st r hc (by simpa [PStmt.nbaPlain] using hn) h)
                simp [EdgeWork.ndOpen, ndOpenStmt, hlegacy]
        | _ => simp [PStmt.nbaPlain] at hn
      · intro stmts env st r hc hn h
        cases stmts with
        | nil =>
            rw [CoreMemDesign.execStmtsFuel] at h
            cases h
            exact NdRuns.open0 hA hc rfl
        | cons s ss =>
            simp only [PStmt.nbaPlainList, Bool.and_eq_true] at hn
            rw [CoreMemDesign.execStmtsFuel] at h
            obtain ⟨a, ha, h⟩ := Res.bind_eq_ok.mp h
            obtain ⟨b, hb, h⟩ := Res.bind_eq_ok.mp h
            cases h
            have hra := ihS s env st a hc hn.1 ha
            rw [hra.2.2.1] at hb
            exact NdRuns.open2 hA (w₁ := .edgeStmt env s) (w₂ := .edgeBlock env ss) rfl hra
              (ihL ss env a.state b hra.1 hn.2 hb)
      · intro values body iterator env st r hc hn h
        cases values with
        | nil =>
            rw [CoreMemDesign.execLoopValuesFuel] at h
            cases h
            exact NdRuns.open0 hA hc rfl
        | cons i rest =>
            rw [CoreMemDesign.execLoopValuesFuel] at h
            obtain ⟨a, ha, h⟩ := Res.bind_eq_ok.mp h
            obtain ⟨b, hb, h⟩ := Res.bind_eq_ok.mp h
            cases h
            have hra := ihS body (env.bindVal iterator i) st a hc hn ha
            rw [hra.2.2.1] at hb
            exact NdRuns.open2 hA (w₁ := .edgeStmt (env.bindVal iterator i) body)
              (w₂ := .edgeLoop env iterator body rest) rfl hra
              (ihV rest body iterator env a.state b hra.1 hn hb)

/-! ## The Active region: `runEdges` -/

theorem ndCtx_mid_cons (st : CoreMemState) (c : EdgeCursor) (rest : List EdgeCursor)
    (sQ : NbaQueue2) (mQ : MemNbaQueue) (base : SvState) :
    ndCtx st [] (c :: rest) [] sQ mQ base = ndCtx st [] [c] rest sQ mQ base := by
  simp [ndCtx]

theorem ndCtx_mid_nil (st : CoreMemState) (rest : List EdgeCursor)
    (sQ : NbaQueue2) (mQ : MemNbaQueue) (base : SvState) :
    ndCtx st [] [] rest sQ mQ base = ndCtx st [] rest [] sQ mQ base := by
  simp [ndCtx]

/-- What the Active region of the executor did, as a fact about the relation:
the store it reached is coherent and gives every clock and event source the
value it had, no issued update names a clock or event source, and the woken
cursors run from the start store to that store and the empty list with
exactly the issued queues. -/
def NdEdgesRun (E : CoreMemDesign) (a b : SvState) (procs : List CoreMemProc)
    (st : CoreMemState) (r : CoreMemExecResult) : Prop :=
  E.Coherent r.state ∧
    E.SourcesAgree (E.scalar.view st.scalar) (E.scalar.view r.state.scalar) ∧
    (∀ u ∈ r.scalarQ, u.1 ∉ E.ndEventSources) ∧
    ∀ (sQ : NbaQueue2) (mQ : MemNbaQueue) (base : SvState),
      Nd.Run E (ndCtx st [] (E.ndWakeList a b procs) [] sQ mQ base)
        (ndCtx r.state [] [] [] (sQ ++ r.scalarQ) (mQ ++ r.memoryQ) base)

private theorem runEdges_fire {E : CoreMemDesign} (hA : E.ndAdmitted = true) {a b : SvState}
    {st : CoreMemState} (hc : E.Coherent st) {body : PStmt} {rest : List CoreMemProc}
    {r : CoreMemExecResult}
    (hbody : PStmt.nbaPlain E.ndEventSources body = true)
    (ih : ∀ (st : CoreMemState) (r : CoreMemExecResult), E.Coherent st →
      E.runEdges E.env E.elems st a b rest = .ok r → NdEdgesRun E a b rest st r)
    (h : (do
      let x ← E.execStmt E.env E.elems st body
      let y ← E.runEdges E.env E.elems x.state a b rest
      Res.ok (CoreMemExec.append x y)) = .ok r) :
    E.Coherent r.state ∧
      E.SourcesAgree (E.scalar.view st.scalar) (E.scalar.view r.state.scalar) ∧
      (∀ u ∈ r.scalarQ, u.1 ∉ E.ndEventSources) ∧
      ∀ (sQ : NbaQueue2) (mQ : MemNbaQueue) (base : SvState), Nd.Run E
        (ndCtx st [] (EdgeCursor.start E.env body :: E.ndWakeList a b rest) [] sQ mQ base)
        (ndCtx r.state [] [] [] (sQ ++ r.scalarQ) (mQ ++ r.memoryQ) base) := by
  obtain ⟨x, hx, h⟩ := Res.bind_eq_ok.mp h
  obtain ⟨y, hy, h⟩ := Res.bind_eq_ok.mp h
  cases h
  have hrx := (exec_runs hA
      (4096 + PStmt.need E.env body + PStmt.runtimeNeed E.env body)).1
    body E.env st x hc hbody (by
      simpa only [CoreMemDesign.execStmt] using hx)
  obtain ⟨hyc, hya, hyq, hyr⟩ := ih x.state y hrx.1 hy
  have hq : (CoreMemExec.append x y).scalarQ = x.scalarQ ++ y.scalarQ := rfl
  have hm : (CoreMemExec.append x y).memoryQ = x.memoryQ ++ y.memoryQ := rfl
  refine ⟨hyc, hrx.2.1.trans hya, ?_, fun sQ mQ base => ?_⟩
  · intro u hu
    rw [hq] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hrx.2.2.2.1 u hu
    · exact hyq u hu
  have h1 := hrx.2.2.2.2 [] (E.ndWakeList a b rest) [] sQ mQ base
  have hk : EdgeCursor.keep ⟨[], []⟩ = [] := rfl
  rw [hk, ndCtx_mid_nil] at h1
  rw [ndCtx_mid_cons]
  rw [hq, hm, ← List.append_assoc, ← List.append_assoc]
  exact h1.trans (hyr (sQ ++ x.scalarQ) (mQ ++ x.memoryQ) base)

/-- The executor's Active-region result is a run of the relation that empties
the runnable list, reaching the same store with the same issued queues. -/
theorem runEdges_runs {E : CoreMemDesign} (hA : E.ndAdmitted = true) (a b : SvState) :
    ∀ (procs : List CoreMemProc), (∀ p ∈ procs, p.nbaBody E.ndEventSources = true) →
      ∀ (st : CoreMemState) (r : CoreMemExecResult), E.Coherent st →
        E.runEdges E.env E.elems st a b procs = .ok r → NdEdgesRun E a b procs st r
  | [], _, st, r, hc, h => by
      rw [CoreMemDesign.runEdges] at h
      cases h
      refine ⟨hc, CoreMemDesign.SourcesAgree.refl E _, fun u hu => by simp at hu,
        fun sQ mQ base => ?_⟩
      show Nd.Run E (ndCtx st [] [] [] sQ mQ base) (ndCtx st [] [] [] (sQ ++ []) (mQ ++ []) base)
      rw [List.append_nil, List.append_nil]
      exact .refl _
  | p :: rest, hb, st, r, hc, h => by
      have ih := runEdges_runs hA a b rest (fun q hq => hb q (List.mem_cons_of_mem _ hq))
      have hp := hb p (List.mem_cons_self ..)
      cases p with
      | edge q =>
          rw [CoreMemDesign.runEdges] at h
          by_cases hf : q.fires a b = true
          · simp only [hf, ↓reduceIte] at h
            have hw : E.ndWakeList a b (.edge q :: rest) =
                EdgeCursor.start E.env q.body :: E.ndWakeList a b rest := by
              simp [CoreMemDesign.ndWakeList, CoreMemProc.ndWake, hf]
            unfold NdEdgesRun
            rw [hw]
            exact runEdges_fire hA hc hp ih h
          · simp only [hf, Bool.false_eq_true, ↓reduceIte] at h
            have hw : E.ndWakeList a b (.edge q :: rest) = E.ndWakeList a b rest := by
              simp [CoreMemDesign.ndWakeList, CoreMemProc.ndWake, hf]
            unfold NdEdgesRun
            rw [hw]
            exact ih st r hc h
      | event events body =>
          rw [CoreMemDesign.runEdges] at h
          by_cases hf : coreMemEventsFire a b events = true
          · simp only [hf, ↓reduceIte] at h
            have hw : E.ndWakeList a b (.event events body :: rest) =
                EdgeCursor.start E.env body :: E.ndWakeList a b rest := by
              simp [CoreMemDesign.ndWakeList, CoreMemProc.ndWake, hf]
            unfold NdEdgesRun
            rw [hw]
            exact runEdges_fire hA hc hp ih h
          · simp only [hf, Bool.false_eq_true, ↓reduceIte] at h
            have hw : E.ndWakeList a b (.event events body :: rest) = E.ndWakeList a b rest := by
              simp [CoreMemDesign.ndWakeList, CoreMemProc.ndWake, hf]
            unfold NdEdgesRun
            rw [hw]
            exact ih st r hc h
      | _ =>
          simp only [CoreMemDesign.runEdges] at h
          have hw : ∀ p', (CoreMemProc.ndWake E a b p' = none) →
              E.ndWakeList a b (p' :: rest) = E.ndWakeList a b rest := by
            intro p' hp'
            simp [CoreMemDesign.ndWakeList, hp']
          unfold NdEdgesRun
          rw [hw _ rfl]
          exact ih st r hc h

/-! ## The regions the fragment does not have are the identity in the executor -/

theorem settleAssignAt_clocked (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) :
    ∀ (procs : List CoreMemProc), (∀ p ∈ procs, p.ndClocked = true) →
      ∀ (st : CoreMemState) (view : SvState) (index : Nat),
        E.settleAssignAt env elems st view index procs = .ok (st, view)
  | [], _, st, view, index => by rw [CoreMemDesign.settleAssignAt]
  | p :: rest, hb, st, view, index => by
      have ih := settleAssignAt_clocked E env elems rest
        (fun q hq => hb q (List.mem_cons_of_mem _ hq))
      have hp := hb p (List.mem_cons_self ..)
      cases p <;> simp [CoreMemProc.ndClocked] at hp <;>
        (rw [CoreMemDesign.settleAssignAt]; exact ih st view (index + 1))

theorem CoreMemDesign.ndAdmitted_nets {E : CoreMemDesign} (h : E.ndAdmitted = true) :
    E.resolvedNets = [] := by
  simp only [CoreMemDesign.ndAdmitted, Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.1.1.1

theorem CoreMemDesign.ndAdmitted_procs {E : CoreMemDesign} (h : E.ndAdmitted = true) :
    ∀ p ∈ E.processes.toList, p.ndClocked = true := by
  simp only [CoreMemDesign.ndAdmitted, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

theorem CoreMemDesign.ndAdmitted_hasComb {E : CoreMemDesign} (h : E.ndAdmitted = true) :
    E.hasComb = false := by
  unfold CoreMemDesign.hasComb
  rw [List.any_eq_false]
  intro p hp
  have := CoreMemDesign.ndAdmitted_procs h p hp
  cases p <;> simp_all [CoreMemProc.ndClocked]

theorem CoreMemDesign.ndAdmitted_hasImplicit {E : CoreMemDesign} (h : E.ndAdmitted = true) :
    E.hasImplicit = false := by
  unfold CoreMemDesign.hasImplicit
  rw [List.any_eq_false]
  intro p hp
  have := CoreMemDesign.ndAdmitted_procs h p hp
  cases p <;> simp_all [CoreMemProc.ndClocked]

/-- On an admitted design the executor's continuous-assignment settle is the
identity. -/
theorem CoreMemDesign.settleCanonical_clocked {E : CoreMemDesign} (h : E.ndAdmitted = true)
    (st : CoreMemState) : E.settleCanonical E.env E.elems st E.processes.toList = .ok st := by
  have h0 : E.resetResolvedNets st = st := by
    simp [CoreMemDesign.resetResolvedNets, CoreMemDesign.ndAdmitted_nets h]
  have hs : E.settleAssign E.env E.elems st E.processes.toList = .ok st := by
    unfold CoreMemDesign.settleAssign
    simp [h0, settleAssignAt_clocked E E.env E.elems _ (CoreMemDesign.ndAdmitted_procs h),
      CoreMemDesign.compactScalar]
  unfold CoreMemDesign.settleCanonical
  rw [show (4096 : Nat) = 4095 + 1 from rfl, CoreMemDesign.settleAssignQuiesce]
  simp [hs]

/-- On an admitted design the executor's preparation of a row is: apply the
inputs.  It makes no test on the control signals. -/
theorem CoreMemDesign.prepareStep_clocked {E : CoreMemDesign} (h : E.ndAdmitted = true)
    (st : CoreMemState) (entry : SvState) :
    E.prepareStep st entry =
      .ok (E.ndInput st entry, E.scalar.view st.scalar,
        E.scalar.view (E.ndInput st entry).scalar) := by
  unfold CoreMemDesign.prepareStep CoreMemDesign.ndInput
  simp [CoreMemDesign.settleCanonical_clocked h, CoreMemDesign.ndAdmitted_hasComb h,
    CoreMemDesign.ndAdmitted_hasImplicit h]

theorem CoreMemDesign.edgePass_clocked {E : CoreMemDesign} (h : E.ndAdmitted = true)
    {st cb next : CoreMemState} {before after : SvState}
    (hp : E.edgePass st before after cb = .ok next) :
    ∃ edge m, E.runEdges E.env E.elems st before after E.processes.toList = .ok edge ∧
      edge.state.memory.commitNba edge.memoryQ = some m ∧
      next = E.ndCommitted edge.state edge.scalarQ m := by
  unfold CoreMemDesign.edgePass at hp
  cases he : E.runEdges E.env E.elems st before after E.processes.toList with
  | timeout => simp [he] at hp
  | unsupported msg => simp [he] at hp
  | ok edge =>
      cases hm : edge.state.memory.commitNba edge.memoryQ with
      | none => simp [he, hm] at hp
      | some m =>
          simp [he, hm, CoreMemDesign.settleCanonical_clocked h,
            CoreMemDesign.ndAdmitted_hasComb h, CoreMemDesign.ndAdmitted_hasImplicit h] at hp
          exact ⟨edge, m, rfl, hm, hp.symm⟩

/-- The converse on an admitted design: an Active-region result whose memory
queue commits gives the pass. -/
theorem CoreMemDesign.edgePass_clocked_ok {E : CoreMemDesign} (h : E.ndAdmitted = true)
    {st cb : CoreMemState} {before after : SvState} {edge : CoreMemExecResult} {m : MemState}
    (he : E.runEdges E.env E.elems st before after E.processes.toList = .ok edge)
    (hm : edge.state.memory.commitNba edge.memoryQ = some m) :
    E.edgePass st before after cb = .ok (E.ndCommitted edge.state edge.scalarQ m) := by
  unfold CoreMemDesign.edgePass
  simp [he, hm, CoreMemDesign.settleCanonical_clocked h, CoreMemDesign.ndAdmitted_hasComb h,
    CoreMemDesign.ndAdmitted_hasImplicit h, CoreMemDesign.ndCommitted]

/-! ## One slot of the executor, decomposed -/

/-- **What the executor's slot function computes on the fragment.**  From a
typed store, `E.step st entry = .ok next` means: the inputs were applied
(`ndInput`), the woken cursors ran to the empty list, reaching a coherent
store `es` in which every clock and event source has the value it had after
the inputs (`es` differs from the input store by the blocking writes), and
issuing a queue `q` that names no clock or event source; `next` is the commit
of that queue on `es`.  The slot has exactly one round. -/
theorem CoreMemDesign.step_decompose {E : CoreMemDesign} (hE : E.NbaClocked)
    {st next : CoreMemState} {entry : SvState} (hT : E.scalar.Typed st.scalar)
    (h : E.step st entry = .ok next) :
    ∃ (es : CoreMemState) (q : NbaQueue2) (mq : MemNbaQueue) (m : MemState),
      E.Coherent es ∧
      E.SourcesAgree (E.scalar.view (E.ndInput st entry).scalar) (E.scalar.view es.scalar) ∧
      (∀ u ∈ q, u.1 ∉ E.ndEventSources) ∧
      es.memory.commitNba mq = some m ∧
      next = E.ndCommitted es q m ∧
      Nd.Run E (E.ndStart st entry Oracle.zero)
        { store := es, active := [], scalarQ := q, memoryQ := mq,
          base := E.scalar.view (E.ndInput st entry).scalar, oracle := Oracle.zero,
          settled := false } := by
  have hA := hE.admitted
  have hic : E.Coherent (E.ndInput st entry) :=
    E.normalizeScalar_coherent _ (hT.applyInputs entry)
  unfold CoreMemDesign.step CoreMemDesign.stepFuel at h
  rw [CoreMemDesign.prepareStep_clocked hA] at h
  simp only [Res.ok_bind] at h
  rw [show (4096 : Nat) = 4095 + 1 from rfl, CoreMemDesign.edgeQuiesce] at h
  obtain ⟨nx, hpass, h⟩ := Res.bind_eq_ok.mp h
  obtain ⟨edge, m, he, hm, rfl⟩ := CoreMemDesign.edgePass_clocked hA hpass
  obtain ⟨hec, hea, hq, hrun⟩ := runEdges_runs hA (E.scalar.view st.scalar)
    (E.scalar.view (E.ndInput st entry).scalar) _ (List.all_eq_true.mp hE.bodies)
    (E.ndInput st entry) edge hic he
  have hagree := hea.trans
    (CoreMemDesign.ndCommitted_agree hE.edgeBase hE.allFour hec.typed hq m)
  simp only [CoreMemDesign.any_firesIn_agree hagree, Bool.false_eq_true, ↓reduceIte,
    Res.ok.injEq] at h
  refine ⟨edge.state, edge.scalarQ, edge.memoryQ, m, hec, hea, hq, hm, h.symm, ?_⟩
  have hrun' := hrun [] [] (E.scalar.view (E.ndInput st entry).scalar)
  simpa [ndCtx, CoreMemDesign.ndStart, CoreMemDesign.ndWake] using hrun'

/-- **When the executor's slot function returns, on the fragment.**  If the
Active region returns for the woken processes and its memory queue commits,
the slot function returns the commit of the issued queue.  (Used to show that
the hypothesis `E.step st entry = .ok next` of `step_sound` is met on a
design, without evaluating the executor.) -/
theorem CoreMemDesign.step_eq_of_runEdges {E : CoreMemDesign} (hE : E.NbaClocked)
    {st : CoreMemState} {entry : SvState} (hT : E.scalar.Typed st.scalar)
    {edge : CoreMemExecResult} {m : MemState}
    (he : E.runEdges E.env E.elems (E.ndInput st entry) (E.scalar.view st.scalar)
      (E.scalar.view (E.ndInput st entry).scalar) E.processes.toList = .ok edge)
    (hm : edge.state.memory.commitNba edge.memoryQ = some m) :
    E.step st entry = .ok (E.ndCommitted edge.state edge.scalarQ m) := by
  have hA := hE.admitted
  have hic : E.Coherent (E.ndInput st entry) :=
    E.normalizeScalar_coherent _ (hT.applyInputs entry)
  obtain ⟨hec, hea, hq, -⟩ := runEdges_runs hA (E.scalar.view st.scalar)
    (E.scalar.view (E.ndInput st entry).scalar) _ (List.all_eq_true.mp hE.bodies)
    (E.ndInput st entry) edge hic he
  unfold CoreMemDesign.step CoreMemDesign.stepFuel
  rw [CoreMemDesign.prepareStep_clocked hA]
  simp only [Res.ok_bind]
  apply CoreMemDesign.edgeQuiesce_eq_edgePass_of_no_followup
    (CoreMemDesign.edgePass_clocked_ok hA he hm)
  exact CoreMemDesign.any_firesIn_agree (hea.trans
    (CoreMemDesign.ndCommitted_agree hE.edgeBase hE.allFour hec.typed hq m))

/-! ## T2: the executor's slot result is a settled run of the relation -/

/-- On the fragment the executor's result has the control values of the store
after the inputs were applied: no process writes a control signal. -/
theorem CoreMemDesign.step_input_controls {E : CoreMemDesign} (hE : E.NbaClocked)
    {st next : CoreMemState} {entry : SvState} (hT : E.scalar.Typed st.scalar)
    (h : E.step st entry = .ok next) :
    E.ControlsKnown next ↔ E.ControlsKnown (E.ndInput st entry) := by
  obtain ⟨es, q, mq, m, hec, hea, hq, -, rfl, -⟩ := CoreMemDesign.step_decompose hE hT h
  unfold CoreMemDesign.ControlsKnown
  rw [CoreMemDesign.ndControlsKnownIn_agree (hea.trans
    (CoreMemDesign.ndCommitted_agree hE.edgeBase hE.allFour hec.typed hq m))]

/-- The executor's result on the fragment is typed. -/
theorem CoreMemDesign.step_typed {E : CoreMemDesign} (hE : E.NbaClocked)
    {st next : CoreMemState} {entry : SvState} (hT : E.scalar.Typed st.scalar)
    (h : E.step st entry = .ok next) : E.scalar.Typed next.scalar := by
  obtain ⟨es, q, mq, m, hec, -, -, -, rfl, -⟩ := CoreMemDesign.step_decompose hE hT h
  exact CoreMemDesign.ndCommitted_typed hE.edgeBase hec.typed q m

/-- **T2: soundness of the executor's slot function on the fragment.**

For a design of the named syntactic fragment `NbaClocked`, from a typed start
store whose control signals are known, if the executor's slot function returns
`next` for the input row `entry`, and the control signals are known in `next`,
then the relation, started from the same store and row under the executor's
choices (first runnable cursor to completion; the always-0 oracle), has a run
to a settled state whose store is exactly `next`, and the oracle is still the
always-0 oracle.

The fuel of the executor occurs only inside the hypothesis `h`. -/
theorem CoreMemDesign.step_sound {E : CoreMemDesign} (hE : E.NbaClocked)
    {st next : CoreMemState} {entry : SvState}
    (hT : E.scalar.Typed st.scalar) (hk : E.ControlsKnown st)
    (h : E.step st entry = .ok next) (hk' : E.ControlsKnown next) :
    ∃ t, Nd.EventSettles E st entry Oracle.zero t ∧ t.store = next ∧ t.oracle = Oracle.zero := by
  have hA := hE.admitted
  have hkin : E.ControlsKnown (E.ndInput st entry) :=
    (CoreMemDesign.step_input_controls hE hT h).mp hk'
  obtain ⟨es, q, mq, m, hec, hea, hq, hm, rfl, hrun⟩ := CoreMemDesign.step_decompose hE hT h
  have hagree := hea.trans
    (CoreMemDesign.ndCommitted_agree hE.edgeBase hE.allFour hec.typed hq m)
  have hstep := Nd.Step.commit hA
    (s := { store := es, active := [], scalarQ := q, memoryQ := mq,
            base := E.scalar.view (E.ndInput st entry).scalar, oracle := Oracle.zero,
            settled := false })
    rfl rfl hm hkin hk'
  refine ⟨_, ⟨_, NdState.begin_eq_next hA Oracle.zero hk hkin, Nd.Run.tail hrun hstep, ?_⟩,
    rfl, rfl⟩
  show (E.ndWake _ _).isEmpty = true
  rw [CoreMemDesign.ndWake_agree hagree]
  rfl

/-- **T2, row-list form.**  The executor's list of stores for a stimulus is a
trace of the relation with the oracle threaded from row to row (`Nd.Trace`),
under the executor's choices.  Hypotheses: the fragment; a typed start store
with known controls; the controls are known in every store the executor
returned; and no row takes the executor's repeat shortcut for an empty row. -/
theorem runCoreMemRows_sound {E : CoreMemDesign} (hE : E.NbaClocked) :
    ∀ (rows : List SvState) (st : CoreMemState) (out : List CoreMemState),
      E.scalar.Typed st.scalar → E.ControlsKnown st →
      (∀ row ∈ rows, (row.isEmpty && E.scalarAssignInputsOnly) = false) →
      runCoreMemRows E st rows = .ok out → (∀ st' ∈ out, E.ControlsKnown st') →
      Nd.Trace E st Oracle.zero rows out Oracle.zero
  | [], st, out, _, _, _, h, _ => by
      simp only [runCoreMemRows, Res.ok.injEq] at h
      subst h
      exact .nil st Oracle.zero
  | row :: rest, st, out, hT, hk, hne, h, hout => by
      have hrow := hne row (List.mem_cons_self ..)
      simp only [runCoreMemRows, hrow, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨st', hstep, h⟩ := Res.bind_eq_ok.mp h
      obtain ⟨tail, htail, h⟩ := Res.bind_eq_ok.mp h
      cases h
      have hk' : E.ControlsKnown st' := hout st' (List.mem_cons_self ..)
      have hT' := CoreMemDesign.step_typed hE hT hstep
      obtain ⟨t, hev, rfl, ho⟩ := CoreMemDesign.step_sound hE hT hk hstep hk'
      refine .cons hev ?_
      rw [ho]
      exact runCoreMemRows_sound hE rest t.store tail hT' hk'
        (fun r hr => hne r (List.mem_cons_of_mem _ hr)) htail
        (fun s hs => hout s (List.mem_cons_of_mem _ hs))

#print axioms exec_runs
#print axioms runEdges_runs
#print axioms CoreMemDesign.settleCanonical_clocked
#print axioms CoreMemDesign.step_decompose
#print axioms CoreMemDesign.step_eq_of_runEdges
#print axioms CoreMemDesign.step_input_controls
#print axioms CoreMemDesign.step_typed
#print axioms CoreMemDesign.step_sound
#print axioms runCoreMemRows_sound

end LeanModels.Sv.Kernel
