import LeanModels.Sv.Kernel.NdSound
import LeanModels.Sv.Kernel.EdgePhaseConfluence

/-! # L2: non-interfering cursors give one observable outcome (T3)

The relation of `NdStep.lean` offers every scheduling choice and every oracle.
This file proves that, when the cursors woken by one event do not interfere,
those choices do not show in what is observed: every settled outcome has the
same scalar view, and a settled outcome exists.

## The non-interference condition (`Nd.NonInterfering`)

It is a condition on the start state `s₀` of one event (the state `begin`
produces), on the design, and on one queue `T` of nonblocking updates:

* `solo`: every woken cursor, executed alone on the start store, (a) leaves
  the store as it is at every node, (b) gives the same node result under
  every oracle, i.e. reads no unknown at a decision, and (c) issues its part
  of `T` (`NdSolo`, `NdPending`).  Since no cursor changes the store before
  the commit, every read of every cursor sees the start store: no cursor
  reads what another one writes.
* `disjoint`: the updates of `T` are pairwise disjoint (`NbaDisj`: different
  signals, or disjoint bit windows of one signal).
* `offSources`: no update of `T` names a clock or event source.
* design side: `edgeBase`, `fourState`; store side: `typed`, `keys` (the
  view has no duplicate name), and `base` (the wake base is the view of the
  start store, which is what `begin` sets).

Every item is checked on a concrete design by evaluation of the step's own
node function (`solo`) or by a decision procedure (the rest); the swap example
does this for all 16 start values.  None of them mentions a run.

## What is derived

* `Nd.NonInterfering.quiet`: the commit of ANY permutation of `T` wakes no
  process and keeps the control signals as they were.  (Derived from
  `offSources`; it was an assumption in the earlier draft.)
* `Nd.settled_view`: EVERY settled state reachable from `s₀`, by any
  scheduling choices, any oracle and any number of steps, has the scalar view
  `commitNba2 (view of the start store) T`.
* `Nd.settled_view_unique`: two settled outcomes have the same scalar view.
* `Nd.exists_settled`: a settled outcome exists (given that the memory commit
  of the issued memory queue succeeds and the controls are known).
* `Nd.EventSettles.view_unique`: the same at the event level, across two
  oracles.

All of them go through the invariant lemma L1 (`Nd.Run.invariant`) with the
invariant `NdActiveInv ∨ NdDoneInv`; no schedule is enumerated and no length
is bounded.

## What is not claimed (owner questions, not decided here)

* Uniqueness is of the OBSERVABLE scalar view of the store, not of the whole
  machine state.  Whole-state uniqueness is false (the order of the issued
  queue differs between schedules).
* Memory contents: `Nd.settled_store` gives the committed memory as the
  commit of a permutation of the memory queue; equality of the committed
  memories for two permutations is not derived here.
* One NBA round per event: `offSources` excludes an update of a clock, so no
  second round can start.  Slots with a second round are outside this lemma.
* Blocking writes to shared signals are outside `NdSolo` (a node must leave
  the store unchanged).
* The condition is stated per start state.  A decidable predicate on the
  design that implies it for every start state is not in this file.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## The footprint of one cursor -/

/-- The cursor `c`, run alone on the store `st`, never changes the store,
gives the same result under every oracle (it reads no unknown at a decision),
and issues the scalar queue `q` and the memory queue `mq` before it runs out
of work. -/
inductive NdSolo (E : CoreMemDesign) (st : CoreMemState) :
    EdgeCursor → NbaQueue2 → MemNbaQueue → Prop where
  | done {c : EdgeCursor} (h : c.work = []) : NdSolo E st c [] []
  | step {c : EdgeCursor} {head : EdgeWork} {tail exposed : List EdgeWork}
      {r : CoreMemExecResult} {q : NbaQueue2} {mq : MemNbaQueue}
      (hw : c.work = head :: tail)
      (hopen : ∀ o : Oracle, head.ndOpen E st c.locals o = .ok (r, exposed, o))
      (hst : r.state = st)
      (hrest : NdSolo E st ⟨exposed ++ tail, r.locals⟩ q mq) :
      NdSolo E st c (r.scalarQ ++ q) (r.memoryQ ++ mq)

/-- Every cursor of the list is `NdSolo`; the queues are concatenated in list
order. -/
inductive NdPending (E : CoreMemDesign) (st : CoreMemState) :
    List EdgeCursor → NbaQueue2 → MemNbaQueue → Prop where
  | nil : NdPending E st [] [] []
  | cons {c : EdgeCursor} {cs : List EdgeCursor} {q q' : NbaQueue2} {mq mq' : MemNbaQueue}
      (hc : NdSolo E st c q mq) (hcs : NdPending E st cs q' mq') :
      NdPending E st (c :: cs) (q ++ q') (mq ++ mq')

theorem NdSolo.of_empty {E : CoreMemDesign} {st : CoreMemState} {c : EdgeCursor}
    {q : NbaQueue2} {mq : MemNbaQueue} (h : NdSolo E st c q mq) (hw : c.work = []) :
    q = [] ∧ mq = [] := by
  cases h with
  | done _ => exact ⟨rfl, rfl⟩
  | step hw' _ _ _ => rw [hw] at hw'; cases hw'

theorem NdPending.of_nil {E : CoreMemDesign} {st : CoreMemState} {q : NbaQueue2}
    {mq : MemNbaQueue} (h : NdPending E st [] q mq) : q = [] ∧ mq = [] := by
  cases h
  exact ⟨rfl, rfl⟩

theorem NdPending.append {E : CoreMemDesign} {st : CoreMemState} :
    ∀ {cs ds : List EdgeCursor} {q q' : NbaQueue2} {mq mq' : MemNbaQueue},
      NdPending E st cs q mq → NdPending E st ds q' mq' →
      NdPending E st (cs ++ ds) (q ++ q') (mq ++ mq')
  | [], _, _, _, _, _, h₁, h₂ => by
      obtain ⟨rfl, rfl⟩ := h₁.of_nil
      exact h₂
  | c :: cs, _, _, _, _, _, h₁, h₂ => by
      cases h₁ with
      | cons hc hcs =>
          rw [List.cons_append, List.append_assoc, List.append_assoc]
          exact .cons hc (NdPending.append hcs h₂)

theorem NdPending.split {E : CoreMemDesign} {st : CoreMemState} :
    ∀ {cs ds : List EdgeCursor} {q : NbaQueue2} {mq : MemNbaQueue},
      NdPending E st (cs ++ ds) q mq →
      ∃ q₁ q₂ mq₁ mq₂, NdPending E st cs q₁ mq₁ ∧ NdPending E st ds q₂ mq₂ ∧
        q = q₁ ++ q₂ ∧ mq = mq₁ ++ mq₂
  | [], _, q, mq, h => ⟨[], q, [], mq, .nil, h, rfl, rfl⟩
  | c :: cs, _, _, _, h => by
      cases h with
      | cons hc hcs =>
          obtain ⟨q₁, q₂, mq₁, mq₂, h₁, h₂, rfl, rfl⟩ := NdPending.split hcs
          exact ⟨_, q₂, _, mq₂, .cons hc h₁, h₂, by simp, by simp⟩

/-- `NdPending` for the cursor that `fire` puts back. -/
theorem NdPending.keep {E : CoreMemDesign} {st : CoreMemState} {c : EdgeCursor}
    {q : NbaQueue2} {mq : MemNbaQueue} (h : NdSolo E st c q mq) :
    NdPending E st (EdgeCursor.keep c) q mq := by
  unfold EdgeCursor.keep
  cases hw : c.work.isEmpty with
  | true =>
      obtain ⟨rfl, rfl⟩ := h.of_empty (List.isEmpty_iff.mp hw)
      exact .nil
  | false =>
      have := NdPending.cons h (NdPending.nil (E := E) (st := st))
      simpa using this

private theorem perm_move {α : Type} (a r b s c : List α) :
    (a ++ r ++ (b ++ s ++ c)).Perm (a ++ (b ++ (r ++ s) ++ c)) := by
  have h1 : (r ++ b).Perm (b ++ r) := List.perm_append_comm
  have h2 := (h1.append_right (s ++ c)).append_left a
  simpa [List.append_assoc] using h2

/-! ## The invariant, and its step (L1's obligation) -/

/-- The invariant of the Active region: the store is `st`; the runnable
cursors are all `NdSolo`; what has been issued, together with what the
runnable cursors will still issue, is a permutation of `T` (`TM`). -/
structure NdActiveInv (E : CoreMemDesign) (st : CoreMemState) (base : SvState)
    (T : NbaQueue2) (TM : MemNbaQueue) (s : NdState) : Prop where
  settled : s.settled = false
  store : s.store = st
  base : s.base = base
  pending : ∃ P PM, NdPending E st s.active P PM ∧ (s.scalarQ ++ P).Perm T ∧
    (s.memoryQ ++ PM).Perm TM

/-- The invariant after the commit: settled, and the store is the commit of a
permutation of `T` and `TM`. -/
structure NdDoneInv (E : CoreMemDesign) (st : CoreMemState)
    (T : NbaQueue2) (TM : MemNbaQueue) (s : NdState) : Prop where
  settled : s.settled = true
  store : ∃ q mq m, q.Perm T ∧ mq.Perm TM ∧ st.memory.commitNba mq = some m ∧
    s.store = E.ndCommitted st q m

/-- One step preserves "Active invariant or Done invariant".  This is the
step obligation of L1 for the footprint invariant.  `hquiet` says that the
commit of any permutation of the queue wakes nobody; `Nd.NonInterfering.quiet`
derives it from the footprint condition. -/
theorem NdActiveInv.step {E : CoreMemDesign} {st : CoreMemState} {base : SvState}
    {T : NbaQueue2} {TM : MemNbaQueue}
    (hquiet : ∀ q mq m, q.Perm T → mq.Perm TM → st.memory.commitNba mq = some m →
      E.ndWake base (E.scalar.view (E.ndCommitted st q m).scalar) = [])
    {s t : NdState} (hI : NdActiveInv E st base T TM s ∨ NdDoneInv E st T TM s)
    (hstep : Nd.Step E s t) : NdActiveInv E st base T TM t ∨ NdDoneInv E st T TM t := by
  rcases hI with hI | hI
  · obtain ⟨hset, hstore, hbase, P, PM, hpend, hperm, hpermM⟩ := hI
    obtain ⟨i, hi⟩ := hstep
    cases hA : E.ndAdmitted with
    | false => simp [ndStep, hA] at hi
    | true =>
    simp only [ndStep, hA, hset, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hi
    cases hact : s.active.isEmpty with
    | true =>
        -- the NBA commit
        have hnil : s.active = [] := List.isEmpty_iff.mp hact
        rw [hnil] at hpend
        obtain ⟨rfl, rfl⟩ := hpend.of_nil
        rw [List.append_nil] at hperm hpermM
        simp only [hact, ↓reduceIte] at hi
        cases hm : s.store.memory.commitNba s.memoryQ with
        | none => simp [NdState.commit, hm] at hi
        | some m =>
            rw [NdState.commit_eq_ite hm] at hi
            split at hi
            · cases hi
            · simp only [NdOutcome.next.injEq] at hi
              subst hi
              rw [hstore] at hm
              have hq := hquiet s.scalarQ s.memoryQ m hperm hpermM hm
              right
              refine ⟨?_, s.scalarQ, s.memoryQ, m, hperm, hpermM, hm, ?_⟩
              · show (E.ndWake s.base (E.scalar.view
                  (E.ndCommitted s.store s.scalarQ m).scalar)).isEmpty = true
                rw [hstore, hbase, hq]
                rfl
              · show E.ndCommitted s.store s.scalarQ m = E.ndCommitted st s.scalarQ m
                rw [hstore]
    | false =>
        -- one node of one cursor
        simp only [hact, Bool.false_eq_true, ↓reduceIte, NdState.fire] at hi
        cases hp : pickAt i s.active with
        | none => simp [hp] at hi
        | some pr =>
            obtain ⟨before, c, after⟩ := pr
            have hsplit := pickAt_eq hp
            rw [hsplit] at hpend
            obtain ⟨Pb, Pca, PMb, PMca, hpb, hpca, rfl, rfl⟩ := NdPending.split hpend
            cases hpca with
            | cons hc hpa =>
                rename_i Pc Pa PMc PMa
                simp only [hp] at hi
                cases hw : c.work with
                | nil =>
                    obtain ⟨rfl, rfl⟩ := hc.of_empty hw
                    simp only [hw, NdOutcome.next.injEq] at hi
                    subst hi
                    left
                    exact ⟨hset, hstore, hbase, _, _, NdPending.append hpb hpa,
                      by simpa using hperm, by simpa using hpermM⟩
                | cons head tail =>
                    cases hc with
                    | done h0 => rw [hw] at h0; cases h0
                    | step hw' hopen hst hrest =>
                        rename_i head' tail' exposed r q' mq'
                        rw [hw] at hw'
                        cases hw'
                        simp only [hw, hstore, hopen s.oracle, hst, CoreMemProc.firesIn_self,
                          CoreMemDesign.ndEventSourceChanged_self, Bool.and_false, Bool.or_false,
                          List.any_eq_true, Bool.false_eq_true, and_false, exists_false, ↓reduceIte,
                          NdOutcome.next.injEq] at hi
                        subst hi
                        left
                        refine ⟨rfl, rfl, hbase, Pb ++ (q' ++ Pa), PMb ++ (mq' ++ PMa),
                          ?_, ?_, ?_⟩
                        · have hk := NdPending.keep hrest
                          have := NdPending.append hpb (NdPending.append hk hpa)
                          simpa [List.append_assoc] using this
                        · have := perm_move s.scalarQ r.scalarQ Pb q' Pa
                          exact (by simpa [List.append_assoc] using this :
                            (s.scalarQ ++ r.scalarQ ++ (Pb ++ (q' ++ Pa))).Perm
                              (s.scalarQ ++ (Pb ++ (r.scalarQ ++ q' ++ Pa)))).trans hperm
                        · have := perm_move s.memoryQ r.memoryQ PMb mq' PMa
                          exact (by simpa [List.append_assoc] using this :
                            (s.memoryQ ++ r.memoryQ ++ (PMb ++ (mq' ++ PMa))).Perm
                              (s.memoryQ ++ (PMb ++ (r.memoryQ ++ mq' ++ PMa)))).trans hpermM
  · exact absurd hI.settled (by rw [hstep.not_settled]; simp)

/-- The view-level commit does not depend on the order of pairwise disjoint
updates.  This is the existing `EdgePhaseState.observable_eq_of_perm`, stated
on a store. -/
theorem CoreMemDesign.commitNba2_view_perm {E : CoreMemDesign} {st : CoreMemState}
    {T q : NbaQueue2} (hkeys : ((E.scalar.view st.scalar).map Prod.fst).Nodup)
    (hdisj : T.Pairwise NbaDisj) (hperm : q.Perm T) :
    commitNba2 (E.scalar.view st.scalar) q = commitNba2 (E.scalar.view st.scalar) T :=
  (EdgePhaseState.observable_eq_of_perm (E := E)
    (s₁ := { state := st, scalarQ := T }) (s₂ := { state := st, scalarQ := q })
    rfl hkeys hdisj hperm.symm).symm

/-! ## The non-interference condition -/

/-- **The non-interference condition** for the cursors woken by one event.
`s₀` is the start state of the event, `T` (`TM`) the scalar (memory) updates
the cursors issue.  See the file header for the reading of each field. -/
structure Nd.NonInterfering (E : CoreMemDesign) (s₀ : NdState) (T : NbaQueue2)
    (TM : MemNbaQueue) : Prop where
  /-- The state is the start of an event: not settled, nothing issued yet. -/
  unsettled : s₀.settled = false
  scalarQ : s₀.scalarQ = []
  memoryQ : s₀.memoryQ = []
  /-- The wake base is the view of the start store. -/
  base : s₀.base = E.scalar.view s₀.store.scalar
  /-- Each woken cursor alone: store untouched at every node, the same result
      under every oracle, and together they issue `T` and `TM`. -/
  solo : NdPending E s₀.store s₀.active T TM
  /-- The issued updates are pairwise disjoint. -/
  disjoint : T.Pairwise NbaDisj
  /-- No issued update names a clock or event source. -/
  offSources : ∀ u ∈ T, u.1 ∉ E.ndEventSources
  edgeBase : E.scalarEdge.base = E.scalar
  fourState : AllFour E.scalar
  typed : E.scalar.Typed s₀.store.scalar
  keys : ((E.scalar.view s₀.store.scalar).map Prod.fst).Nodup

/-- **Derived, not assumed: the commit starts no second round.**  Under the
footprint condition the commit of any permutation of the issued queue gives
every clock and event source the value it had, so no process is woken. -/
theorem Nd.NonInterfering.agree {E : CoreMemDesign} {s₀ : NdState} {T : NbaQueue2}
    {TM : MemNbaQueue} (h : Nd.NonInterfering E s₀ T TM) {q : NbaQueue2} (hq : q.Perm T)
    (m : MemState) :
    E.SourcesAgree s₀.base (E.scalar.view (E.ndCommitted s₀.store q m).scalar) := by
  rw [h.base]
  exact CoreMemDesign.ndCommitted_agree h.edgeBase h.fourState h.typed
    (fun u hu => h.offSources u (hq.mem_iff.mp hu)) m

theorem Nd.NonInterfering.quiet {E : CoreMemDesign} {s₀ : NdState} {T : NbaQueue2}
    {TM : MemNbaQueue} (h : Nd.NonInterfering E s₀ T TM) :
    ∀ q mq m, q.Perm T → mq.Perm TM → s₀.store.memory.commitNba mq = some m →
      E.ndWake s₀.base (E.scalar.view (E.ndCommitted s₀.store q m).scalar) = [] :=
  fun _ _ m hq _ _ => CoreMemDesign.ndWake_agree (h.agree hq m)

/-! ## L2 -/

/-- **L2, store form.**  From a non-interfering start state, every settled
state reachable by any choices and any oracle has the store obtained by
committing a permutation of the one queue `T` and a permutation of `TM`. -/
theorem Nd.settled_store {E : CoreMemDesign} {s₀ : NdState} {T : NbaQueue2}
    {TM : MemNbaQueue} (h : Nd.NonInterfering E s₀ T TM)
    {t : NdState} (hr : Nd.Run E s₀ t) (ht : t.settled = true) :
    ∃ q mq m, q.Perm T ∧ mq.Perm TM ∧ s₀.store.memory.commitNba mq = some m ∧
      t.store = E.ndCommitted s₀.store q m := by
  have hinit : NdActiveInv E s₀.store s₀.base T TM s₀ ∨ NdDoneInv E s₀.store T TM s₀ :=
    Or.inl ⟨h.unsettled, rfl, rfl, T, TM, h.solo, by simp [h.scalarQ], by simp [h.memoryQ]⟩
  have hfin := Nd.Run.invariant (fun s t hI hs => NdActiveInv.step h.quiet hI hs) hinit hr
  rcases hfin with hA | hD
  · rw [hA.settled] at ht
    cases ht
  · exact hD.store

/-- **L2, view form: the event-to-settled relation is a function on scalar
views.**  From a non-interfering start state, the scalar view of every
reachable settled state is `commitNba2 (view of the start store) T`. -/
theorem Nd.settled_view {E : CoreMemDesign} {s₀ : NdState} {T : NbaQueue2} {TM : MemNbaQueue}
    (h : Nd.NonInterfering E s₀ T TM)
    {t : NdState} (hr : Nd.Run E s₀ t) (ht : t.settled = true) :
    E.scalar.view t.store.scalar = commitNba2 (E.scalar.view s₀.store.scalar) T := by
  obtain ⟨q, mq, m, hperm, -, -, hstore⟩ := Nd.settled_store h hr ht
  rw [hstore, CoreMemDesign.ndCommitted_view h.edgeBase h.fourState h.typed]
  exact CoreMemDesign.commitNba2_view_perm h.keys h.disjoint hperm

/-- **L2, uniqueness of the observable view.**  Two settled outcomes of one
non-interfering start state have the same scalar view. -/
theorem Nd.settled_view_unique {E : CoreMemDesign} {s₀ : NdState} {T : NbaQueue2}
    {TM : MemNbaQueue} (h : Nd.NonInterfering E s₀ T TM)
    {t₁ t₂ : NdState} (hr₁ : Nd.Run E s₀ t₁) (ht₁ : t₁.settled = true)
    (hr₂ : Nd.Run E s₀ t₂) (ht₂ : t₂.settled = true) :
    E.scalar.view t₁.store.scalar = E.scalar.view t₂.store.scalar := by
  rw [Nd.settled_view h hr₁ ht₁, Nd.settled_view h hr₂ ht₂]

/-! ## Existence: a non-interfering start state has a settled outcome -/

/-- A `NdSolo` cursor can be run to completion wherever it stands in the
runnable list, under any oracle. -/
theorem NdSolo.run {E : CoreMemDesign} (hA : E.ndAdmitted = true) {st : CoreMemState}
    {c : EdgeCursor} {q : NbaQueue2} {mq : MemNbaQueue} (h : NdSolo E st c q mq) :
    ∀ (before after : List EdgeCursor) (sQ : NbaQueue2) (mQ : MemNbaQueue) (base : SvState)
      (o : Oracle),
      Nd.Run E
        { store := st, active := before ++ c :: after, scalarQ := sQ, memoryQ := mQ, base,
          oracle := o, settled := false }
        { store := st, active := before ++ after, scalarQ := sQ ++ q, memoryQ := mQ ++ mq, base,
          oracle := o, settled := false } := by
  induction h with
  | @done c hw =>
      intro before after sQ mQ base o
      refine Nd.Run.single ⟨before.length, ?_⟩
      simp [ndStep, hA, NdState.fire, pickAt_append, hw]
  | @step c head tail exposed r q mq hw hopen hst hrest ih =>
      intro before after sQ mQ base o
      have hfire : Nd.Step E
          { store := st, active := before ++ c :: after, scalarQ := sQ, memoryQ := mQ, base,
            oracle := o, settled := false }
          { store := st,
            active := before ++ EdgeCursor.keep ⟨exposed ++ tail, r.locals⟩ ++ after,
            scalarQ := sQ ++ r.scalarQ, memoryQ := mQ ++ r.memoryQ, base, oracle := o,
            settled := false } := by
        refine ⟨before.length, ?_⟩
        simp [ndStep, hA, NdState.fire, pickAt_append, hw, hopen o, hst]
      refine Nd.Run.head hfire ?_
      cases hk : (exposed ++ tail).isEmpty with
      | true =>
          obtain ⟨rfl, rfl⟩ := hrest.of_empty (List.isEmpty_iff.mp hk)
          have hkeep : EdgeCursor.keep ⟨exposed ++ tail, r.locals⟩ = [] := by
            simp [EdgeCursor.keep, hk]
          rw [hkeep]
          simp only [List.append_nil]
          exact .refl _
      | false =>
          have hkeep : EdgeCursor.keep ⟨exposed ++ tail, r.locals⟩ =
              [⟨exposed ++ tail, r.locals⟩] := by
            simp [EdgeCursor.keep, hk]
          rw [hkeep]
          have := ih before after (sQ ++ r.scalarQ) (mQ ++ r.memoryQ) base o
          simpa [List.append_assoc] using this

/-- A `NdPending` list can be run until no cursor is runnable. -/
theorem NdPending.run {E : CoreMemDesign} (hA : E.ndAdmitted = true) {st : CoreMemState}
    {cs : List EdgeCursor} {q : NbaQueue2} {mq : MemNbaQueue} (h : NdPending E st cs q mq) :
    ∀ (sQ : NbaQueue2) (mQ : MemNbaQueue) (base : SvState) (o : Oracle),
      Nd.Run E
        { store := st, active := cs, scalarQ := sQ, memoryQ := mQ, base, oracle := o,
          settled := false }
        { store := st, active := [], scalarQ := sQ ++ q, memoryQ := mQ ++ mq, base, oracle := o,
          settled := false } := by
  induction h with
  | nil =>
      intro sQ mQ base o
      simp only [List.append_nil]
      exact .refl _
  | @cons c cs q q' mq mq' hc hcs ih =>
      intro sQ mQ base o
      have h1 := hc.run hA [] cs sQ mQ base o
      have h2 := ih (sQ ++ q) (mQ ++ mq) base o
      simp only [List.nil_append] at h1
      simpa [List.append_assoc] using h1.trans h2

/-- **L2, existence.**  A non-interfering start state of an admitted design,
with known controls, whose issued memory queue commits, has a settled
outcome, whatever the oracle.  Together with `Nd.settled_view` this makes the
event-to-settled relation total and single-valued on scalar views. -/
theorem Nd.exists_settled {E : CoreMemDesign} (hA : E.ndAdmitted = true) {s₀ : NdState}
    {T : NbaQueue2} {TM : MemNbaQueue} (h : Nd.NonInterfering E s₀ T TM)
    (hk : E.ndControlsKnownIn s₀.base = true)
    {m : MemState} (hm : s₀.store.memory.commitNba TM = some m) :
    ∃ t, Nd.Run E s₀ t ∧ t.settled = true ∧ t.store = E.ndCommitted s₀.store T m := by
  have hagree := h.agree (List.Perm.refl T) m
  have hw := h.quiet T TM m (List.Perm.refl _) (List.Perm.refl _) hm
  have hsolo := h.solo
  obtain ⟨st, active, sQ, mQ, base, o, settled⟩ := s₀
  have h1 := h.unsettled
  have h2 := h.scalarQ
  have h3 := h.memoryQ
  simp only at h1 h2 h3 hk hm hagree hw hsolo
  subst h1 h2 h3
  have hrun := hsolo.run hA [] [] base o
  simp only [List.nil_append] at hrun
  have hkv : E.ndControlsKnownIn (E.scalar.view (E.ndCommitted st T m).scalar) = true := by
    rw [← CoreMemDesign.ndControlsKnownIn_agree hagree]
    exact hk
  have hstep := Nd.Step.commit hA
    (s := { store := st, active := [], scalarQ := T, memoryQ := TM, base, oracle := o,
            settled := false }) rfl rfl hm hk hkv
  refine ⟨_, Nd.Run.tail hrun hstep, ?_, rfl⟩
  show (E.ndWake base (E.scalar.view (E.ndCommitted st T m).scalar)).isEmpty = true
  rw [hw]
  rfl

/-! ## The event level -/

/-- **L2 for one event: the observable outcome does not depend on the
schedule or on the oracle.**  If the start state of the event is
non-interfering under every oracle (the same queue `T`), then any two settled
outcomes of the event, under any two oracles, have the same scalar view. -/
theorem Nd.EventSettles.view_unique {E : CoreMemDesign} {st : CoreMemState} {entry : SvState}
    {T : NbaQueue2} {TM : MemNbaQueue}
    (h : ∀ o, Nd.NonInterfering E (E.ndStart st entry o) T TM)
    {o₁ o₂ : Oracle} {t₁ t₂ : NdState}
    (h₁ : Nd.EventSettles E st entry o₁ t₁) (h₂ : Nd.EventSettles E st entry o₂ t₂) :
    E.scalar.view t₁.store.scalar = E.scalar.view t₂.store.scalar := by
  obtain ⟨s₁, hb₁, hr₁, hs₁⟩ := h₁
  obtain ⟨s₂, hb₂, hr₂, hs₂⟩ := h₂
  obtain ⟨-, rfl, -, -⟩ := NdState.begin_next_inv hb₁
  obtain ⟨-, rfl, -, -⟩ := NdState.begin_next_inv hb₂
  rw [Nd.settled_view (h o₁) hr₁ hs₁, Nd.settled_view (h o₂) hr₂ hs₂]
  rfl

/-- The observable outcome of the event, named: the commit of `T` on the view
after the inputs. -/
theorem Nd.EventSettles.view_eq {E : CoreMemDesign} {st : CoreMemState} {entry : SvState}
    {T : NbaQueue2} {TM : MemNbaQueue} {o : Oracle}
    (h : Nd.NonInterfering E (E.ndStart st entry o) T TM)
    {t : NdState} (ht : Nd.EventSettles E st entry o t) :
    E.scalar.view t.store.scalar = commitNba2 (E.scalar.view (E.ndInput st entry).scalar) T := by
  obtain ⟨s₀, hb, hr, hs⟩ := ht
  obtain ⟨-, rfl, -, -⟩ := NdState.begin_next_inv hb
  exact Nd.settled_view h hr hs

/-- A settled outcome of the event exists, under every oracle. -/
theorem Nd.EventSettles.exists_of_nonInterfering {E : CoreMemDesign} (hA : E.ndAdmitted = true)
    {st : CoreMemState} {entry : SvState} {T : NbaQueue2} {TM : MemNbaQueue} {o : Oracle}
    (hk : E.ControlsKnown st) (hk' : E.ControlsKnown (E.ndInput st entry))
    (h : Nd.NonInterfering E (E.ndStart st entry o) T TM)
    {m : MemState} (hm : (E.ndInput st entry).memory.commitNba TM = some m) :
    ∃ t, Nd.EventSettles E st entry o t := by
  obtain ⟨t, hr, hs, -⟩ := Nd.exists_settled hA h hk' hm
  exact ⟨t, _, NdState.begin_eq_next hA o hk hk', hr, hs⟩

#print axioms NdActiveInv.step
#print axioms Nd.NonInterfering.quiet
#print axioms Nd.settled_store
#print axioms Nd.settled_view
#print axioms Nd.settled_view_unique
#print axioms NdSolo.run
#print axioms Nd.exists_settled
#print axioms Nd.EventSettles.view_unique
#print axioms Nd.EventSettles.view_eq
#print axioms Nd.EventSettles.exists_of_nonInterfering

end LeanModels.Sv.Kernel
