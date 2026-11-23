import LeanModels.Sv.SeqCycleObl

/-!
# Confluence of the admitted NBA edge class

This is the first concrete observable scheduler class.  Every active edge process is
represented by its parser-native process index, and its source-shaped body is
evaluated against the one pre-edge view.  The state records only the observable
NBA commit, so an event choice is the IEEE 1800-2023 §4.7 choice while the
intermediate queue order remains unobservable.  The no-overlap condition is an
admission guard, paid for by `commitNba2_swap`.  The terminal-path theorem
proves schedule independence, and the one-step/order bridges tie each chosen
process back to `CoreMemDesign.edgesV` and its existing `CoreMemDesign.step`
refinement.
This class deliberately contains no blocking edge writes or level-sensitive
reactivation.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

def removeProcessId (i : Nat) : List Nat → List Nat :=
  List.filter (fun j => j != i)

structure EdgeScheduleState where
  pending : List Nat
  view : SvState

def edgeProcQ (E : CoreMemDesign) (before after v : SvState) (mv : MemV) (i : Nat) :
    Res NbaQueue2 :=
  match E.processes[i]? with
  | some p => E.procQ before after v mv p
  | none => .unsupported "4.7: edge process index is outside the design"

def EdgeScheduleStep (E : CoreMemDesign) (before after v : SvState) (mv : MemV)
    (s t : EdgeScheduleState) : Prop :=
  ∃ i q, i ∈ s.pending ∧ edgeProcQ E before after v mv i = .ok q ∧
    t = { pending := removeProcessId i s.pending, view := commitNba2 s.view q }

def EdgeScheduleTerminal (s : EdgeScheduleState) : Prop := s.pending = []

structure EdgeScheduleAdmission (E : CoreMemDesign) (before after v : SvState) (mv : MemV)
    (ids : List Nat) : Prop where
  nodup : ids.Nodup
  inRange : ∀ i ∈ ids, ∃ p, E.processes[i]? = some p
  defined : ∀ i ∈ ids, ∃ q, edgeProcQ E before after v mv i = .ok q
  disjoint : ∀ i ∈ ids, ∀ j ∈ ids, i ≠ j →
    ∀ q₁ q₂, edgeProcQ E before after v mv i = .ok q₁ →
      edgeProcQ E before after v mv j = .ok q₂ →
      ∀ u ∈ q₁, ∀ u' ∈ q₂, u.1 ≠ u'.1

/-! Build the scheduler admission record directly from the indexed parser
    queue receipt.  This keeps the process-index/range correspondence in one
    place for concrete admitted designs. -/
theorem EdgeScheduleAdmission.of_processes_range
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    (F : Nat → NbaQueue2)
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ before after v mv p = .ok (F k))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ u' ∈ F j, u.1 ≠ u'.1) :
    EdgeScheduleAdmission E before after v mv (List.range E.processes.size) := by
  refine {
    nodup := List.nodup_range,
    inRange := ?_,
    defined := ?_,
    disjoint := ?_ }
  · intro i hi
    have hi' : i < E.processes.size := List.mem_range.mp hi
    exact ⟨E.processes[i], Array.getElem?_eq_getElem hi'⟩
  · intro i hi
    have hi' : i < E.processes.size := List.mem_range.mp hi
    simp only [edgeProcQ, Array.getElem?_eq_getElem hi']
    exact ⟨F i, hq i E.processes[i] (Array.getElem?_eq_getElem hi')⟩
  · intro i hi j hj hij q₁ q₂ hq₁ hq₂ u hu u' hu'
    have hi' : i < E.processes.size := List.mem_range.mp hi
    have hj' : j < E.processes.size := List.mem_range.mp hj
    have hqi : q₁ = F i := by
      apply Res.ok.inj
      exact hq₁.symm.trans (by
        simpa [edgeProcQ, Array.getElem?_eq_getElem hi'] using
          hq i E.processes[i] (Array.getElem?_eq_getElem hi'))
    have hqj : q₂ = F j := by
      apply Res.ok.inj
      exact hq₂.symm.trans (by
        simpa [edgeProcQ, Array.getElem?_eq_getElem hj'] using
          hq j E.processes[j] (Array.getElem?_eq_getElem hj'))
    subst q₁
    subst q₂
    exact hdisj i j hij u hu u' hu'

#print axioms EdgeScheduleAdmission.of_processes_range

private theorem removeProcessId_mem_of_ne {i j : Nat} {xs : List Nat}
    (h : j ∈ xs) (hne : j ≠ i) : j ∈ removeProcessId i xs := by
  simp [removeProcessId, h, hne]

private theorem removeProcessId_comm {i j : Nat} (hij : i ≠ j) (xs : List Nat) :
    removeProcessId j (removeProcessId i xs) =
      removeProcessId i (removeProcessId j xs) := by
  simp only [removeProcessId, List.filter_filter]
  apply congrArg (fun p => List.filter p xs)
  funext x
  by_cases hxi : x = i <;> by_cases hxj : x = j <;>
    simp [hxi, hxj, hij, Ne.symm hij, Bool.and_comm]

private theorem removeProcessId_length_lt {i : Nat} {xs : List Nat}
    (hn : xs.Nodup) (hm : i ∈ xs) : (removeProcessId i xs).length < xs.length := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
      simp only [List.nodup_cons, List.mem_cons] at hn hm
      by_cases hxi : x = i
      · subst x
        have hle := List.length_filter_le (fun j => j != i) xs
        simp [removeProcessId]
        omega
      · have htail : i ∈ xs := by
          rcases hm with h | h
          · exact False.elim (hxi h.symm)
          · exact h
        have hlt := ih hn.2 htail
        simp [removeProcessId, hxi]
        omega

private theorem edgeScheduleState_ext {a b : EdgeScheduleState}
    (hp : a.pending = b.pending) (hv : a.view = b.view) : a = b := by
  cases a; cases b; simp_all

theorem EdgeScheduleStep.progress
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {s : EdgeScheduleState} (ad : EdgeScheduleAdmission E before after v mv s.pending)
    (hn : s.pending ≠ []) :
    ∃ t, EdgeScheduleStep E before after v mv s t := by
  cases hs : s.pending with
  | nil => exact False.elim (hn hs)
  | cons i rest =>
      obtain ⟨q, hq⟩ := ad.defined i (by simp [hs])
      let t : EdgeScheduleState :=
        { pending := removeProcessId i s.pending, view := commitNba2 s.view q }
      refine ⟨t, ?_⟩
      refine ⟨i, q, ?_, hq, rfl⟩
      simp [hs]

theorem EdgeScheduleStep.measure_decreases
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {s t : EdgeScheduleState} (ad : s.pending.Nodup)
    (h : EdgeScheduleStep E before after v mv s t) :
    t.pending.length < s.pending.length := by
  obtain ⟨i, q, hi, hq, rfl⟩ := h
  exact removeProcessId_length_lt ad hi

theorem EdgeScheduleStep.local_diamond
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ids : List Nat} (ad : EdgeScheduleAdmission E before after v mv ids)
    {s u w : EdgeScheduleState}
    (hsub : ∀ i ∈ s.pending, i ∈ ids)
    (hnodup : s.pending.Nodup)
    (hv : (s.view.map Prod.fst).Nodup)
    (hu : EdgeScheduleStep E before after v mv s u)
    (hw : EdgeScheduleStep E before after v mv s w) :
    u = w ∨ ∃ z, EdgeScheduleStep E before after v mv u z ∧
      EdgeScheduleStep E before after v mv w z := by
  obtain ⟨i, qi, hi, hqi, rfl⟩ := hu
  obtain ⟨j, qj, hj, hqj, rfl⟩ := hw
  by_cases hij : i = j
  · subst j
    have hqeq : qi = qj := by
      exact Res.ok.inj (hqi.symm.trans hqj)
    subst qj
    exact Or.inl (edgeScheduleState_ext rfl rfl)
  · right
    have hji : j ∈ removeProcessId i s.pending := removeProcessId_mem_of_ne hj (Ne.symm hij)
    have hij' : i ∈ removeProcessId j s.pending := removeProcessId_mem_of_ne hi hij
    have hdisj := ad.disjoint i (hsub i hi) j (hsub j hj) hij qi qj hqi hqj
    let z : EdgeScheduleState :=
      { pending := removeProcessId j (removeProcessId i s.pending)
        view := commitNba2 (commitNba2 s.view qi) qj }
    have hz1 : EdgeScheduleStep E before after v mv
        { pending := removeProcessId i s.pending, view := commitNba2 s.view qi } z := by
      refine ⟨j, qj, hji, hqj, ?_⟩
      rfl
    have hz2 : EdgeScheduleStep E before after v mv
        { pending := removeProcessId j s.pending, view := commitNba2 s.view qj } z := by
      refine ⟨i, qi, hij', hqi, ?_⟩
      dsimp [z]
      apply edgeScheduleState_ext
      · exact removeProcessId_comm hij s.pending
      · simpa [z, commitNba2_append] using (commitNba2_swap hv hdisj).symm
    exact ⟨z, hz1, hz2⟩

private theorem removeProcessId_nodup {i : Nat} {xs : List Nat}
    (h : xs.Nodup) : (removeProcessId i xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      simp only [removeProcessId, List.filter_cons, List.nodup_cons] at h ih ⊢
      by_cases hxi : x = i <;> simp [hxi, h, ih]

private theorem removeProcessId_subset {i : Nat} {xs : List Nat} :
    ∀ {j}, j ∈ removeProcessId i xs → j ∈ xs := by
  intro j h
  exact (List.mem_filter.mp h).1

private theorem edgeScheduleStep_valid
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ids : List Nat}
    {s t : EdgeScheduleState} (hn : s.pending.Nodup)
    (hsub : ∀ i ∈ s.pending, i ∈ ids)
    (hkeys : (s.view.map Prod.fst).Nodup)
    (h : EdgeScheduleStep E before after v mv s t) :
    t.pending.Nodup ∧ (∀ i ∈ t.pending, i ∈ ids) ∧
      (t.view.map Prod.fst).Nodup := by
  obtain ⟨i, q, hi, hq, rfl⟩ := h
  refine ⟨removeProcessId_nodup hn, ?_, ?_⟩
  · intro j hj
    exact hsub j (removeProcessId_subset hj)
  · rw [keys_commitNba2]
    exact hkeys

inductive EdgeScheduleTerminalPath
    (E : CoreMemDesign) (before after v : SvState) (mv : MemV) :
    Nat → EdgeScheduleState → EdgeScheduleState → Prop where
  | terminal {s} (h : s.pending = []) : EdgeScheduleTerminalPath E before after v mv 0 s s
  | head {n s u t} (hn : s.pending ≠ [])
      (hstep : EdgeScheduleStep E before after v mv s u)
      (htail : EdgeScheduleTerminalPath E before after v mv n u t) :
      EdgeScheduleTerminalPath E before after v mv (n + 1) s t

private theorem perm_cons_removeProcessId {i : Nat} {xs : List Nat}
    (hn : xs.Nodup) (hm : i ∈ xs) :
    (i :: removeProcessId i xs).Perm xs := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
      simp only [List.nodup_cons, List.mem_cons] at hn hm
      by_cases hxi : x = i
      · subst x
        have hfilter : List.filter (fun j => j != i) xs = xs :=
          List.filter_eq_self.mpr (fun j hj => by
            by_cases hji : j = i
            · exact False.elim (hn.1 (hji ▸ hj))
            · simp [hji])
        simp [removeProcessId, hfilter]
      · have htail : i ∈ xs := by
          rcases hm with h | h
          · exact False.elim (hxi h.symm)
          · exact h
        have hperm := ih hn.2 htail
        have hs : (i :: x :: removeProcessId i xs).Perm
            (x :: i :: removeProcessId i xs) :=
          List.Perm.swap x i (removeProcessId i xs)
        have hc : (x :: i :: removeProcessId i xs).Perm (x :: xs) :=
          List.Perm.cons x hperm
        simpa [removeProcessId, hxi] using hs.trans hc

theorem EdgeScheduleTerminalPath.exists
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ids : List Nat} (ad : EdgeScheduleAdmission E before after v mv ids)
    {s : EdgeScheduleState} (hsub : ∀ i ∈ s.pending, i ∈ ids)
    (hnodup : s.pending.Nodup) (hkeys : (s.view.map Prod.fst).Nodup) :
    ∃ n t, EdgeScheduleTerminalPath E before after v mv n s t := by
  have aux : ∀ k, ∀ (s : EdgeScheduleState), s.pending.length = k →
      (∀ i ∈ s.pending, i ∈ ids) → s.pending.Nodup →
      (s.view.map Prod.fst).Nodup →
      ∃ n t, EdgeScheduleTerminalPath E before after v mv n s t := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro s hs hsub hnodup hkeys
      by_cases hempty : s.pending = []
      · exact ⟨0, s, .terminal hempty⟩
      · cases hp : s.pending with
        | nil => exact False.elim (hempty hp)
        | cons i rest =>
            obtain ⟨q, hq⟩ := ad.defined i (hsub i (by simp [hp]))
            let u : EdgeScheduleState :=
              { pending := removeProcessId i s.pending,
                view := commitNba2 s.view q }
            have hstep : EdgeScheduleStep E before after v mv s u := by
              refine ⟨i, q, by simp [hp], hq, rfl⟩
            have hu := edgeScheduleStep_valid hnodup hsub hkeys hstep
            have hlt : u.pending.length < k := by
              have := EdgeScheduleStep.measure_decreases hnodup hstep
              omega
            obtain ⟨n, t, ht⟩ := ih u.pending.length hlt u rfl hu.2.1 hu.1 hu.2.2
            exact ⟨n + 1, t, .head hempty hstep ht⟩
  exact aux s.pending.length s rfl hsub hnodup hkeys

theorem EdgeScheduleTerminalPath.exists_processes_range
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {s : EdgeScheduleState} (F : Nat → NbaQueue2)
    (hs : s.pending = List.range E.processes.size)
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ before after v mv p = .ok (F k))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ u' ∈ F j, u.1 ≠ u'.1)
    (hkeys : (s.view.map Prod.fst).Nodup) :
    ∃ n t, EdgeScheduleTerminalPath E before after v mv n s t := by
  have ad := EdgeScheduleAdmission.of_processes_range F hw hq hdisj
  exact EdgeScheduleTerminalPath.exists ad
    (by intro i hi; simpa [hs] using hi)
    (by simpa [hs] using (List.nodup_range : (List.range E.processes.size).Nodup)) hkeys

#print axioms EdgeScheduleTerminalPath.exists_processes_range

/-! The terminal trace records the exact queue contributed by every selected
process.  The process order remains a permutation, so this is the bridge used
to compare a scheduler path with the canonical source-order edge pass. -/
theorem EdgeScheduleTerminalPath.queue_trace
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ids : List Nat} {s t : EdgeScheduleState} {n : Nat}
    (q : Nat → NbaQueue2)
    (hq : ∀ i ∈ ids, edgeProcQ E before after v mv i = .ok (q i))
    (hsub : ∀ i ∈ s.pending, i ∈ ids)
    (hnodup : s.pending.Nodup)
    (hp : EdgeScheduleTerminalPath E before after v mv n s t) :
    ∃ choices : List Nat, choices.Perm s.pending ∧
      t.view = commitNba2 s.view (choices.flatMap q) := by
  induction hp with
  | @terminal s hterm =>
      refine ⟨[], ?_, ?_⟩
      · simpa [hterm]
      · symm
        exact commitNba2_nil s.view
  | @head n s u t hn hstep htail ih =>
      obtain ⟨i, qi, hi, hqi, rfl⟩ := hstep
      have hiids : i ∈ ids := hsub i hi
      have hqeq : qi = q i := by
        exact Res.ok.inj (hqi.symm.trans (hq i hiids))
      have hsub' : ∀ j ∈ (removeProcessId i s.pending), j ∈ ids := by
        intro j hj
        exact hsub j (removeProcessId_subset hj)
      have hnodup' : (removeProcessId i s.pending).Nodup :=
        removeProcessId_nodup hnodup
      obtain ⟨choices, hchoices, htrace⟩ := ih hsub' hnodup'
      refine ⟨i :: choices, ?_, ?_⟩
      · exact (List.Perm.cons i hchoices).trans
          (perm_cons_removeProcessId hnodup hi)
      · rw [htrace, hqeq]
        simp [EdgeScheduleState.view, commitNba2_append, List.flatMap_cons]

#print axioms EdgeScheduleTerminalPath.queue_trace

/-! Pairwise-disjoint queue contributions erase the scheduler permutation. -/
theorem EdgeScheduleTerminalPath.canonical_view
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ids : List Nat} {s t : EdgeScheduleState} {n : Nat}
    (q : Nat → NbaQueue2)
    (hq : ∀ i ∈ ids, edgeProcQ E before after v mv i = .ok (q i))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ q i, ∀ u' ∈ q j, NbaDisj u u')
    (hsub : ∀ i ∈ s.pending, i ∈ ids)
    (hnodup : s.pending.Nodup)
    (hkeys : (s.view.map Prod.fst).Nodup)
    (hp : EdgeScheduleTerminalPath E before after v mv n s t) :
    t.view = commitNba2 s.view (s.pending.flatMap q) := by
  obtain ⟨choices, hchoices, htrace⟩ :=
    EdgeScheduleTerminalPath.queue_trace q hq hsub hnodup hp
  rw [htrace]
  have hchoices_nd : choices.Nodup := hchoices.nodup_iff.mpr hnodup
  exact commitNba2_perm hdisj hchoices hchoices_nd hkeys

#print axioms EdgeScheduleTerminalPath.canonical_view

/-! This is the narrow executor bridge.  The `edgesV` receipt is an
independent source-order evaluator fact.  The scheduler equality is derived
from the terminal trace and the disjointness guard. -/
theorem EdgeScheduleTerminalPath.view_eq_edgesV_commit
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ids : List Nat} {s t : EdgeScheduleState} {n : Nat}
    (q : Nat → NbaQueue2)
    (hq : ∀ i ∈ ids, edgeProcQ E before after v mv i = .ok (q i))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ q i, ∀ u' ∈ q j, NbaDisj u u')
    (hsub : ∀ i ∈ s.pending, i ∈ ids)
    (hnodup : s.pending.Nodup)
    (hkeys : (s.view.map Prod.fst).Nodup)
    (hp : EdgeScheduleTerminalPath E before after v mv n s t)
    {v' : SvState} {mq : MemQV}
    (hroute : E.edgesV before after s.view mv E.processes.toList =
      .ok (v', s.pending.flatMap q, mq)) :
    ∃ r, E.edgesV before after s.view mv E.processes.toList = .ok r ∧
      t.view = commitNba2 s.view r.2.1 := by
  obtain hview := EdgeScheduleTerminalPath.canonical_view q hq hdisj hsub hnodup hkeys hp
  refine ⟨(v', s.pending.flatMap q, mq), hroute, ?_⟩
  simpa using hview

#print axioms EdgeScheduleTerminalPath.view_eq_edgesV_commit

/-! The source-order evaluator exposes the same queue decomposition that the
indexed scheduler consumes.  This theorem deliberately keeps the process
identity in the `procQ` premise instead of introducing a second evaluator. -/
theorem CoreMemDesign.edgesV_queue_flatMap
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ps : List CoreMemProc} {r : ExecV}
    (hw : ∀ p ∈ ps, p.nbaWholeP = true)
    (hroute : E.edgesV before after v mv ps = .ok r) :
    ∃ qs : List NbaQueue2,
      (∀ q ∈ qs, ∃ p ∈ ps, E.procQ before after v mv p = .ok q) ∧
      r.2.1 = qs.flatMap id := by
  induction ps generalizing r with
  | nil =>
      simp only [CoreMemDesign.edgesV, Res.ok.injEq] at hroute
      subst r
      exact ⟨[], by simp, by simp⟩
  | cons p rest ih =>
      obtain ⟨qp, rr, hqp, htargets, hrest, hr⟩ :=
        CoreMemDesign.edgesV_cons_inv (hw p (by simp)) hroute
      obtain ⟨qs, hqs, hflat⟩ := ih (fun q hq => hw q (by simp [hq])) hrest
      refine ⟨qp :: qs, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ⟨p, by simp, hqp⟩
        · obtain ⟨p', hp', hq'⟩ := hqs q hq
          exact ⟨p', by simp [hp'], hq'⟩
      · rw [hr]
        change qp ++ rr.2.1 = qp ++ qs.flatMap id
        rw [hflat]

#print axioms CoreMemDesign.edgesV_queue_flatMap

theorem CoreMemDesign.edgesV_queue_map
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ps : List CoreMemProc} {r : ExecV}
    (q : CoreMemProc → NbaQueue2)
    (hw : ∀ p ∈ ps, p.nbaWholeP = true)
    (hq : ∀ p ∈ ps, E.procQ before after v mv p = .ok (q p))
    (hroute : E.edgesV before after v mv ps = .ok r) :
    r.2.1 = ps.flatMap q := by
  induction ps generalizing r with
  | nil =>
      simp only [CoreMemDesign.edgesV, Res.ok.injEq] at hroute
      subst r
      rfl
  | cons p rest ih =>
      obtain ⟨qp, rr, hqp, htargets, hrest, hr⟩ :=
        CoreMemDesign.edgesV_cons_inv (hw p (by simp)) hroute
      have hqp' : qp = q p := by
        exact Res.ok.inj (hqp.symm.trans (hq p (by simp)))
      have hrestq := ih (fun q' hq' => hw q' (by simp [hq']))
        (fun q' hq' => hq q' (by simp [hq'])) hrest
      rw [hr, hqp', hrestq]
      rfl

#print axioms CoreMemDesign.edgesV_queue_map

/-! The indexed form aligns each source-order process with the queue slot
    consumed by the scheduler's process-index list. -/
theorem CoreMemDesign.edgesV_queue_indexed
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ps : List CoreMemProc} {r : ExecV} (offset : Nat)
    (F : Nat → NbaQueue2)
    (hw : ∀ p ∈ ps, p.nbaWholeP = true)
    (hq : ∀ k p, ps[k]? = some p →
      E.procQ before after v mv p = .ok (F (offset + k)))
    (hroute : E.edgesV before after v mv ps = .ok r) :
    r.2.1 = (List.range ps.length).flatMap (fun k => F (offset + k)) := by
  induction ps generalizing offset r with
  | nil =>
      simp only [CoreMemDesign.edgesV, Res.ok.injEq] at hroute
      subst r
      simp
  | cons p rest ih =>
      obtain ⟨qp, rr, hqp, htargets, hrest, hr⟩ :=
        CoreMemDesign.edgesV_cons_inv (hw p (by simp)) hroute
      have hpq : qp = F offset := by
        apply Res.ok.inj
        exact hqp.symm.trans (hq 0 p (by simp))
      have hqrest : ∀ k p', (rest[k]? = some p') →
          E.procQ before after v mv p' = .ok (F (offset + (k + 1))) := by
        intro k p' hk
        apply hq (k + 1) p'
        simpa using hk
      have hqrest' : ∀ k p', (rest[k]? = some p') →
          E.procQ before after v mv p' = .ok (F ((offset + 1) + k)) := by
        intro k p' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hqrest k p' hk
      have htail := ih (offset := offset + 1) (r := rr)
        (fun p' hp' => hw p' (by simp [hp'])) hqrest' hrest
      rw [hr, hpq, htail]
      simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
        List.flatMap_map]
      have hpoint : ∀ xs : List Nat,
          List.flatMap (fun k => F ((offset + 1) + k)) xs =
            List.flatMap (fun k => F (offset + (k + 1))) xs := by
        intro xs
        induction xs with
        | nil => rfl
        | cons k ks ih =>
            simp only [List.flatMap_cons]
            rw [ih]
            congr 1
            congr 1
            omega
      simpa [Nat.zero_add, Nat.succ_eq_add_one] using
        congrArg (fun xs => F offset ++ xs) (hpoint (List.range rest.length))

#print axioms CoreMemDesign.edgesV_queue_indexed

theorem CoreMemDesign.edgesV_queue_processes_indexed
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV} {r : ExecV}
    (offset : Nat) (F : Nat → NbaQueue2)
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ before after v mv p = .ok (F (offset + k)))
    (hroute : E.edgesV before after v mv E.processes.toList = .ok r) :
    r.2.1 = (List.range E.processes.size).flatMap (fun k => F (offset + k)) := by
  apply CoreMemDesign.edgesV_queue_indexed offset F
    (ps := E.processes.toList) (r := r)
  · intro p hp
    obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
    have hk' : k < E.processes.size := by simpa using hk
    have hopt : E.processes[k]? = some p := by
      rw [← Array.getElem?_toList]
      exact (List.getElem?_eq_getElem hk).trans (congrArg some hpk)
    exact hw k p hopt
  · intro k p hk
    obtain ⟨hklt, hkp⟩ := List.getElem?_eq_some_iff.mp hk
    have hk' : k < E.processes.size := by simpa using hklt
    have hopt : E.processes[k]? = some p := by
      rw [← Array.getElem?_toList]
      exact hk
    exact hq k p hopt
  · exact hroute

#print axioms CoreMemDesign.edgesV_queue_processes_indexed

/-! The indexed receipt feeds the terminal-path bridge.  The queue receipt is
    still an explicit evaluator premise, so this theorem does not identify a
    scheduler path with `CoreMemDesign.step`. -/
theorem EdgeScheduleTerminalPath.view_eq_edgesV_processes_indexed
    {E : CoreMemDesign} {before after : SvState} {mv : MemV}
    {s t : EdgeScheduleState} {n : Nat} (F : Nat → NbaQueue2)
    (hs : s.pending = List.range E.processes.size)
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ before after s.view mv p = .ok (F k))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ u' ∈ F j, u.1 ≠ u'.1)
    (hkeys : (s.view.map Prod.fst).Nodup)
    (hp : EdgeScheduleTerminalPath E before after s.view mv n s t)
    {r : ExecV}
    (hroute : E.edgesV before after s.view mv E.processes.toList = .ok r) :
    ∃ r', E.edgesV before after s.view mv E.processes.toList = .ok r' ∧
      t.view = commitNba2 s.view r'.2.1 := by
  have hqEdge : ∀ i ∈ s.pending, edgeProcQ E before after s.view mv i = .ok (F i) := by
    intro i hi
    have hi' : i < E.processes.size := by
      rw [hs] at hi
      exact List.mem_range.mp hi
    simp only [edgeProcQ, Array.getElem?_eq_getElem hi']
    exact hq i E.processes[i] (Array.getElem?_eq_getElem hi')
  have hqroute := CoreMemDesign.edgesV_queue_processes_indexed
    (E := E) (before := before) (after := after) (v := s.view) (mv := mv)
    0 F hw (by
      intro k p hk
      simpa [Nat.zero_add] using hq k p hk) hroute
  have hroute' : E.edgesV before after s.view mv E.processes.toList =
      .ok (r.1, s.pending.flatMap F, r.2.2) := by
    rw [hroute]
    cases r with
    | mk rv rm =>
      cases rm with
      | mk rq mm =>
        simp only at hqroute ⊢
        have hqroute' : rq = List.flatMap F s.pending := by
          rw [hs]
          simpa [Nat.zero_add] using hqroute
        simpa [hqroute']
  have hview := EdgeScheduleTerminalPath.view_eq_edgesV_commit F hqEdge
    (fun i j hij u hu u' hu' => Or.inl (hdisj i j hij u hu u' hu'))
    (by intro i hi; exact hi)
    (by simpa [hs] using (List.nodup_range : (List.range E.processes.size).Nodup))
    hkeys hp hroute'
  exact hview

#print axioms EdgeScheduleTerminalPath.view_eq_edgesV_processes_indexed

/-! Carry the scheduler's canonical terminal view through the real step
    refinement.  The route receipt remains explicit, so this is a bridge for
    the admitted class rather than a claim that every slot has such a receipt. -/
theorem EdgeScheduleTerminalPath.refines_step
    {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    {before after : SvState} {mv : MemV}
    {s t : EdgeScheduleState} {n : Nat} (F : Nat → NbaQueue2)
    (hs : s.pending = List.range E.processes.size)
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ before after s.view mv p = .ok (F k))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ u' ∈ F j, u.1 ≠ u'.1)
    (hkeys : (s.view.map Prod.fst).Nodup)
    (hp : EdgeScheduleTerminalPath E before after s.view mv n s t)
    {r : ExecV}
    (hroute : E.edgesV before after s.view mv E.processes.toList = .ok r) :
    ∃ st', E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' ∧ t.view = commitNba2 s.view r.2.1 := by
  obtain ⟨st', hstep, hvstep, hmstep, -, -⟩ :=
    CoreMemDesign.step_seqI hP hO hc hmc hty hslot
  obtain ⟨r', hr', hview⟩ :=
    EdgeScheduleTerminalPath.view_eq_edgesV_processes_indexed F hs hw hq hdisj hkeys hp hroute
  have hreq : r' = r := Res.ok.inj (hr'.symm.trans hroute)
  subst r'
  exact ⟨st', hstep, hvstep, hmstep, hview⟩

#print axioms EdgeScheduleTerminalPath.refines_step

theorem EdgeScheduleTerminalPath.unique
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ids : List Nat} (ad : EdgeScheduleAdmission E before after v mv ids)
    {s t₁ t₂ : EdgeScheduleState} {n₁ n₂ : Nat}
    (hsub : ∀ i ∈ s.pending, i ∈ ids) (hnodup : s.pending.Nodup)
    (hkeys : (s.view.map Prod.fst).Nodup)
    (hp₁ : EdgeScheduleTerminalPath E before after v mv n₁ s t₁)
    (hp₂ : EdgeScheduleTerminalPath E before after v mv n₂ s t₂) :
    t₁ = t₂ := by
  have aux : ∀ k, ∀ (s : EdgeScheduleState) (t₁ t₂ : EdgeScheduleState), ∀ n₁ n₂,
      s.pending.length = k → s.pending.Nodup →
      (∀ i ∈ s.pending, i ∈ ids) → (s.view.map Prod.fst).Nodup →
      EdgeScheduleTerminalPath E before after v mv n₁ s t₁ →
      EdgeScheduleTerminalPath E before after v mv n₂ s t₂ → t₁ = t₂ := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro s t₁ t₂ n₁ n₂ hlen hnd hsub' hkeys' hp₁ hp₂
        cases hp₁ with
        | terminal hterm =>
            cases hp₂ with
            | terminal => rfl
            | head hn2 hs2 ht2 =>
                exact False.elim (hn2 hterm)
        | @head _ s u₁ t₁ hn1 hs1 ht1 =>
            cases hp₂ with
            | terminal hterm => exact False.elim (hn1 hterm)
            | @head _ _ u₂ _ hn2 hs2 ht2 =>
                have hu₁ := hs1
                have hu₂ := hs2
                have hlt₁ : u₁.pending.length < k := by
                  have hlt := EdgeScheduleStep.measure_decreases hnd hu₁
                  omega
                have hlt₂ : u₂.pending.length < k := by
                  have hlt := EdgeScheduleStep.measure_decreases hnd hu₂
                  omega
                obtain hvalid₁ := edgeScheduleStep_valid hnd hsub' hkeys' hu₁
                obtain hvalid₂ := edgeScheduleStep_valid hnd hsub' hkeys' hu₂
                rcases EdgeScheduleStep.local_diamond ad hsub' hnd hkeys' hu₁ hu₂ with
                  heq | ⟨w, huw₁, huw₂⟩
                · subst u₂
                  exact ih u₁.pending.length hlt₁ u₁ t₁ t₂ _ _ rfl
                    hvalid₁.1 hvalid₁.2.1 hvalid₁.2.2 ht1 ht2
                · have hw₁ := edgeScheduleStep_valid hvalid₁.1 hvalid₁.2.1 hvalid₁.2.2 huw₁
                  have hw₂ := edgeScheduleStep_valid hvalid₂.1 hvalid₂.2.1 hvalid₂.2.2 huw₂
                  obtain ⟨nw, tw, htw⟩ := EdgeScheduleTerminalPath.exists ad
                    hw₁.2.1 hw₁.1 hw₁.2.2
                  have hn_u₁ : u₁.pending ≠ [] := by
                    intro he
                    obtain ⟨i, qi, hi, hqi, rfl⟩ := huw₁
                    simp [he] at hi
                  have hn_u₂ : u₂.pending ≠ [] := by
                    intro he
                    obtain ⟨i, qi, hi, hqi, rfl⟩ := huw₂
                    simp [he] at hi
                  have hpath₁ := EdgeScheduleTerminalPath.head hn_u₁ huw₁ htw
                  have hpath₂ := EdgeScheduleTerminalPath.head hn_u₂ huw₂ htw
                  have e₁ := ih u₁.pending.length hlt₁ u₁ t₁ tw _ _ rfl
                    hvalid₁.1 hvalid₁.2.1 hvalid₁.2.2 ht1 hpath₁
                  have e₂ := ih u₂.pending.length hlt₂ u₂ t₂ tw _ _ rfl
                    hvalid₂.1 hvalid₂.2.1 hvalid₂.2.2 ht2 hpath₂
                  exact e₁.trans e₂.symm
  exact aux s.pending.length s t₁ t₂ n₁ n₂ rfl hnodup hsub hkeys hp₁ hp₂

/-! Each scheduler choice is an executor choice.  This is the one-step bridge
used when a path is folded over the active process list.  The source body is
still consumed by `procQ`/`execV`; no scheduler-specific update semantics is
introduced here. -/
theorem EdgeScheduleStep.executor_cons_bridge
    {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {i : Nat} {p : CoreMemProc} {q : NbaQueue2} {rest : List CoreMemProc}
    (hi : E.processes[i]? = some p) (hp : p.nbaWholeP = true)
    (hq : edgeProcQ E before after v mv i = .ok q)
    {r : ExecV} (hr : E.edgesV before after v mv rest = .ok r) :
    E.edgesV before after v mv (p :: rest) = .ok (r.1, q ++ r.2.1, r.2.2) := by
  have hq' : E.procQ before after v mv p = .ok q := by
    simpa [edgeProcQ, hi] using hq
  exact CoreMemDesign.edgesV_cons_mk hp hq' hr

/-! The canonical route bridge is then available without an event-order
choice.  `edgesV_order` supplies the permutation result, and the existing
`edge_schedule_refines_step` theorem carries that result through `step`. -/
theorem EdgeScheduleStep.executor_order_bridge
    {E : CoreMemDesign} (hO : E.seqOblI = true)
    {ps : List CoreMemProc} (hσ : ps.Perm E.processes.toList)
    {before after v : SvState} {mv : MemV} (hv : (v.map Prod.fst).Nodup)
    {r : ExecV}
    (hr : E.edgesV before after v mv E.processes.toList = .ok r) :
    ∃ r', E.edgesV before after v mv ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      commitMemV mv r'.2.2 = commitMemV mv r.2.2 :=
  CoreMemDesign.edgesV_order hO hσ hv hr

#print axioms EdgeScheduleTerminalPath.unique
#print axioms EdgeScheduleStep.executor_cons_bridge

end LeanModels.Sv.Kernel
