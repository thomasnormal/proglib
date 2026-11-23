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
