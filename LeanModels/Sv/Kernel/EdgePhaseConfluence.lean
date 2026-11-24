import LeanModels.Sv.Kernel.CoreMemResume
import LeanModels.Sv.Scheduler
import LeanModels.Sv.SeqCycleStep
import LeanModels.Sv.SeqCycle

/-!
# Observable confluence for the source-shaped edge phase

`EdgePhaseStep` is the real §4.7 active-region relation.  The raw state keeps
NBA issue order, so this packet compares the committed observable view.  For
two active edge cursors whose resumes are stable NBA-only actions, disjoint
queues commute by the canonical NBA theorem.  This is the first bridge from
the real source-shaped relation to the executor's observable commit.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

def EdgePhaseState.observable (E : CoreMemDesign) (s : EdgePhaseState) : SvState :=
  commitNba2 (E.scalar.view s.state.scalar) s.scalarQ

/-! The memory observation is kept as a separate adapter because the
canonical edge cursor stores declaration-identity records (`MemNbaRecord`),
while the view-level memory theorem is stated over `MemQV`.  A receipt for a
chosen record projection is therefore an explicit premise of the adapter.
This does not identify the two record representations by fiat. -/
def EdgePhaseState.observableMemoryView (E : CoreMemDesign) (decode : MemNbaRecord → String × Int × LVec)
    (mv : MemV) (s : EdgePhaseState) : SvState × MemV :=
  (EdgePhaseState.observable E s, commitMemV mv (s.memoryQ.map decode))

private theorem after_first_active
    {s : EdgePhaseState}
    {c₁ c₂ : EdgeCursor} {r₁ : CoreMemExecResult} {n₁ : EdgeCursor}
    (ha : s.active = [c₁, c₂]) (hn : n₁.work = [])
    (hs : r₁.state = s.state) (hm : r₁.memoryQ = []) :
    (s.after r₁ n₁ [] [c₂]).active = [c₂] := by
  simp [EdgePhaseState.after, ha, hn, hs, hm]

private theorem after_second_active
    {s : EdgePhaseState}
    {r₁ r₂ : CoreMemExecResult} {n₁ n₂ : EdgeCursor}
    (hn₁ : n₁.work = []) (hn₂ : n₂.work = [])
    (hs₁ : r₁.state = s.state) (hs₂ : r₂.state = s.state)
    (hm₁ : r₁.memoryQ = []) (hm₂ : r₂.memoryQ = []) :
    ((s.after r₁ n₁ [] []).after r₂ n₂ [] []).active = [] := by
  simp [EdgePhaseState.after, hn₁, hn₂, hs₁, hs₂, hm₁, hm₂]

/-- The two legal selections of two active NBA-only cursors have equal
committed observable state.  The queues may retain different issue order. -/
theorem EdgePhaseStep.two_nba_observable_diamond
    {E : CoreMemDesign} {s : EdgePhaseState}
    {c₁ c₂ : EdgeCursor} {r₁ r₂ : CoreMemExecResult}
    {n₁ n₂ : EdgeCursor}
    (ha : s.active = [c₁, c₂]) (hne : c₁ ≠ c₂)
    (h₁ : c₁.resume E s.state = .ok (r₁, n₁))
    (h₂ : c₂.resume E s.state = .ok (r₂, n₂))
    (hn₁ : n₁.work = []) (hn₂ : n₂.work = [])
    (hs₁ : r₁.state = s.state) (hs₂ : r₂.state = s.state)
    (hm₁ : r₁.memoryQ = []) (hm₂ : r₂.memoryQ = [])
    (hkeys : (E.scalar.view s.state.scalar).map Prod.fst |>.Nodup)
    (hdisj : ∀ u ∈ r₁.scalarQ, ∀ u' ∈ r₂.scalarQ, NbaDisj u u') :
    EdgePhaseState.observable E
        ((s.after r₁ n₁ [] [c₂]).after r₂ n₂ [] []) =
      EdgePhaseState.observable E
        ((s.after r₂ n₂ [c₁] []).after r₁ n₁ [] []) := by
  have hstep₁ : EdgePhaseStep E s (s.after r₁ n₁ [] [c₂]) :=
    .select (by simp [ha]) h₁
  have hactive₁ := after_first_active (s := s) ha hn₁ hs₁ hm₁
  have hstep₂ : EdgePhaseStep E (s.after r₁ n₁ [] [c₂])
      ((s.after r₁ n₁ [] [c₂]).after r₂ n₂ [] []) := by
    apply EdgePhaseStep.select (cursor := c₂) (before := []) (after := [])
    · simpa [hactive₁]
    · simpa [EdgePhaseState.after, hs₁] using h₂
  have hstep₃ : EdgePhaseStep E s (s.after r₂ n₂ [c₁] []) := by
    exact .select (by simp [ha]) h₂
  have hstep₄ : EdgePhaseStep E (s.after r₂ n₂ [c₁] [])
      ((s.after r₂ n₂ [c₁] []).after r₁ n₁ [] []) := by
    apply EdgePhaseStep.select (cursor := c₁) (before := []) (after := [])
    · simp [EdgePhaseState.after, hn₂, hs₂, hm₂]
    · simpa [EdgePhaseState.after, hs₂] using h₁
  let base := E.scalar.view s.state.scalar
  let hbase := commitNba2 base s.scalarQ
  have hkeys2 : hbase.map Prod.fst |>.Nodup := by
    dsimp [hbase]
    rw [keys_commitNba2]
    exact hkeys
  have hswap := commitNba2_swap hkeys2 hdisj
  unfold EdgePhaseState.observable
  simp only [EdgePhaseState.after, hs₁, hs₂, hn₁, hn₂, hm₁, hm₂, List.append_nil]
  simp only [List.append_assoc]
  change commitNba2 base (s.scalarQ ++ (r₁.scalarQ ++ r₂.scalarQ)) =
    commitNba2 base (s.scalarQ ++ (r₂.scalarQ ++ r₁.scalarQ))
  calc
    commitNba2 base (s.scalarQ ++ (r₁.scalarQ ++ r₂.scalarQ)) =
        commitNba2 hbase (r₁.scalarQ ++ r₂.scalarQ) := by
          dsimp [hbase]
          rw [commitNba2_append]
    _ = commitNba2 hbase (r₂.scalarQ ++ r₁.scalarQ) := hswap
    _ = commitNba2 base (s.scalarQ ++ (r₂.scalarQ ++ r₁.scalarQ)) := by
          dsimp [hbase]
          symm
          rw [commitNba2_append]


#print axioms EdgePhaseStep.two_nba_observable_diamond

/-! The same local diamond carries memory-element NBAs when each cursor's
issue-time canonical records have an explicit view-level receipt.  Scalar and
memory footprints are separate, so each commutation premise is visible.  The
relation remains fine-grained: only the two legal first selections are
compared, and no source-order permutation theorem is substituted for it. -/
theorem EdgePhaseStep.two_nba_memory_observable_diamond
    {E : CoreMemDesign} {s : EdgePhaseState}
    {c₁ c₂ : EdgeCursor} {r₁ r₂ : CoreMemExecResult}
    {n₁ n₂ : EdgeCursor} {m₁ m₂ : MemQV} {mv : MemV}
    {decode : MemNbaRecord → String × Int × LVec}
    (ha : s.active = [c₁, c₂]) (hne : c₁ ≠ c₂)
    (h₁ : c₁.resume E s.state = .ok (r₁, n₁))
    (h₂ : c₂.resume E s.state = .ok (r₂, n₂))
    (hn₁ : n₁.work = []) (hn₂ : n₂.work = [])
    (hs₁ : r₁.state = s.state) (hs₂ : r₂.state = s.state)
    (hm₁ : r₁.memoryQ.map decode = m₁)
    (hm₂ : r₂.memoryQ.map decode = m₂)
    (hkeys : (E.scalar.view s.state.scalar).map Prod.fst |>.Nodup)
    (hdisjS : ∀ u ∈ r₁.scalarQ, ∀ u' ∈ r₂.scalarQ, NbaDisj u u')
    (hdisjM : ∀ u ∈ m₁, ∀ u' ∈ m₂, u.1 ≠ u'.1) :
    EdgePhaseState.observableMemoryView E decode mv
        ((s.after r₁ n₁ [] [c₂]).after r₂ n₂ [] []) =
      EdgePhaseState.observableMemoryView E decode mv
        ((s.after r₂ n₂ [c₁] []).after r₁ n₁ [] []) := by
  have hstep₁ : EdgePhaseStep E s (s.after r₁ n₁ [] [c₂]) :=
    .select (by simp [ha]) h₁
  have hactive₁ : (s.after r₁ n₁ [] [c₂]).active = [c₂] := by
    simp [EdgePhaseState.after, ha, hn₁, hs₁]
  have hstep₂ : EdgePhaseStep E (s.after r₁ n₁ [] [c₂])
      ((s.after r₁ n₁ [] [c₂]).after r₂ n₂ [] []) := by
    apply EdgePhaseStep.select (cursor := c₂) (before := []) (after := [])
    · simpa [hactive₁]
    · simpa [EdgePhaseState.after, hs₁] using h₂
  have hstep₃ : EdgePhaseStep E s (s.after r₂ n₂ [c₁] []) := by
    exact .select (by simp [ha]) h₂
  have hstep₄ : EdgePhaseStep E (s.after r₂ n₂ [c₁] [])
      ((s.after r₂ n₂ [c₁] []).after r₁ n₁ [] []) := by
    apply EdgePhaseStep.select (cursor := c₁) (before := []) (after := [])
    · simp [EdgePhaseState.after, hn₂, hs₂]
    · simpa [EdgePhaseState.after, hs₂] using h₁
  have hkeys2 :
      (commitNba2 (E.scalar.view s.state.scalar) s.scalarQ).map Prod.fst |>.Nodup := by
    rw [keys_commitNba2]
    exact hkeys
  have hswapS := commitNba2_swap hkeys2 hdisjS
  have hswapM := commitMemV_swap (mv := mv) hdisjM
  unfold EdgePhaseState.observableMemoryView EdgePhaseState.observable
  simp only [EdgePhaseState.after, hs₁, hs₂, hn₁, hn₂,
    List.map_append, List.append_nil, hm₁, hm₂]
  simp only [List.append_assoc]
  apply Prod.ext
  · change commitNba2 (E.scalar.view s.state.scalar)
      (s.scalarQ ++ (r₁.scalarQ ++ r₂.scalarQ)) =
      commitNba2 (E.scalar.view s.state.scalar)
      (s.scalarQ ++ (r₂.scalarQ ++ r₁.scalarQ))
    let base := E.scalar.view s.state.scalar
    let hbase := commitNba2 base s.scalarQ
    calc
      commitNba2 base (s.scalarQ ++ (r₁.scalarQ ++ r₂.scalarQ)) =
          commitNba2 hbase (r₁.scalarQ ++ r₂.scalarQ) := by
            dsimp [hbase]
            rw [commitNba2_append]
      _ = commitNba2 hbase (r₂.scalarQ ++ r₁.scalarQ) := hswapS
      _ = commitNba2 base (s.scalarQ ++ (r₂.scalarQ ++ r₁.scalarQ)) := by
            dsimp [hbase]
            symm
            rw [commitNba2_append]
  · change commitMemV mv
      (s.memoryQ.map decode ++ (m₁ ++ m₂)) =
      commitMemV mv
      (s.memoryQ.map decode ++ (m₂ ++ m₁))
    let base := commitMemV mv (s.memoryQ.map decode)
    calc
      commitMemV mv (s.memoryQ.map decode ++ (m₁ ++ m₂)) =
          commitMemV base (m₁ ++ m₂) := by
            dsimp [base]
            rw [commitMemV_append]
      _ = commitMemV base (m₂ ++ m₁) := commitMemV_swap hdisjM
      _ = commitMemV mv (s.memoryQ.map decode ++ (m₂ ++ m₁)) := by
            dsimp [base]
            symm
            rw [commitMemV_append]

#print axioms EdgePhaseStep.two_nba_memory_observable_diamond

end LeanModels.Sv.Kernel

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

/-! ## Level-sensitive commutation receipt

The level-sensitive phase cannot inherit the NBA disjointness guard.  A
blocking write changes the shared view immediately, so the scheduler proof
must expose the two cross-resume executions that establish commutation for the
particular pair of cursors. -/

theorem CombPhaseStep.two_cursor_commute
    {E : CoreMemDesign} {s : CombPhaseState}
    {c₁ c₂ n₁ n₂ : CombCursor}
    {x₁ x₂ y₁ y₂ : CoreMemState} {v₁ v₂ w₁ w₂ : SvState}
    (ha : s.active = [c₁, c₂])
    (h₁ : c₁.resume E s.state s.view = .ok (x₁, v₁, n₁))
    (h₂ : c₂.resume E s.state s.view = .ok (x₂, v₂, n₂))
    (h₂₁ : c₂.resume E x₁ v₁ = .ok (y₁, w₁, n₂))
    (h₁₂ : c₁.resume E x₂ v₂ = .ok (y₂, w₂, n₁))
    (hstate : y₁ = y₂) (hview : w₁ = w₂)
    (hn₁ : n₁.work = []) (hn₂ : n₂.work = []) :
    ∃ u₁ u₂ z,
      CombPhaseStep E s u₁ ∧ CombPhaseStep E s u₂ ∧
      CombPhaseStep E u₁ z ∧ CombPhaseStep E u₂ z := by
  let u₁ := CombPhaseState.after s x₁ v₁ n₁ [] [c₂]
  let u₂ := CombPhaseState.after s x₂ v₂ n₂ [c₁] []
  let z := CombPhaseState.after u₁ y₁ w₁ n₂ [] []
  have hz : CombPhaseState.after u₁ y₁ w₁ n₂ [] [] =
      CombPhaseState.after u₂ y₂ w₂ n₁ [] [] := by
    simp [u₁, u₂, CombPhaseState.after, hn₁, hn₂, hstate, hview]
  have hs₁ : CombPhaseStep E s u₁ := .select (by simpa [u₁, ha]) h₁
  have hs₂ : CombPhaseStep E s u₂ := .select (by simpa [u₂, ha]) h₂
  have hu₁ : CombPhaseStep E u₁ z := by
    change CombPhaseStep E u₁ (CombPhaseState.after u₁ y₁ w₁ n₂ [] [])
    apply CombPhaseStep.select (cursor := c₂) (next := n₂) (state := y₁) (view := w₁)
      (before := []) (after := [])
    · simp [u₁, z, CombPhaseState.after, hn₁]
    · simpa [u₁, CombPhaseState.after] using h₂₁
  have hu₂ : CombPhaseStep E u₂ z := by
    change CombPhaseStep E u₂ (CombPhaseState.after u₁ y₁ w₁ n₂ [] [])
    rw [hz]
    apply CombPhaseStep.select (cursor := c₁) (next := n₁) (state := y₂) (view := w₂)
      (before := []) (after := [])
    · simp [u₂, z, CombPhaseState.after, hn₂]
    · simpa [z, u₂, CombPhaseState.after, hstate, hview] using h₁₂
  exact ⟨u₁, u₂, z, hs₁, hs₂, hu₁, hu₂⟩

#print axioms CombPhaseStep.two_cursor_commute

/-! A level-sensitive progress receipt is separate from commutation.  It only
requires that every active cursor has a successful source-shaped resume. -/
structure CombPhaseAdmission (E : CoreMemDesign) (s : CombPhaseState) where
  resume_ok : ∀ cursor, cursor ∈ s.active →
    ∃ state view next, cursor.resume E s.state s.view = .ok (state, view, next)

theorem CombPhaseStep.progress
    {E : CoreMemDesign} {s : CombPhaseState}
    (ad : CombPhaseAdmission E s) (hn : s.active ≠ []) :
    ∃ t, CombPhaseStep E s t := by
  cases hxs : s.active with
  | nil => exact False.elim (hn hxs)
  | cons cursor rest =>
    have hmem : cursor ∈ s.active := by simp [hxs]
    obtain ⟨state, view, next, hresume⟩ := ad.resume_ok cursor hmem
    exact ⟨s.after state view next [] rest, .select hxs hresume⟩

#print axioms CombPhaseStep.progress

/-! A blocking combinational phase needs an explicit termination receipt.  A
successful resume may requeue its cursor when a reactive process wakes itself,
so source-shaped admission must provide both the empty-continuation fact and
the local scheduler diamond.  The following relation is the concrete
terminal-path form of that receipt. -/
structure CombPhaseConfluenceAdmission (E : CoreMemDesign) where
  resume_ok : ∀ (s : CombPhaseState) (cursor : CombCursor), cursor ∈ s.active →
    ∃ state view next, cursor.resume E s.state s.view = .ok (state, view, next)
  continuation_empty : ∀ (s : CombPhaseState) (cursor : CombCursor)
    (state : CoreMemState) (view : SvState) (next : CombCursor),
    cursor ∈ s.active →
    cursor.resume E s.state s.view = .ok (state, view, next) → next.work = []
  diamond : ∀ {s u v : CombPhaseState},
    CombPhaseStep E s u → CombPhaseStep E s v →
      u = v ∨ ∃ w, CombPhaseStep E u w ∧ CombPhaseStep E v w

inductive CombPhaseTerminalPath (E : CoreMemDesign) :
    Nat → CombPhaseState → CombPhaseState → Prop where
  | terminal {s} (h : CombPhaseQuiescent s) :
      CombPhaseTerminalPath E 0 s s
  | head {n s u t} (hn : ¬ CombPhaseQuiescent s)
      (hstep : CombPhaseStep E s u)
      (htail : CombPhaseTerminalPath E n u t) :
      CombPhaseTerminalPath E (n + 1) s t

private theorem CombPhaseStep.active_length_decreases
    {E : CoreMemDesign} {s t : CombPhaseState}
    (ad : CombPhaseConfluenceAdmission E)
    (h : CombPhaseStep E s t) :
    t.active.length < s.active.length := by
  cases h with
  | select hactive hresume =>
      rename_i before after cursor next state view
      have hmem : cursor ∈ s.active := by
        rw [hactive]
        simp
      have hempty := ad.continuation_empty s cursor state view next hmem hresume
      rw [hactive]
      simp [CombPhaseState.after, hempty]

theorem CombPhaseTerminalPath.exists
    {E : CoreMemDesign} (ad : CombPhaseConfluenceAdmission E)
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
          let u := s.after state view next [] rest
          have hstep : CombPhaseStep E s u := by
            exact .select (by simpa [hsplit, u]) hresume
          have hlt : u.active.length < k := by
            have hdec := CombPhaseStep.active_length_decreases ad hstep
            simpa [hlen] using hdec
          obtain ⟨n, t, htail⟩ := ih u.active.length hlt u rfl
          exact ⟨n + 1, t, .head hempty hstep htail⟩
  exact aux s.active.length s rfl

theorem CombPhaseTerminalPath.unique
    {E : CoreMemDesign} (ad : CombPhaseConfluenceAdmission E)
    {s t₁ t₂ : CombPhaseState} {n₁ n₂ : Nat}
    (hp₁ : CombPhaseTerminalPath E n₁ s t₁)
    (hp₂ : CombPhaseTerminalPath E n₂ s t₂) : t₁ = t₂ := by
  have aux : ∀ k, ∀ s t₁ t₂ : CombPhaseState, ∀ n₁ n₂,
      s.active.length = k →
      CombPhaseTerminalPath E n₁ s t₁ →
      CombPhaseTerminalPath E n₂ s t₂ → t₁ = t₂ := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro s t₁ t₂ n₁ n₂ hlen hpath₁ hpath₂
        cases hpath₁ with
        | terminal hterm₁ =>
            cases hpath₂ with
            | terminal => rfl
            | head _ hstep₂ _ =>
                have hnil : s.active = [] := hterm₁
                cases hstep₂ with
                | select hactive _ =>
                    rw [hnil] at hactive
                    simp at hactive
        | @head _ _ u₁ _ hn₁ hstep₁ tail₁ =>
            cases hpath₂ with
            | terminal hterm₂ =>
                have hnil : s.active = [] := hterm₂
                cases hstep₁ with
                | select hactive _ =>
                    rw [hnil] at hactive
                    simp at hactive
            | @head _ _ u₂ _ _ hstep₂ tail₂ =>
                have hlt₁ : u₁.active.length < k := by
                  simpa [hlen] using CombPhaseStep.active_length_decreases ad hstep₁
                have hlt₂ : u₂.active.length < k := by
                  simpa [hlen] using CombPhaseStep.active_length_decreases ad hstep₂
                rcases ad.diamond hstep₁ hstep₂ with heq | ⟨w, huw₁, huw₂⟩
                · subst u₂
                  exact ih u₁.active.length hlt₁ u₁ t₁ t₂ _ _ rfl tail₁ tail₂
                · obtain ⟨nw, tw, htw⟩ := CombPhaseTerminalPath.exists ad w
                  have hnot₁ : ¬ CombPhaseQuiescent u₁ := by
                    intro hq
                    have hnil : u₁.active = [] := hq
                    cases huw₁ with
                    | select hactive _ =>
                        rw [hnil] at hactive
                        simp at hactive
                  have hnot₂ : ¬ CombPhaseQuiescent u₂ := by
                    intro hq
                    have hnil : u₂.active = [] := hq
                    cases huw₂ with
                    | select hactive _ =>
                        rw [hnil] at hactive
                        simp at hactive
                  have hjoin₁ := ih u₁.active.length hlt₁ u₁ t₁ tw _ _ rfl tail₁
                    (.head hnot₁ huw₁ htw)
                  have hjoin₂ := ih u₂.active.length hlt₂ u₂ t₂ tw _ _ rfl tail₂
                    (.head hnot₂ huw₂ htw)
                  exact hjoin₁.trans hjoin₂.symm
  exact aux s.active.length s t₁ t₂ n₁ n₂ rfl hp₁ hp₂

#print axioms CombPhaseTerminalPath.exists
#print axioms CombPhaseTerminalPath.unique

/-! The retained two-process diamond also supplies an explicit terminal path.
This is the scheduler-side bridge used before a global admission structure is
constructed. -/
theorem CombPhaseTerminalPath.two_cursor_terminal
    {E : CoreMemDesign} {s : CombPhaseState}
    {c₁ c₂ n₁ n₂ : CombCursor}
    {x₁ x₂ y₁ y₂ : CoreMemState} {v₁ v₂ w₁ w₂ : SvState}
    (ha : s.active = [c₁, c₂])
    (h₁ : c₁.resume E s.state s.view = .ok (x₁, v₁, n₁))
    (h₂ : c₂.resume E s.state s.view = .ok (x₂, v₂, n₂))
    (h₂₁ : c₂.resume E x₁ v₁ = .ok (y₁, w₁, n₂))
    (h₁₂ : c₁.resume E x₂ v₂ = .ok (y₂, w₂, n₁))
    (hstate : y₁ = y₂) (hview : w₁ = w₂)
    (hn₁ : n₁.work = []) (hn₂ : n₂.work = []) :
    ∃ na ta nb tb,
      CombPhaseTerminalPath E na s ta ∧
      CombPhaseTerminalPath E nb s tb ∧
      ta = { state := y₁, view := w₁, active := [] } ∧
      tb = { state := y₁, view := w₁, active := [] } := by
  let u₁ := CombPhaseState.after s x₁ v₁ n₁ [] [c₂]
  let u₂ := CombPhaseState.after s x₂ v₂ n₂ [c₁] []
  let z := CombPhaseState.after u₁ y₁ w₁ n₂ [] []
  let z₂ := CombPhaseState.after u₂ y₂ w₂ n₁ [] []
  have hs₁ : CombPhaseStep E s u₁ := .select (by simpa [u₁, ha]) h₁
  have hs₂ : CombPhaseStep E s u₂ := .select (by simpa [u₂, ha]) h₂
  have hu₁ : CombPhaseStep E u₁ z := by
    apply CombPhaseStep.select (cursor := c₂) (next := n₂) (state := y₁) (view := w₁)
      (before := []) (after := [])
    · simp [u₁, z, CombPhaseState.after, hn₁]
    · simpa [u₁, CombPhaseState.after] using h₂₁
  have hu₂ : CombPhaseStep E u₂ z₂ := by
    apply CombPhaseStep.select (cursor := c₁) (next := n₁) (state := y₂) (view := w₂)
      (before := []) (after := [])
    · simp [u₂, z₂, CombPhaseState.after, hn₂]
    · simpa [u₂, CombPhaseState.after] using h₁₂
  have hz : z = { state := y₁, view := w₁, active := [] } := by
    simp [z, u₁, CombPhaseState.after, hn₁, hn₂]
  have hz₂ : z₂ = { state := y₁, view := w₁, active := [] } := by
    simp [z₂, u₂, CombPhaseState.after, hn₁, hn₂, hstate, hview]
  have hnonempty : ¬ CombPhaseQuiescent s := by
    simp [CombPhaseQuiescent, ha]
  have hu₁_empty : ¬ CombPhaseQuiescent u₁ := by
    simp [u₁, CombPhaseQuiescent, CombPhaseState.after, hn₁]
  have hu₂_empty : ¬ CombPhaseQuiescent u₂ := by
    simp [u₂, CombPhaseQuiescent, CombPhaseState.after, hn₂]
  have hterm : CombPhaseQuiescent ({ state := y₁, view := w₁, active := [] } : CombPhaseState) := by
    rfl
  have hterm₂ : CombPhaseQuiescent ({ state := y₁, view := w₁, active := [] } : CombPhaseState) := by
    rfl
  refine ⟨2, z, 2, z₂, ?_, ?_, hz, hz₂⟩
  · exact .head hnonempty hs₁
      (.head hu₁_empty hu₁ (.terminal (by rw [hz]; exact hterm)))
  · exact .head hnonempty hs₂
      (.head hu₂_empty hu₂ (.terminal (by rw [hz₂]; exact hterm₂)))

theorem CombPhaseTerminalPath.of_two_step_diamond
    {E : CoreMemDesign} {s u₁ u₂ z : CombPhaseState}
    (h₁ : CombPhaseStep E s u₁)
    (h₂ : CombPhaseStep E s u₂)
    (h₁z : CombPhaseStep E u₁ z)
    (h₂z : CombPhaseStep E u₂ z)
    (hz : z.active = []) :
    CombPhaseTerminalPath E 2 s z ∧ CombPhaseTerminalPath E 2 s z := by
  have hs : ¬ CombPhaseQuiescent s := by
    cases h₁ with
    | select hactive _ =>
        simp [CombPhaseQuiescent, hactive]
  have hu₁ : ¬ CombPhaseQuiescent u₁ := by
    cases h₁z with
    | select hactive _ =>
        simp [CombPhaseQuiescent, hactive]
  have hu₂ : ¬ CombPhaseQuiescent u₂ := by
    cases h₂z with
    | select hactive _ =>
        simp [CombPhaseQuiescent, hactive]
  have hterminal : CombPhaseQuiescent z := by
    simpa [CombPhaseQuiescent] using hz
  exact ⟨.head hs h₁ (.head hu₁ h₁z (.terminal hterminal)),
    .head hs h₂ (.head hu₂ h₂z (.terminal hterminal))⟩

/-! Pure scalar expressions have the evaluator frame needed by the
level-sensitive diamond.  The source access guard still has to establish the
read agreement premise for the instantiated expression.  Keeping this lemma
at the `evalScalarLocals` boundary means the eventual guard proof can use the
parser-native read closure without changing the source-shaped evaluator. -/
theorem CoreMemDesign.evalScalarLocals_congr_view
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st st' : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    (h : ∀ r ∈ (instExpr2 env (if elems.isEmpty then E.elems else elems) ctx e).reads,
      r.agree (locals ++ E.scalar.view st.scalar)
        (locals ++ E.scalar.view st'.scalar)) :
    E.evalScalarLocals env elems st ctx locals e =
      E.evalScalarLocals env elems st' ctx locals e := by
  unfold CoreMemDesign.evalScalarLocals
  exact evalPure2_congr_reads h

#print axioms CoreMemDesign.evalScalarLocals_congr_view

/-! A whole-binding variant matches the parser-native name walkers.  It is
 intentionally conservative about slices, but lets a source read closure be
 connected to the instantiated expression without exposing `Expr2.reads`. -/
theorem CoreMemDesign.evalScalarLocals_congr_idents
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st st' : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    (h : ∀ n ∈ (instExpr2 env (if elems.isEmpty then E.elems else elems) ctx e).idents,
      SvState.lookup (locals ++ E.scalar.view st.scalar) n =
        SvState.lookup (locals ++ E.scalar.view st'.scalar) n) :
    E.evalScalarLocals env elems st ctx locals e =
      E.evalScalarLocals env elems st' ctx locals e := by
  unfold CoreMemDesign.evalScalarLocals
  exact evalPure2_congr h

#print axioms CoreMemDesign.evalScalarLocals_congr_idents

/-! A source-shaped blocking write can be framed at the evaluator boundary
when none of the instantiated read windows names the written signal.  This is
the small semantic bridge needed before the parser-native guard can be used to
derive the cross-resume equality. -/
theorem CoreMemDesign.evalScalarLocals_setScalarState_of_not_read
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    {n : String} {x : VarId} {v : LVec}
    (hx : E.scalar.resolve n = some x)
    (hset : E.scalar.view (E.setScalarState st n v).scalar =
      SvState.set (E.scalar.view st.scalar) n (Val.ofLVec (st.scalar x).ty v).bits)
    (hread : ∀ r ∈ (instExpr2 env (if elems.isEmpty then E.elems else elems) ctx e).reads,
      r.name ≠ n) :
    E.evalScalarLocals env elems st ctx locals e =
      E.evalScalarLocals env elems (E.setScalarState st n v) ctx locals e := by
  unfold CoreMemDesign.evalScalarLocals
  apply evalPure2_congr_reads
  intro r hr
  apply ReadWin.agree_of_lookup
  rw [hset]
  let lookupAppend : ∀ (a b : SvState) (q : String),
      SvState.lookup (a ++ b) q = (SvState.lookup a q).or (SvState.lookup b q) := by
    intro a
    induction a with
    | nil => intro b q; rfl
    | cons kv rest ih =>
        intro b q
        obtain ⟨k, w⟩ := kv
        simp only [List.cons_append, SvState.lookup]
        split
        · rfl
        · simp only [ih]
  rw [lookupAppend, lookupAppend]
  by_cases hlocal : SvState.lookup locals r.name = none
  · simp only [hlocal, Option.none_or]
    rw [SvState.lookup_set_ne _ _ (Ne.symm (hread r hr))]
  · cases hval : SvState.lookup locals r.name with
    | none => exact False.elim (hlocal hval)
    | some lv => simp [hval]

theorem CoreMemDesign.evalScalarLocals_setScalarState_of_not_read_coherent
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    {n : String} {x : VarId} {v : LVec}
    (hc : E.Coherent st) (hx : E.scalar.resolve n = some x)
    (hread : ∀ r ∈ (instExpr2 env (if elems.isEmpty then E.elems else elems) ctx e).reads,
      r.name ≠ n) :
    E.evalScalarLocals env elems st ctx locals e =
      E.evalScalarLocals env elems (E.setScalarState st n v) ctx locals e := by
  apply CoreMemDesign.evalScalarLocals_setScalarState_of_not_read hx
  exact (CoreMemDesign.setScalarState_spec hc hx v).1
  exact hread

theorem SvState.set_commute_of_mem
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

theorem ReadWin.agree_set_two
    {st : SvState} {n m : String} {oldN oldM p q : LVec} {loN wN loM wM : Nat}
    (hn : SvState.lookup st n = some oldN) (hm : SvState.lookup st m = some oldM)
    (hp : p.width = wN) (hq : q.width = wM)
    (hneq : n ≠ m)
    {r : ReadWin}
    (hrN : r.overlaps (n, loN, wN) = false)
    (hrM : r.overlaps (m, loM, wM) = false) :
    r.agree st (SvState.set (SvState.set st n (oldN.insertAt loN p)) m
      (oldM.insertAt loM q)) := by
  apply ReadWin.agree_trans (ReadWin.agree_set hn hp hrN)
  apply ReadWin.agree_set
  · rw [SvState.lookup_set_ne _ _ hneq]
    exact hm
  · exact hq
  · exact hrM

/-! A retained scalar blocking leaf resumes to the exact updated state and
view, leaving the suspended tail untouched. -/
theorem CombCursor.resume_blocking_scalar
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n : String} {value : PExpr} {width : Nat}
    {tail : List CombWork} {v : LVec}
    (hlocal : SvState.lookup locals n = none)
    (htarget : E.scalarTarget n = some width)
    (htest : PExpr.hasTestPlusargs value = false)
    (hvalue : E.evalExprLocals env E.elems st (some width) locals value = .ok v) :
    CombCursor.resume E st view
      { work := .stmt env (.blockingAssign n value) :: tail, locals := locals } =
      .ok (E.setScalarState st n v, SvState.set view n v,
        { work := tail, locals := locals }) := by
  simp [CombCursor.resume, CombWork.openNode, CoreMemDesign.execCombStmtFuel,
    hlocal, htarget, htest, hvalue]

/-! Each scalar expression keeps its value when the other cursor's write is
absent from its instantiated read windows.  The two directions are stated
separately so a later scheduler diamond can use whichever expression it needs. -/
theorem CoreMemDesign.evalScalarLocals_cross_write_frame
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st stN stM : CoreMemState} {ctxN ctxM : Option Nat} {locals : SvState}
    {eN eM : PExpr} {n m : String} {xN xM : VarId} {vN vM : LVec}
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hstateN : stN = E.setScalarState st n vN)
    (hstateM : stM = E.setScalarState st m vM)
    (hsetN : E.scalar.view stN.scalar =
      SvState.set (E.scalar.view st.scalar) n
        (Val.ofLVec (st.scalar xN).ty vN).bits)
    (hsetM : E.scalar.view stM.scalar =
      SvState.set (E.scalar.view st.scalar) m
        (Val.ofLVec (st.scalar xM).ty vM).bits)
    (hreadM : ∀ r ∈ (instExpr2 env (if elems.isEmpty then E.elems else elems) ctxM eM).reads,
      r.name ≠ n)
    (hreadN : ∀ r ∈ (instExpr2 env (if elems.isEmpty then E.elems else elems) ctxN eN).reads,
      r.name ≠ m) :
    E.evalScalarLocals env elems stN ctxM locals eM =
        E.evalScalarLocals env elems st ctxM locals eM ∧
      E.evalScalarLocals env elems stM ctxN locals eN =
        E.evalScalarLocals env elems st ctxN locals eN := by
  have hsetN' : E.scalar.view (E.setScalarState st n vN).scalar =
      SvState.set (E.scalar.view st.scalar) n
        (Val.ofLVec (st.scalar xN).ty vN).bits := by
    simpa [hstateN] using hsetN
  have hsetM' : E.scalar.view (E.setScalarState st m vM).scalar =
      SvState.set (E.scalar.view st.scalar) m
        (Val.ofLVec (st.scalar xM).ty vM).bits := by
    simpa [hstateM] using hsetM
  constructor
  · rw [hstateN]
    exact (CoreMemDesign.evalScalarLocals_setScalarState_of_not_read hxN hsetN' hreadM).symm
  · rw [hstateM]
    exact (CoreMemDesign.evalScalarLocals_setScalarState_of_not_read hxM hsetM' hreadN).symm

/-! Under coherent scalar updates, the two updated views commute when the
converted values at the untouched declarations retain their declared types. -/
theorem CoreMemDesign.scalar_view_commute_of_coherent
    {E : CoreMemDesign} {st : CoreMemState}
    {n m : String} {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hn : n ∈ (E.scalar.view st.scalar).map Prod.fst)
    (hm : m ∈ (E.scalar.view st.scalar).map Prod.fst)
    (hneq : n ≠ m)
    (hkeys : ((E.scalar.view st.scalar).map Prod.fst).Nodup)
    (hcompatM :
      (Val.ofLVec ((E.setScalarState st n vN).scalar xM).ty vM).bits =
        (Val.ofLVec (st.scalar xM).ty vM).bits)
    (hcompatN :
      (Val.ofLVec ((E.setScalarState st m vM).scalar xN).ty vN).bits =
        (Val.ofLVec (st.scalar xN).ty vN).bits) :
    E.scalar.view (E.setScalarState (E.setScalarState st n vN) m vM).scalar =
      E.scalar.view (E.setScalarState (E.setScalarState st m vM) n vN).scalar := by
  have hspecN := CoreMemDesign.setScalarState_spec hc hxN vN
  have hspecM := CoreMemDesign.setScalarState_spec hc hxM vM
  have hspecNM := CoreMemDesign.setScalarState_spec hspecN.2 hxM vM
  have hspecMN := CoreMemDesign.setScalarState_spec hspecM.2 hxN vN
  rw [hspecNM.1, hspecMN.1, hspecN.1, hspecM.1, hcompatM, hcompatN]
  exact SvState.set_commute_of_mem hn hm hneq hkeys

/-! The retained blocking scalar leaf is source-shaped at the resume boundary.
This equation exposes its exact evaluator input and state/view update. -/
theorem CombWork.openNode_blockingAssign_scalar
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n : String} {value : PExpr} {width : Nat}
    (hlocal : SvState.lookup locals n = none)
    (htarget : E.scalarTarget n = some width)
    (htest : PExpr.hasTestPlusargs value = false) :
    CombWork.openNode E st view locals
        (.stmt env (.blockingAssign n value)) =
      (do
        let v ← E.evalExprLocals env E.elems st (some width) locals value
        .ok ((E.setScalarState st n v, SvState.set view n v, locals), [])) := by
  simp only [CombWork.openNode, CoreMemDesign.execCombStmtFuel, hlocal, htarget, htest]
  cases h : E.evalExprLocals env E.elems st (some width) locals value <;> simp [h]

/-! Two scalar blocking leaves compose through the real statement executor.
The second expression is evaluated in the state and view produced by the first
leaf, matching the retained-process cut used by `CombCursor.resume`. -/
theorem CoreMemDesign.execCombStmtsFuel_two_blocking_scalar
    {E : CoreMemDesign} {env : IEnv} {st : CoreMemState} {view locals : SvState}
    {n m : String} {e₁ e₂ : PExpr} {widthN widthM : Nat} {v₁ v₂ : LVec}
    (hlocalN : SvState.lookup locals n = none)
    (hlocalM : SvState.lookup locals m = none)
    (htargetN : E.scalarTarget n = some widthN)
    (htargetM : E.scalarTarget m = some widthM)
    (htestN : PExpr.hasTestPlusargs e₁ = false)
    (htestM : PExpr.hasTestPlusargs e₂ = false)
    (hv₁ : E.evalExprLocals env E.elems st (some widthN) locals e₁ = .ok v₁)
    (hv₂ : E.evalExprLocals env E.elems (E.setScalarState st n v₁)
      (some widthM) locals e₂ = .ok v₂) :
    E.execCombStmtsFuel env E.elems st view locals 3
      [.blockingAssign n e₁, .blockingAssign m e₂] =
      .ok (E.setScalarState (E.setScalarState st n v₁) m v₂,
        SvState.set (SvState.set view n v₁) m v₂, locals) := by
  simp [CoreMemDesign.execCombStmtsFuel, CoreMemDesign.execCombStmtFuel,
    hlocalN, htargetN, htestN, hv₁, hlocalM, htargetM, htestM, hv₂]

/-! Composing the single-write evaluator frame gives the exact two-write
frame needed by a cross-resume proof.  The two view equations are explicit so
this theorem does not hide any scheduler or coherence assumption. -/
theorem CoreMemDesign.evalScalarLocals_setScalarState_two_of_not_read
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st st₁ st₂ : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    {n m : String} {xN xM : VarId} {vN vM : LVec}
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hstateN : st₁ = E.setScalarState st n vN)
    (hstateM : st₂ = E.setScalarState st₁ m vM)
    (hsetN : E.scalar.view st₁.scalar =
      SvState.set (E.scalar.view st.scalar) n
        (Val.ofLVec (st.scalar xN).ty vN).bits)
    (hsetM : E.scalar.view st₂.scalar =
      SvState.set (E.scalar.view st₁.scalar) m
        (Val.ofLVec (st₁.scalar xM).ty vM).bits)
    (hreadN : ∀ r ∈ (instExpr2 env (if elems.isEmpty then E.elems else elems) ctx e).reads,
      r.name ≠ n)
    (hreadM : ∀ r ∈ (instExpr2 env (if elems.isEmpty then E.elems else elems) ctx e).reads,
      r.name ≠ m) :
    E.evalScalarLocals env elems st ctx locals e =
      E.evalScalarLocals env elems st₂ ctx locals e := by
  have hsetN' : E.scalar.view (E.setScalarState st n vN).scalar =
      SvState.set (E.scalar.view st.scalar) n
        (Val.ofLVec (st.scalar xN).ty vN).bits := by
    simpa [hstateN] using hsetN
  have hsetM' : E.scalar.view (E.setScalarState st₁ m vM).scalar =
      SvState.set (E.scalar.view st₁.scalar) m
        (Val.ofLVec (st₁.scalar xM).ty vM).bits := by
    simpa [hstateM] using hsetM
  calc
    E.evalScalarLocals env elems st ctx locals e =
        E.evalScalarLocals env elems (E.setScalarState st n vN) ctx locals e :=
      CoreMemDesign.evalScalarLocals_setScalarState_of_not_read hxN hsetN' hreadN
    _ = E.evalScalarLocals env elems st₁ ctx locals e := by rw [hstateN]
    _ = E.evalScalarLocals env elems (E.setScalarState st₁ m vM) ctx locals e :=
      CoreMemDesign.evalScalarLocals_setScalarState_of_not_read hxM hsetM' hreadM
    _ = E.evalScalarLocals env elems st₂ ctx locals e := by rw [hstateM]

/-! The four source-level obligations for a level-sensitive admission.  They
are retained as a proposition over `PDesign`, where the access closure and
reactive dependency walks still have their parser-native inputs.  The first
field is the IEEE 1800-2023 §4.7 blocking read/write check after continuous
driver closure.  The synthesis reading is the corresponding IEEE 1364.1-2002
§5.2.2 and Annex B.1 race boundary. -/
structure CombPhaseGuard (d : PDesign) : Prop where
  no_blocking_read_after_closure :
    coreMemEdgeBlockingReadRaceThroughAssign d.processes = false
  no_multiple_writers :
    coreMemEdgeMultipleWriteThroughAssign d.processes = false
  comb_acyclic :
    coreMemReactiveDependencyViol d.processes = none ∧
      coreMemAssignReactiveChainViol d.processes = none
  no_self_read :
    coreMemCombSelfReadViol d.processes = none ∧
      coreMemLatchSelfReadViol d.processes = none

#print axioms CombPhaseGuard

/-! The parser guard is defined over the complete process list, while a local
    resume diamond consumes a pair of source processes.  For the two-process
    source-shaped boundary, unfold the guard once and expose both directed
    exclusions.  The closure remains the parser's transitive
    `coreMemReadNamesThroughDrivers` set, so this theorem does not replace the
    real evaluator frame with a syntactic approximation. -/
theorem coreMemEdgeBlockingReadRacePairThroughAssign_false_of_two
    {p q : PProcess}
    (hguard : coreMemEdgeBlockingReadRaceThroughAssign [p, q] = false)
    (hcommon : coreMemHasCommonEventSourceThroughAssign [p, q] p q = true) :
    (∀ x, x ∈ coreMemProcBlockingWrites p →
      x ∉ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames q)) ∧
    (∀ x, x ∈ coreMemProcBlockingWrites q →
      x ∉ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames p)) := by
  simpa [coreMemEdgeBlockingReadRaceThroughAssign,
    coreMemEdgeBlockingReadRaceThroughAssignFrom,
    coreMemEdgeBlockingReadRaceAtThroughAssign,
    coreMemEdgeBlockingReadRacePairThroughAssign, hcommon] using hguard

#print axioms coreMemEdgeBlockingReadRacePairThroughAssign_false_of_two

/-! The public guard is attached to the complete parser design.  This adapter
specializes its exact parser-native race field to a two-process source slice,
so a retained evaluator proof can consume the guard without restating the
boolean refusal predicate. -/
theorem CombPhaseGuard.two_process_read_write_exclusions
    {d : PDesign} {p q : PProcess}
    (hg : CombPhaseGuard d)
    (hprocesses : d.processes = [p, q])
    (hcommon : coreMemHasCommonEventSourceThroughAssign [p, q] p q = true) :
    (∀ x, x ∈ coreMemProcBlockingWrites p →
      x ∉ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames q)) ∧
    (∀ x, x ∈ coreMemProcBlockingWrites q →
      x ∉ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames p)) := by
  apply coreMemEdgeBlockingReadRacePairThroughAssign_false_of_two
  · simpa [hprocesses] using hg.no_blocking_read_after_closure
  · exact hcommon

#print axioms CombPhaseGuard.two_process_read_write_exclusions

end LeanModels.Sv.Kernel

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

/-- The real edge-phase commit is definitionally the executor's canonical
`committedState`, including its memory NBA result. -/
theorem EdgePhaseState.commit_eq_committedState
    {E : CoreMemDesign} {s : EdgePhaseState} {m : MemState}
    (hm : s.state.memory.commitNba s.memoryQ = some m) :
    s.commit E = .ok (E.committedState
      { state := s.state, scalarQ := s.scalarQ, memoryQ := s.memoryQ, locals := [] } m) := by
  unfold EdgePhaseState.commit CoreMemDesign.committedState
  simp [hm]
  cases s.state
  rfl

#print axioms EdgePhaseState.commit_eq_committedState

/-- Once the surrounding pre-edge and post-edge settle receipts are available,
the source-shaped edge-phase commit enters the same `CoreMemDesign.step`
refinement used by the canonical executor. -/
theorem CoreMemDesign.edge_phase_commit_refines_step
    {E : CoreMemDesign} {st : CoreMemState} {entry : SvState}
    (hcomb : E.hasComb = false) (himp : E.hasImplicit = false)
    {pre0 pre s3 next : CoreMemState} {edge : CoreMemExecResult} {m : MemState}
    (h0 : E.settleCanonical E.env E.elems (E.inputState st entry) E.processes.toList = .ok pre0)
    (h1 : E.settleCanonical E.env E.elems pre0 E.processes.toList = .ok pre)
    (he : E.runEdges E.env E.elems pre (E.scalar.view st.scalar)
      (E.scalar.view pre.scalar) E.processes.toList = .ok edge)
    (hm : edge.state.memory.commitNba edge.memoryQ = some m)
    (h3 : E.settleCanonical E.env E.elems (E.committedState edge m) E.processes.toList = .ok s3)
    (h4 : E.settleCanonical E.env E.elems s3 E.processes.toList = .ok next)
    (hq : E.firesAny (E.scalar.view pre.scalar) (E.scalar.view next.scalar) = false) :
    E.step st entry = .ok next := by
  exact CoreMemDesign.step_of_onePass hcomb himp h0 h1 he hm h3 h4 hq

#print axioms CoreMemDesign.edge_phase_commit_refines_step

end LeanModels.Sv.Kernel

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

/-- Admission facts for the source-shaped edge phase when every active cursor is
one stable scalar-NBA action.  The facts are stated on `EdgePhaseStep`'s own
cursor and result types, so no source order is selected. -/
structure EdgePhaseNbaAdmission (E : CoreMemDesign) (s : EdgePhaseState) where
  resume_ok : ∀ cursor, cursor ∈ s.active →
    ∃ result next, cursor.resume E s.state = .ok (result, next)
  continuation_empty : ∀ cursor result next, cursor ∈ s.active →
    cursor.resume E s.state = .ok (result, next) → next.work = []
  stable_state : ∀ cursor result next, cursor ∈ s.active →
    cursor.resume E s.state = .ok (result, next) → result.state = s.state
  no_memory_nba : ∀ cursor result next, cursor ∈ s.active →
    cursor.resume E s.state = .ok (result, next) → result.memoryQ = []

/-! The memory-aware admission keeps the same stable-state and
continuation obligations but records the issue-time memory queue instead of
requiring it to be empty.  The scalar admission above remains the narrow
scalar-only profile. -/
structure EdgePhaseMemoryAdmission (E : CoreMemDesign) (s : EdgePhaseState) where
  resume_ok : ∀ cursor, cursor ∈ s.active →
    ∃ result next, cursor.resume E s.state = .ok (result, next)
  continuation_empty : ∀ cursor result next, cursor ∈ s.active →
    cursor.resume E s.state = .ok (result, next) → next.work = []
  stable_state : ∀ cursor result next, cursor ∈ s.active →
    cursor.resume E s.state = .ok (result, next) → result.state = s.state

/-- Every legal source-shaped edge step in the admitted NBA-only class reduces
the active-cursor measure. -/
theorem EdgePhaseStep.nba_measure_decreases
    {E : CoreMemDesign} {s t : EdgePhaseState}
    (ad : EdgePhaseNbaAdmission E s)
    (h : EdgePhaseStep E s t) :
    t.active.length < s.active.length := by
  cases h with
  | select hactive hresume =>
      rename_i before after cursor next result
      have hmem : cursor ∈ s.active := by
        rw [hactive]
        simp
      have hempty := ad.continuation_empty cursor result next hmem hresume
      rw [hactive]
      simp [EdgePhaseState.after, hempty]

/-- A nonempty admitted NBA-only edge phase always has a legal next step. -/
theorem EdgePhaseStep.nba_progress
    {E : CoreMemDesign} {s : EdgePhaseState}
    (ad : EdgePhaseNbaAdmission E s) (hn : s.active ≠ []) :
    ∃ t, EdgePhaseStep E s t := by
  obtain ⟨t, h⟩ := EdgePhaseStep.progress hn (ad.resume_ok)
  exact ⟨t, h⟩

#print axioms EdgePhaseStep.nba_measure_decreases
#print axioms EdgePhaseStep.nba_progress


end LeanModels.Sv.Kernel

namespace LeanModels.Sv.Scheduler

/-- A concrete two-process NBA-only scheduler witness.  Both source-shaped
processes issue one disjoint scalar NBA, then terminate.  `allSlotOutcomes`
therefore explores both legal §4.7 active-event orders and the common NBA
commit. -/
def twoNbaWitness : SchedulerDesign :=
  { eval := fun p resume _ =>
      match p, resume with
      | 0, 0 => .nonblocking 0 "a" (.lit "0") 1
      | 1, 0 => .nonblocking 0 "b" (.lit "1") 1
      | _, _ => .done
    initial :=
      { store := [("a", .lit "x"), ("b", .lit "x")]
        active := [.eval 0 0, .eval 1 0] }
    admitted := true }

private def twoNbaExpected : SvState :=
  [("a", .lit "0"), ("b", .lit "1")]

#guard (allSlotOutcomes 16 twoNbaWitness twoNbaWitness.initial).all
  (fun o => o == .value twoNbaExpected)

theorem twoNbaWitness_all_orders :
    (allSlotOutcomes 16 twoNbaWitness twoNbaWitness.initial).all
      (fun o => o == .value twoNbaExpected) = true := by
  decide

theorem twoNbaWitness_outcomes :
    allSlotOutcomes 16 twoNbaWitness twoNbaWitness.initial =
      List.replicate 12 (.value twoNbaExpected) := by
  decide

#print axioms twoNbaWitness_all_orders
#print axioms twoNbaWitness_outcomes

end LeanModels.Sv.Scheduler

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

inductive EdgePhaseTerminalPath (E : CoreMemDesign) :
    Nat → EdgePhaseState → EdgePhaseState → Prop where
  | terminal {s} (h : EdgePhaseQuiescent s) :
      EdgePhaseTerminalPath E 0 s s
  | head {n s u t} (hn : ¬ EdgePhaseQuiescent s)
      (hstep : EdgePhaseStep E s u)
      (htail : EdgePhaseTerminalPath E n u t) :
      EdgePhaseTerminalPath E (n + 1) s t

private theorem EdgePhaseNbaAdmission.restrict
    {E : CoreMemDesign} {s s' : EdgePhaseState}
    (ad : EdgePhaseNbaAdmission E s)
    (hstate : s'.state = s.state)
    (hsub : ∀ cursor, cursor ∈ s'.active → cursor ∈ s.active) :
    EdgePhaseNbaAdmission E s' := by
  constructor
  · intro cursor hmem
    obtain ⟨result, next, hresume⟩ := ad.resume_ok cursor (hsub cursor hmem)
    exact ⟨result, next, by simpa [hstate] using hresume⟩
  · intro cursor result next hmem hresume
    apply ad.continuation_empty cursor result next (hsub cursor hmem)
    simpa [hstate] using hresume
  · intro cursor result next hmem hresume
    have hs := ad.stable_state cursor result next (hsub cursor hmem)
      (by simpa [hstate] using hresume)
    exact hs.trans hstate.symm
  · intro cursor result next hmem hresume
    apply ad.no_memory_nba cursor result next (hsub cursor hmem)
    simpa [hstate] using hresume

private theorem EdgePhaseMemoryAdmission.restrict
    {E : CoreMemDesign} {s s' : EdgePhaseState}
    (ad : EdgePhaseMemoryAdmission E s)
    (hstate : s'.state = s.state)
    (hsub : ∀ cursor, cursor ∈ s'.active → cursor ∈ s.active) :
    EdgePhaseMemoryAdmission E s' := by
  constructor
  · intro cursor hmem
    obtain ⟨result, next, hresume⟩ := ad.resume_ok cursor (hsub cursor hmem)
    exact ⟨result, next, by simpa [hstate] using hresume⟩
  · intro cursor result next hmem hresume
    apply ad.continuation_empty cursor result next (hsub cursor hmem)
    simpa [hstate] using hresume
  · intro cursor result next hmem hresume
    have hs := ad.stable_state cursor result next (hsub cursor hmem)
      (by simpa [hstate] using hresume)
    exact hs.trans hstate.symm

private theorem EdgePhaseStep.nba_length_succ
    {E : CoreMemDesign} {s t : EdgePhaseState}
    (ad : EdgePhaseNbaAdmission E s)
    (h : EdgePhaseStep E s t) :
    t.active.length + 1 = s.active.length := by
  cases h with
  | select hactive hresume =>
      rename_i before after cursor next result
      have hmem : cursor ∈ s.active := by
        rw [hactive]
        simp
      have hempty := ad.continuation_empty cursor result next hmem hresume
      rw [hactive]
      simp [EdgePhaseState.after, hempty]
      omega

/-- Along any admitted NBA-only terminal path, the number of selected active
cursors plus the remaining active length equals the initial active length. -/
theorem EdgePhaseTerminalPath.nba_length_balance
    {E : CoreMemDesign} {s t : EdgePhaseState} {n : Nat}
    (ad : EdgePhaseNbaAdmission E s)
    (hp : EdgePhaseTerminalPath E n s t) :
    n + t.active.length = s.active.length := by
  induction hp with
  | terminal hterm => simp [EdgePhaseQuiescent] at hterm; simp [hterm]
  | @head n s u t hn hstep htail ih =>
      cases hstep with
      | select hactive hresume =>
          rename_i before after cursor next result
          have hmem : cursor ∈ s.active := by
            rw [hactive]
            simp
          have hempty := ad.continuation_empty cursor result next hmem hresume
          have hstable := ad.stable_state cursor result next hmem hresume
          let u' : EdgePhaseState := s.after result next before after
          have hstate : u'.state = s.state := by
            simp [u', EdgePhaseState.after, hstable]
          have hsub : ∀ c, c ∈ u'.active → c ∈ s.active := by
            intro c hc
            have hc' : c ∈ before ++ after := by
              simpa [u', EdgePhaseState.after, hempty] using hc
            rw [hactive]
            rcases List.mem_append.mp hc' with hb | ha
            · exact List.mem_append_left _ hb
            · exact List.mem_append_right before (List.mem_cons_of_mem cursor ha)
          have huad : EdgePhaseNbaAdmission E u' :=
            ad.restrict hstate hsub
          have hbal : n + t.active.length = u'.active.length := by
            simpa [u'] using ih huad
          have hstep' : EdgePhaseStep E s u' := by
            exact .select hactive hresume
          have hlen := EdgePhaseStep.nba_length_succ ad hstep'
          omega

#print axioms EdgePhaseStep.nba_length_succ
#print axioms EdgePhaseTerminalPath.nba_length_balance

private theorem EdgePhaseTerminalPath.state_eq
    {E : CoreMemDesign} {s t : EdgePhaseState} {n : Nat}
    (ad : EdgePhaseNbaAdmission E s)
    (hp : EdgePhaseTerminalPath E n s t) :
    t.state = s.state := by
  induction hp with
  | terminal hterm => rfl
  | @head n s u t hn hstep htail ih =>
      cases hstep with
      | select hactive hresume =>
          rename_i before after cursor next result
          have hmem : cursor ∈ s.active := by
            rw [hactive]
            simp
          have hempty := ad.continuation_empty cursor result next hmem hresume
          have hstable := ad.stable_state cursor result next hmem hresume
          let u' : EdgePhaseState := s.after result next before after
          have hstate : u'.state = s.state := by
            simp [u', EdgePhaseState.after, hstable]
          have hsub : ∀ c, c ∈ u'.active → c ∈ s.active := by
            intro c hc
            have hc' : c ∈ before ++ after := by
              simpa [u', EdgePhaseState.after, hempty] using hc
            rw [hactive]
            rcases List.mem_append.mp hc' with hb | ha
            · exact List.mem_append_left _ hb
            · exact List.mem_append_right before (List.mem_cons_of_mem cursor ha)
          have huad : EdgePhaseNbaAdmission E u' :=
            ad.restrict hstate hsub
          have htailstate : t.state = u'.state := ih huad
          exact htailstate.trans hstate

#print axioms EdgePhaseTerminalPath.state_eq

/-- The canonical one-pass executor can consume an actual terminal edge-phase
state.  The path invariant supplies the pre-edge state equality, while the
run, commit, and settle receipts remain explicit obligations of the exact E
semantics. -/
theorem EdgePhaseTerminalPath.executor_result
    {E : CoreMemDesign} {s t : EdgePhaseState} {n : Nat}
    (ad : EdgePhaseNbaAdmission E s)
    (hp : EdgePhaseTerminalPath E n s t)
    (hcomb : E.hasComb = false) (himp : E.hasImplicit = false)
    {st : CoreMemState} {entry : SvState}
    {pre0 s3 next : CoreMemState} {m : MemState}
    (h0 : E.settleCanonical E.env E.elems (E.inputState st entry) E.processes.toList = .ok pre0)
    (h1 : E.settleCanonical E.env E.elems pre0 E.processes.toList = .ok s.state)
    (he : E.runEdges E.env E.elems t.state
      (E.scalar.view st.scalar) (E.scalar.view t.state.scalar) E.processes.toList =
      .ok { state := t.state, scalarQ := t.scalarQ, memoryQ := t.memoryQ, locals := [] })
    (hm : t.state.memory.commitNba t.memoryQ = some m)
    (h3 : E.settleCanonical E.env E.elems
      (E.committedState
        { state := t.state, scalarQ := t.scalarQ, memoryQ := t.memoryQ, locals := [] } m) E.processes.toList =
      .ok s3)
    (h4 : E.settleCanonical E.env E.elems s3 E.processes.toList = .ok next)
    (hq : E.firesAny (E.scalar.view s.state.scalar) (E.scalar.view next.scalar) = false) :
    E.step st entry = .ok next := by
  have hstate := EdgePhaseTerminalPath.state_eq ad hp
  rw [hstate] at he hm h3
  exact CoreMemDesign.edge_phase_commit_refines_step
    (pre := s.state)
    (edge := { state := s.state, scalarQ := t.scalarQ, memoryQ := t.memoryQ, locals := [] })
    hcomb himp h0 h1 he hm h3 h4 hq

#print axioms EdgePhaseTerminalPath.executor_result

private theorem perm_cons_append_insert {α : Type} (x : α) :
    ∀ (before after : List α),
      (x :: (before ++ after)).Perm (before ++ x :: after)
  | [], _ => List.Perm.refl _
  | b :: before, after => by
      simp only [List.cons_append]
      exact (List.Perm.swap b x (before ++ after)).trans
        (List.Perm.cons b (perm_cons_append_insert x before after))

/-! A path records each selected cursor exactly once.  The queue function is
explicitly supplied because the admission theorem is the scheduler-side
obligation that a cursor's stable NBA result is independent of the path. -/
theorem EdgePhaseTerminalPath.scalar_queue_trace
    {E : CoreMemDesign} {s t : EdgePhaseState} {n : Nat}
    (ad : EdgePhaseNbaAdmission E s)
    (q : EdgeCursor → NbaQueue2)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.scalarQ = q cursor)
    (hp : EdgePhaseTerminalPath E n s t) :
    ∃ choices : List EdgeCursor, choices.Perm s.active ∧
      t.scalarQ = s.scalarQ ++ List.flatMap q choices := by
  induction hp with
  | @terminal s0 hterm =>
      have hactive : s0.active = [] := by simpa [EdgePhaseQuiescent] using hterm
      refine ⟨[], ?_, ?_⟩
      · rw [hactive]
      · simp [List.flatMap]
  | @head n s u t hn hstep htail ih =>
      cases hstep with
      | select hactive hresume =>
          rename_i before after cursor next result
          have hmem : cursor ∈ s.active := by
            rw [hactive]
            simp
          have hempty := ad.continuation_empty cursor result next hmem hresume
          have hstable := ad.stable_state cursor result next hmem hresume
          have hqcur := hqueue cursor result next hmem hresume
          let u' : EdgePhaseState := s.after result next before after
          have hstate : u'.state = s.state := by
            simp [u', EdgePhaseState.after, hstable]
          have hsub : ∀ c, c ∈ u'.active → c ∈ s.active := by
            intro c hc
            have hc' : c ∈ before ++ after := by
              simpa [u', EdgePhaseState.after, hempty] using hc
            rw [hactive]
            rcases List.mem_append.mp hc' with hb | ha
            · exact List.mem_append_left _ hb
            · exact List.mem_append_right before (List.mem_cons_of_mem cursor ha)
          have huad : EdgePhaseNbaAdmission E u' :=
            ad.restrict hstate hsub
          have hqueue' : ∀ c result' next', c ∈ u'.active →
              c.resume E u'.state = .ok (result', next') →
              result'.scalarQ = q c := by
            intro c result' next' hc hresume'
            apply hqueue c result' next' (hsub c hc)
            simpa [hstate] using hresume'
          obtain ⟨choices, hchoices, htrace⟩ := ih huad hqueue'
          refine ⟨cursor :: choices, ?_, ?_⟩
          · have hperm := List.Perm.cons cursor hchoices
            exact hperm.trans (by
              simpa [u', EdgePhaseState.after, hempty, hactive] using
                (perm_cons_append_insert cursor before after))
          · simpa [u', EdgePhaseState.after, hempty, hqcur,
              List.flatMap, List.append_assoc] using htrace

#print axioms EdgePhaseTerminalPath.scalar_queue_trace

theorem EdgePhaseTerminalPath.scalar_queue_perm
    {E : CoreMemDesign} {s t₁ t₂ : EdgePhaseState}
    {n₁ n₂ : Nat}
    (ad : EdgePhaseNbaAdmission E s)
    (q : EdgeCursor → NbaQueue2)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.scalarQ = q cursor)
    (hp₁ : EdgePhaseTerminalPath E n₁ s t₁)
    (hp₂ : EdgePhaseTerminalPath E n₂ s t₂) :
    t₁.scalarQ.Perm t₂.scalarQ := by
  obtain ⟨choices₁, hchoices₁, htrace₁⟩ :=
    EdgePhaseTerminalPath.scalar_queue_trace ad q hqueue hp₁
  obtain ⟨choices₂, hchoices₂, htrace₂⟩ :=
    EdgePhaseTerminalPath.scalar_queue_trace ad q hqueue hp₂
  have hchoices : choices₁.Perm choices₂ := hchoices₁.trans hchoices₂.symm
  have hflat : (List.flatMap q choices₁).Perm (List.flatMap q choices₂) :=
    List.Perm.flatMap_right q hchoices
  rw [htrace₁, htrace₂]
  exact hflat.append_left _

#print axioms EdgePhaseTerminalPath.scalar_queue_perm

/-! The memory queue has the same path-trace shape, but its records retain
canonical declaration identity.  This theorem is the terminal-observation
adapter's structural half.  It does not yet identify two canonical queues
after `MemState.commitNba`, whose success and identity preservation remain
separate receipts. -/
theorem EdgePhaseTerminalPath.memory_queue_trace
    {E : CoreMemDesign} {s t : EdgePhaseState} {n : Nat}
    (ad : EdgePhaseMemoryAdmission E s)
    (q : EdgeCursor → MemNbaQueue)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.memoryQ = q cursor)
    (hp : EdgePhaseTerminalPath E n s t) :
    ∃ choices : List EdgeCursor, choices.Perm s.active ∧
      t.memoryQ = s.memoryQ ++ List.flatMap q choices := by
  induction hp with
  | @terminal s0 hterm =>
      have hactive : s0.active = [] := by simpa [EdgePhaseQuiescent] using hterm
      refine ⟨[], ?_, ?_⟩
      · rw [hactive]
      · simp [List.flatMap]
  | @head n s u t hn hstep htail ih =>
      cases hstep with
      | select hactive hresume =>
          rename_i before after cursor next result
          have hmem : cursor ∈ s.active := by
            rw [hactive]
            simp
          have hempty := ad.continuation_empty cursor result next hmem hresume
          have hstable := ad.stable_state cursor result next hmem hresume
          have hqcur := hqueue cursor result next hmem hresume
          let u' : EdgePhaseState := s.after result next before after
          have hstate : u'.state = s.state := by
            simp [u', EdgePhaseState.after, hstable]
          have hsub : ∀ c, c ∈ u'.active → c ∈ s.active := by
            intro c hc
            have hc' : c ∈ before ++ after := by
              simpa [u', EdgePhaseState.after, hempty] using hc
            rw [hactive]
            rcases List.mem_append.mp hc' with hb | ha
            · exact List.mem_append_left _ hb
            · exact List.mem_append_right before (List.mem_cons_of_mem cursor ha)
          have huad : EdgePhaseMemoryAdmission E u' :=
            ad.restrict hstate hsub
          have hqueue' : ∀ c result' next', c ∈ u'.active →
              c.resume E u'.state = .ok (result', next') → result'.memoryQ = q c := by
            intro c result' next' hc hresume'
            apply hqueue c result' next' (hsub c hc)
            simpa [hstate] using hresume'
          obtain ⟨choices, hchoices, htrace⟩ := ih huad hqueue'
          refine ⟨cursor :: choices, ?_, ?_⟩
          · have hperm := List.Perm.cons cursor hchoices
            exact hperm.trans (by
              simpa [u', EdgePhaseState.after, hempty, hactive] using
                (perm_cons_append_insert cursor before after))
          · simpa [u', EdgePhaseState.after, hempty, hqcur,
              List.flatMap, List.append_assoc] using htrace

theorem EdgePhaseTerminalPath.memory_queue_perm
    {E : CoreMemDesign} {s t₁ t₂ : EdgePhaseState}
    {n₁ n₂ : Nat}
    (ad : EdgePhaseMemoryAdmission E s)
    (q : EdgeCursor → MemNbaQueue)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.memoryQ = q cursor)
    (hp₁ : EdgePhaseTerminalPath E n₁ s t₁)
    (hp₂ : EdgePhaseTerminalPath E n₂ s t₂) :
    t₁.memoryQ.Perm t₂.memoryQ := by
  obtain ⟨choices₁, hchoices₁, htrace₁⟩ :=
    EdgePhaseTerminalPath.memory_queue_trace ad q hqueue hp₁
  obtain ⟨choices₂, hchoices₂, htrace₂⟩ :=
    EdgePhaseTerminalPath.memory_queue_trace ad q hqueue hp₂
  have hchoices : choices₁.Perm choices₂ := hchoices₁.trans hchoices₂.symm
  have hflat : (List.flatMap q choices₁).Perm (List.flatMap q choices₂) :=
    List.Perm.flatMap_right q hchoices
  rw [htrace₁, htrace₂]
  exact hflat.append_left _

#print axioms EdgePhaseTerminalPath.memory_queue_trace
#print axioms EdgePhaseTerminalPath.memory_queue_perm

/-! The memory-aware admission also preserves the pre-edge state along a
terminal path.  This is separate from queue observation because the canonical
commit still needs its own identity and success receipts. -/
theorem EdgePhaseTerminalPath.memory_state_eq
    {E : CoreMemDesign} {s t : EdgePhaseState} {n : Nat}
    (ad : EdgePhaseMemoryAdmission E s)
    (hp : EdgePhaseTerminalPath E n s t) :
    t.state = s.state := by
  induction hp with
  | terminal hterm => rfl
  | @head n s u t hn hstep htail ih =>
      cases hstep with
      | select hactive hresume =>
          rename_i before after cursor next result
          have hmem : cursor ∈ s.active := by
            rw [hactive]
            simp
          have hempty := ad.continuation_empty cursor result next hmem hresume
          have hstable := ad.stable_state cursor result next hmem hresume
          let u' : EdgePhaseState := s.after result next before after
          have hstate : u'.state = s.state := by
            simp [u', EdgePhaseState.after, hstable]
          have hsub : ∀ c, c ∈ u'.active → c ∈ s.active := by
            intro c hc
            have hc' : c ∈ before ++ after := by
              simpa [u', EdgePhaseState.after, hempty] using hc
            rw [hactive]
            rcases List.mem_append.mp hc' with hb | ha
            · exact List.mem_append_left _ hb
            · exact List.mem_append_right before (List.mem_cons_of_mem cursor ha)
          have huad : EdgePhaseMemoryAdmission E u' :=
            ad.restrict hstate hsub
          have htailstate : t.state = u'.state := ih huad
          exact htailstate.trans hstate

#print axioms EdgePhaseTerminalPath.memory_state_eq

/-! The same executor bridge for memory-aware admission uses the memory
terminal-state invariant instead of the scalar-only admission.  All exact E
settle, edge-run, canonical commit, and post-settle receipts stay visible. -/
theorem EdgePhaseTerminalPath.executor_result_memory
    {E : CoreMemDesign} {s t : EdgePhaseState} {n : Nat}
    (ad : EdgePhaseMemoryAdmission E s)
    (hp : EdgePhaseTerminalPath E n s t)
    (hcomb : E.hasComb = false) (himp : E.hasImplicit = false)
    {st : CoreMemState} {entry : SvState}
    {pre0 s3 next : CoreMemState} {m : MemState}
    (h0 : E.settleCanonical E.env E.elems (E.inputState st entry) E.processes.toList = .ok pre0)
    (h1 : E.settleCanonical E.env E.elems pre0 E.processes.toList = .ok s.state)
    (he : E.runEdges E.env E.elems t.state
      (E.scalar.view st.scalar) (E.scalar.view t.state.scalar) E.processes.toList =
      .ok { state := t.state, scalarQ := t.scalarQ, memoryQ := t.memoryQ, locals := [] })
    (hm : t.state.memory.commitNba t.memoryQ = some m)
    (h3 : E.settleCanonical E.env E.elems
      (E.committedState
        { state := t.state, scalarQ := t.scalarQ, memoryQ := t.memoryQ, locals := [] } m) E.processes.toList =
      .ok s3)
    (h4 : E.settleCanonical E.env E.elems s3 E.processes.toList = .ok next)
    (hq : E.firesAny (E.scalar.view s.state.scalar) (E.scalar.view next.scalar) = false) :
    E.step st entry = .ok next := by
  have hstate := EdgePhaseTerminalPath.memory_state_eq ad hp
  rw [hstate] at he hm h3
  exact CoreMemDesign.edge_phase_commit_refines_step
    (pre := s.state)
    (edge := { state := s.state, scalarQ := t.scalarQ, memoryQ := t.memoryQ, locals := [] })
    hcomb himp h0 h1 he hm h3 h4 hq

#print axioms EdgePhaseTerminalPath.executor_result_memory

end LeanModels.Sv.Kernel

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

private theorem nbaDisj_symm {u v : String × Nat × LVec} :
    NbaDisj u v → NbaDisj v u := by
  intro h
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

private def queuePairwiseDisjoint (q : NbaQueue2) : Prop :=
  q.Pairwise NbaDisj

private theorem memNbaNameDisj_symm {u v : String × Int × LVec} :
    u.1 ≠ v.1 → v.1 ≠ u.1 := by
  exact Ne.symm

private def memQueuePairwiseDisjoint (q : MemQV) : Prop :=
  q.Pairwise (fun u v => u.1 ≠ v.1)

private theorem memQueuePairwiseDisjoint_perm {q q' : MemQV} :
    q.Perm q' → memQueuePairwiseDisjoint q → memQueuePairwiseDisjoint q'
  | hp, h =>
      (List.Perm.pairwise_iff memNbaNameDisj_symm hp).mp h

private theorem commitMemV_perm_disjoint
    {mv : MemV} {q q' : MemQV}
    (hdisj : memQueuePairwiseDisjoint q)
    (hperm : q.Perm q') :
    commitMemV mv q = commitMemV mv q' := by
  induction hperm generalizing mv with
  | nil => rfl
  | cons x hperm ih =>
      rw [commitMemV_cons, commitMemV_cons]
      exact ih (List.pairwise_cons.mp hdisj).2
  | swap x y l =>
      have hpref : commitMemV mv (y :: x :: []) =
          commitMemV mv (x :: y :: []) := by
        simpa using (commitMemV_swap (mv := mv) (q₁ := [y]) (q₂ := [x]) (by
          intro u hu v hv
          simp at hu hv
          subst u
          subst v
          exact (List.pairwise_cons.mp hdisj).1 x (by simp)))
      rw [show y :: x :: l = (y :: x :: []) ++ l by rfl,
        show x :: y :: l = (x :: y :: []) ++ l by rfl,
        commitMemV_append, commitMemV_append, hpref]
  | trans h₁ h₂ ih₁ ih₂ =>
      exact (ih₁ hdisj).trans
        (ih₂ (memQueuePairwiseDisjoint_perm h₁ hdisj))

#print axioms commitMemV_perm_disjoint

/-! The view-level consequence is useful independently of canonical commit
success.  It compares the memory observation for any initial `MemV` and keeps
the fine-grained terminal-path relation as the source of the permutation. -/
theorem EdgePhaseTerminalPath.memory_view_eq_of_trace
    {E : CoreMemDesign} {s t₁ t₂ : EdgePhaseState}
    {n₁ n₂ : Nat} (ad : EdgePhaseMemoryAdmission E s)
    (q : EdgeCursor → MemNbaQueue)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.memoryQ = q cursor)
    (hp₁ : EdgePhaseTerminalPath E n₁ s t₁)
    (hp₂ : EdgePhaseTerminalPath E n₂ s t₂)
    (decode : MemNbaRecord → String × Int × LVec)
    (mv : MemV)
    (hdisj : memQueuePairwiseDisjoint (t₁.memoryQ.map decode)) :
    commitMemV mv (t₁.memoryQ.map decode) =
      commitMemV mv (t₂.memoryQ.map decode) := by
  have hpermM : t₁.memoryQ.Perm t₂.memoryQ :=
    EdgePhaseTerminalPath.memory_queue_perm
      (s := s) ad q hqueue hp₁ hp₂
  have hperm : (t₁.memoryQ.map decode).Perm (t₂.memoryQ.map decode) :=
    List.Perm.map decode hpermM
  exact commitMemV_perm_disjoint hdisj hperm

#print axioms EdgePhaseTerminalPath.memory_view_eq_of_trace

/-! The canonical commit success receipt is obtained per terminal path from
the existing memory route theorem.  Queue permutation is deliberately absent
here, so this adapter does not smuggle schedule independence into commit
success. -/
theorem EdgePhaseTerminalPath.memory_commit_success_of_decode
    {E : CoreMemDesign} {s t : EdgePhaseState} {n : Nat}
    (ad : EdgePhaseMemoryAdmission E s)
    (hp : EdgePhaseTerminalPath E n s t)
    (hmo : E.memOkB = true)
    (hmc : E.MemCoherent s.state.memory)
    (decode : MemNbaRecord → String × Int × LVec)
    (hcanon : (t.memoryQ.map decode).map E.memRec = t.memoryQ)
    (hrec : ∀ r ∈ t.memoryQ.map decode, E.RecOk r) :
    ∃ m', t.state.memory.commitNba t.memoryQ = some m' ∧
      E.MemCoherent m' ∧
      E.memOf m' = commitMemV (E.memOf s.state.memory) (t.memoryQ.map decode) := by
  obtain ⟨m', hcommit, hcoh, hview⟩ :=
    CoreMemDesign.commitNba_V hmo (t.memoryQ.map decode) s.state.memory hmc hrec
  have hstate := EdgePhaseTerminalPath.memory_state_eq ad hp
  refine ⟨m', ?_, hcoh, hview⟩
  simpa [hstate, hcanon] using hcommit

#print axioms EdgePhaseTerminalPath.memory_commit_success_of_decode

/-! Two successful canonical memory commits have the same observed memory
view when their identity-preserving queues are permutations and the queue
footprint is pairwise disjoint.  The theorem consumes `commitNba_V` rather
than replacing `MemState.commitNba`; commit success and the decode receipts
remain explicit premises of the adapter. -/
theorem EdgePhaseTerminalPath.memory_commit_observation_eq_of_perm
    {E : CoreMemDesign} {s t₁ t₂ : EdgePhaseState}
    {n₁ n₂ : Nat} {m₁ m₂ : MemState}
    (ad : EdgePhaseMemoryAdmission E s)
    (q : EdgeCursor → MemNbaQueue)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.memoryQ = q cursor)
    (hp₁ : EdgePhaseTerminalPath E n₁ s t₁)
    (hp₂ : EdgePhaseTerminalPath E n₂ s t₂)
    (hmo : E.memOkB = true)
    (hmc : E.MemCoherent s.state.memory)
    (decode : MemNbaRecord → String × Int × LVec)
    (hcanon₁ : (t₁.memoryQ.map decode).map E.memRec = t₁.memoryQ)
    (hcanon₂ : (t₂.memoryQ.map decode).map E.memRec = t₂.memoryQ)
    (hrec₁ : ∀ r ∈ t₁.memoryQ.map decode, E.RecOk r)
    (hrec₂ : ∀ r ∈ t₂.memoryQ.map decode, E.RecOk r)
    (hdisj : memQueuePairwiseDisjoint (t₁.memoryQ.map decode))
    (hm₁ : t₁.state.memory.commitNba t₁.memoryQ = some m₁)
    (hm₂ : t₂.state.memory.commitNba t₂.memoryQ = some m₂) :
    E.memOf m₁ = E.memOf m₂ := by
  let q₁ : MemQV := t₁.memoryQ.map decode
  let q₂ : MemQV := t₂.memoryQ.map decode
  have hpermM : t₁.memoryQ.Perm t₂.memoryQ :=
    EdgePhaseTerminalPath.memory_queue_perm
      (s := s) ad q hqueue hp₁ hp₂
  have hperm : q₁.Perm q₂ := by
    exact List.Perm.map decode hpermM
  have hdisj₂ : memQueuePairwiseDisjoint q₂ :=
    memQueuePairwiseDisjoint_perm hperm hdisj
  obtain ⟨m₁', hcommit₁, hcoh₁, hview₁⟩ :=
    CoreMemDesign.commitNba_V hmo q₁ s.state.memory hmc hrec₁
  obtain ⟨m₂', hcommit₂, hcoh₂, hview₂⟩ :=
    CoreMemDesign.commitNba_V hmo q₂ s.state.memory hmc hrec₂
  have hcommit₁' : s.state.memory.commitNba t₁.memoryQ = some m₁' := by
    simpa [q₁, hcanon₁] using hcommit₁
  have hcommit₂' : s.state.memory.commitNba t₂.memoryQ = some m₂' := by
    simpa [q₂, hcanon₂] using hcommit₂
  have hstate₁ := EdgePhaseTerminalPath.memory_state_eq ad hp₁
  have hstate₂ := EdgePhaseTerminalPath.memory_state_eq ad hp₂
  have hm₁' : s.state.memory.commitNba t₁.memoryQ = some m₁ := by
    simpa [hstate₁] using hm₁
  have hm₂' : s.state.memory.commitNba t₂.memoryQ = some m₂ := by
    simpa [hstate₂] using hm₂
  have heq₁ : m₁ = m₁' := by
    exact Option.some.inj (hm₁'.symm.trans hcommit₁')
  have heq₂ : m₂ = m₂' := by
    exact Option.some.inj (hm₂'.symm.trans hcommit₂')
  have hview₁' : E.memOf m₁ = commitMemV (E.memOf s.state.memory) q₁ := by
    rw [heq₁]
    exact hview₁
  have hview₂' : E.memOf m₂ = commitMemV (E.memOf s.state.memory) q₂ := by
    rw [heq₂]
    exact hview₂
  exact hview₁'.trans ((commitMemV_perm_disjoint hdisj hperm).trans hview₂'.symm)

#print axioms EdgePhaseTerminalPath.memory_commit_observation_eq_of_perm

private theorem queuePairwiseDisjoint_perm {q q' : NbaQueue2}:
    q.Perm q' → queuePairwiseDisjoint q → queuePairwiseDisjoint q'
  | hp, h => (List.Perm.pairwise_iff nbaDisj_symm hp).mp h

private theorem commitNba2_perm_disjoint
    {st : SvState} {q q' : NbaQueue2}
    (hkeys : (st.map Prod.fst).Nodup)
    (hdisj : queuePairwiseDisjoint q)
    (hperm : q.Perm q') :
    commitNba2 st q = commitNba2 st q' := by
  induction hperm generalizing st with
  | nil => rfl
  | cons x hperm ih =>
      rw [commitNba2_cons, commitNba2_cons]
      exact ih (by rw [keys_nbaStep]; exact hkeys)
        (List.pairwise_cons.mp hdisj).2
  | swap x y l =>
      have hpref : commitNba2 st (y :: x :: []) =
          commitNba2 st (x :: y :: []) := by
        simpa using (commitNba2_swap (B₁ := [y]) (B₂ := [x]) hkeys (by
          intro u hu v hv
          simp at hu hv
          subst u
          subst v
          simpa using (List.pairwise_cons.mp hdisj).1 x (by simp)))
      rw [show y :: x :: l = (y :: x :: []) ++ l by rfl,
        show x :: y :: l = (x :: y :: []) ++ l by rfl,
        commitNba2_append, commitNba2_append, hpref]
  | trans h₁ h₂ ih₁ ih₂ =>
      exact (ih₁ hkeys hdisj).trans
        (ih₂ hkeys (queuePairwiseDisjoint_perm h₁ hdisj))

/-- Queue order is observationally irrelevant when all updates are pairwise
disjoint and the base view is the same. -/
theorem EdgePhaseState.observable_eq_of_perm
    {E : CoreMemDesign} {s₁ s₂ : EdgePhaseState}
    (hstate : E.scalar.view s₁.state.scalar = E.scalar.view s₂.state.scalar)
    (hkeys : (E.scalar.view s₁.state.scalar).map Prod.fst |>.Nodup)
    (hdisj : queuePairwiseDisjoint s₁.scalarQ)
    (hperm : s₁.scalarQ.Perm s₂.scalarQ) :
    EdgePhaseState.observable E s₁ = EdgePhaseState.observable E s₂ := by
  unfold EdgePhaseState.observable
  rw [hstate]
  have hkeys2 : (E.scalar.view s₂.state.scalar).map Prod.fst |>.Nodup := by
    rw [← hstate]
    exact hkeys
  exact commitNba2_perm_disjoint hkeys2 hdisj hperm

#print axioms EdgePhaseState.observable_eq_of_perm

/-- Terminal paths have the same observable committed state when their complete
update queues are permutations and every pair of queued updates is disjoint.
The path relation supplies the stable pre-edge state, while the permutation is
the explicit schedule-order obligation. -/
theorem EdgePhaseTerminalPath.observable_eq_of_perm
    {E : CoreMemDesign} {s t₁ t₂ : EdgePhaseState}
    {n₁ n₂ : Nat}
    (ad : EdgePhaseNbaAdmission E s)
    (hp₁ : EdgePhaseTerminalPath E n₁ s t₁)
    (hp₂ : EdgePhaseTerminalPath E n₂ s t₂)
    (hkeys : (E.scalar.view s.state.scalar).map Prod.fst |>.Nodup)
    (hdisj : queuePairwiseDisjoint t₁.scalarQ)
    (hperm : t₁.scalarQ.Perm t₂.scalarQ) :
    EdgePhaseState.observable E t₁ = EdgePhaseState.observable E t₂ := by
  have hs₁ := EdgePhaseTerminalPath.state_eq ad hp₁
  have hs₂ := EdgePhaseTerminalPath.state_eq ad hp₂
  have hstate : E.scalar.view t₁.state.scalar = E.scalar.view t₂.state.scalar := by
    rw [hs₁, hs₂]
  have hkeys₁ : (E.scalar.view t₁.state.scalar).map Prod.fst |>.Nodup := by
    rw [hs₁]
    exact hkeys
  exact EdgePhaseState.observable_eq_of_perm hstate hkeys₁ hdisj hperm

#print axioms EdgePhaseTerminalPath.observable_eq_of_perm

/-- The scheduler's path order is observationally irrelevant when each cursor
has a path-independent scalar NBA queue and the complete updates are disjoint. -/
theorem EdgePhaseTerminalPath.observable_eq_of_trace
    {E : CoreMemDesign} {s t₁ t₂ : EdgePhaseState}
    {n₁ n₂ : Nat}
    (ad : EdgePhaseNbaAdmission E s)
    (q : EdgeCursor → NbaQueue2)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.scalarQ = q cursor)
    (hp₁ : EdgePhaseTerminalPath E n₁ s t₁)
    (hp₂ : EdgePhaseTerminalPath E n₂ s t₂)
    (hkeys : (E.scalar.view s.state.scalar).map Prod.fst |>.Nodup)
    (hdisj : queuePairwiseDisjoint t₁.scalarQ) :
    EdgePhaseState.observable E t₁ = EdgePhaseState.observable E t₂ := by
  apply EdgePhaseTerminalPath.observable_eq_of_perm ad hp₁ hp₂ hkeys hdisj
  exact EdgePhaseTerminalPath.scalar_queue_perm ad q hqueue hp₁ hp₂

#print axioms EdgePhaseTerminalPath.observable_eq_of_trace

/-! Termination of the actual source-shaped active-region relation in the
admitted NBA-only class.  The admission record is restricted to the remaining
cursor list after each selection, while the shared state stays fixed. -/
theorem EdgePhaseTerminalPath.exists
    {E : CoreMemDesign} {s : EdgePhaseState}
    (ad : EdgePhaseNbaAdmission E s) :
    ∃ n t, EdgePhaseTerminalPath E n s t := by
  have aux : ∀ k, ∀ (s : EdgePhaseState), s.active.length = k →
      EdgePhaseNbaAdmission E s → ∃ n t, EdgePhaseTerminalPath E n s t := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro s hlen ads
        by_cases hempty : EdgePhaseQuiescent s
        · exact ⟨0, s, .terminal hempty⟩
        · obtain ⟨u, hstep⟩ := EdgePhaseStep.nba_progress ads hempty
          have hlt : u.active.length < k := by
            have hdec := EdgePhaseStep.nba_measure_decreases ads hstep
            simpa [hlen] using hdec
          have hstable : u.state = s.state := by
            cases hstep with
            | select hactive hresume =>
                rename_i before after cursor next result
                have hmem : cursor ∈ s.active := by
                  rw [hactive]
                  simp
                have hs := ads.stable_state cursor result next hmem hresume
                simp [EdgePhaseState.after, hs]
          have hsub : ∀ cursor, cursor ∈ u.active → cursor ∈ s.active := by
            intro cursor hcursor
            cases hstep with
            | select hactive hresume =>
                rename_i before after selected next result
                have hempty' := ads.continuation_empty selected result next
                  (by rw [hactive]; simp) hresume
                have hc' : cursor ∈ before ++ after := by
                  simpa [EdgePhaseState.after, hempty'] using hcursor
                rw [hactive]
                rcases List.mem_append.mp hc' with hb | ha
                · exact List.mem_append_left _ hb
                · exact List.mem_append_right before (List.mem_cons_of_mem selected ha)
          have adu := ads.restrict hstable hsub
          obtain ⟨n, t, ht⟩ := ih u.active.length hlt u rfl adu
          exact ⟨n + 1, t, .head hempty hstep ht⟩
  exact aux s.active.length s rfl ad

/-! Every terminal path from an admitted NBA-only active region has the same
committed observable scalar view. -/
theorem EdgePhaseTerminalPath.observable_confluent
    {E : CoreMemDesign} {s : EdgePhaseState}
    (ad : EdgePhaseNbaAdmission E s)
    (q : EdgeCursor → NbaQueue2)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.scalarQ = q cursor)
    (hkeys : (E.scalar.view s.state.scalar).map Prod.fst |>.Nodup)
    {n₁ n₂ : Nat} {t₁ t₂ : EdgePhaseState}
    (hp₁ : EdgePhaseTerminalPath E n₁ s t₁)
    (hp₂ : EdgePhaseTerminalPath E n₂ s t₂)
    (hdisj : queuePairwiseDisjoint t₁.scalarQ) :
    EdgePhaseState.observable E t₁ = EdgePhaseState.observable E t₂ := by
  exact EdgePhaseTerminalPath.observable_eq_of_trace ad q hqueue hp₁ hp₂ hkeys hdisj

/-! End-to-end bridge for the source-shaped NBA phase.  The scheduler path is
constructed from the real `EdgePhaseStep` relation, all terminal paths agree
on the committed scalar observable, and one selected path is tied to the
canonical executor by explicit settle/run/commit receipts. -/
theorem EdgePhaseTerminalPath.confluence_refines_step
    {E : CoreMemDesign} {s : EdgePhaseState}
    (ad : EdgePhaseNbaAdmission E s)
    (q : EdgeCursor → NbaQueue2)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.scalarQ = q cursor)
    (hkeys : (E.scalar.view s.state.scalar).map Prod.fst |>.Nodup)
    (hdisj : ∀ {n t}, EdgePhaseTerminalPath E n s t → queuePairwiseDisjoint t.scalarQ)
    (hcomb : E.hasComb = false) (himp : E.hasImplicit = false)
    {n : Nat} {t : EdgePhaseState}
    (hp : EdgePhaseTerminalPath E n s t)
    {st : CoreMemState} {entry : SvState}
    {pre0 s3 next : CoreMemState} {m : MemState}
    (h0 : E.settleCanonical E.env E.elems (E.inputState st entry) E.processes.toList = .ok pre0)
    (h1 : E.settleCanonical E.env E.elems pre0 E.processes.toList = .ok s.state)
    (he : E.runEdges E.env E.elems t.state
      (E.scalar.view st.scalar) (E.scalar.view t.state.scalar) E.processes.toList =
      .ok { state := t.state, scalarQ := t.scalarQ, memoryQ := t.memoryQ, locals := [] })
    (hm : t.state.memory.commitNba t.memoryQ = some m)
    (h3 : E.settleCanonical E.env E.elems
      (E.committedState
        { state := t.state, scalarQ := t.scalarQ, memoryQ := t.memoryQ, locals := [] } m)
      E.processes.toList = .ok s3)
    (h4 : E.settleCanonical E.env E.elems s3 E.processes.toList = .ok next)
    (hq : E.firesAny (E.scalar.view t.state.scalar) (E.scalar.view next.scalar) = false) :
    (∀ n' t', EdgePhaseTerminalPath E n' s t' →
      EdgePhaseState.observable E t' = EdgePhaseState.observable E t) ∧
    E.step st entry = .ok next := by
  have hstate := EdgePhaseTerminalPath.state_eq ad hp
  have hq' : E.firesAny (E.scalar.view s.state.scalar) (E.scalar.view next.scalar) = false := by
    simpa [hstate] using hq
  have hstep := EdgePhaseTerminalPath.executor_result ad hp hcomb himp h0 h1 he hm h3 h4 hq'
  have hobs : ∀ n' t', EdgePhaseTerminalPath E n' s t' →
      EdgePhaseState.observable E t' = EdgePhaseState.observable E t := by
    intro n' t' hp'
    exact EdgePhaseTerminalPath.observable_eq_of_trace ad q hqueue hp' hp hkeys
      (hdisj hp')
  exact ⟨hobs, hstep⟩

end LeanModels.Sv.Kernel
