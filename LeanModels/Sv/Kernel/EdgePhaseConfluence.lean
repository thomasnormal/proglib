import LeanModels.Sv.Kernel.CoreMemResume

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

end LeanModels.Sv.Kernel
