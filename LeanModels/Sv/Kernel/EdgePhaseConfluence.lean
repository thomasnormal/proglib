import LeanModels.Sv.Kernel.CoreMemResume
import LeanModels.Sv.Scheduler
import LeanModels.Sv.SeqCycleStep

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

#print axioms twoNbaWitness_all_orders

end LeanModels.Sv.Scheduler
