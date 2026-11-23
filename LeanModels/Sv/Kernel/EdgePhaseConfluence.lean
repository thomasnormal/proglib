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
    have hs := ad.stable_state cursor result next (hsub cursor hmem) (by simpa [hstate] using hresume)
    exact hs.trans hstate.symm
  · intro cursor result next hmem hresume
    apply ad.no_memory_nba cursor result next (hsub cursor hmem)
    simpa [hstate] using hresume

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

end LeanModels.Sv.Kernel
