import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleObl
import LeanModels.Sv.SeqCycleTactic
import LeanModels.Sv.Kernel.EdgeConfluence
import LeanModels.Sv.Kernel.EdgePhaseConfluence
import LeanModels.Sv.Kernel.CombPhaseFrame

/-!
# Concrete schedule bridges

These are three source-shaped clocked designs already used by the E route.  The
generic bridge in `SeqCycleObl` is instantiated at each envelope.  The
`hslot` premise is the route's view-level slot, so each result compares an
arbitrary process permutation with the canonical `CoreMemDesign.step` result.
The examples deliberately keep the slot premise explicit: it is the boundary
at which the cycle equations for each design supply their concrete row proof.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.confluence_proof


/-! The three concrete wrappers below retain the executor bridge for the
parameterized shift register, counter and case-process examples.  The
NBA-only scheduler relation is in `EdgeConfluence`: its terminal paths are
unique under the same no-overlap guard, and each selected process is bridged
back to `edgesV` by `EdgeScheduleStep.executor_cons_bridge`. -/

load_design_sv2 shreg from "Examples/system-verilog/sem2/clk_shreg/clk_shreg.sv.json"
load_design_sv2 cnt from "Examples/system-verilog/sem2/clk_cnt/clk_cnt.sv.json"
load_design_sv2 caseF from "Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_step11.sv.json"

theorem shreg_bridge (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign}
    (hE : shreg.e N = .ok E) {st : CoreMemState} (hc : E.Coherent st)
    (hmc : E.MemCoherent st.memory) {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    {ps : List CoreMemProc} (hσ : ps.Perm E.processes.toList) :
    ∃ p r r' st',
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) E.processes.toList = .ok r ∧
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧ E.memOf st'.memory = mv' := by
  have hD : SeqDesign (shreg.e N) "clk" := by
    cases hX : shreg.e N with
    | ok E' =>
        sv_seq_inst [shreg.e, shreg.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [shreg.e, shreg.pdesign] at hX
    | unsupported m => sv_seq_inst [shreg.e, shreg.pdesign] at hX
  obtain ⟨E', hE', hPB, hOB⟩ := hD
  have hP := hPB.toSeqProfileI
  have hO := CoreMemDesign.seqOblB_I hOB
  obtain ⟨hdrivers, htopo, hinputs, hsources, hreads, hedge, hconverted⟩ :=
    CoreMemDesign.seqOblI_spec hO
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.edge_schedule_refines_step_guarded hP hdrivers htopo hinputs hsources hreads hedge hconverted
    hc hmc hty hslot hσ

theorem cnt_bridge (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign}
    (hE : cnt.e N = .ok E) {st : CoreMemState} (hc : E.Coherent st)
    (hmc : E.MemCoherent st.memory) {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    {ps : List CoreMemProc} (hσ : ps.Perm E.processes.toList) :
    ∃ p r r' st',
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) E.processes.toList = .ok r ∧
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧ E.memOf st'.memory = mv' := by
  have hD : SeqDesign (cnt.e N) "clk" := by
    cases hX : cnt.e N with
    | ok E' =>
        sv_seq_inst [cnt.e, cnt.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [cnt.e, cnt.pdesign] at hX
    | unsupported m => sv_seq_inst [cnt.e, cnt.pdesign] at hX
  obtain ⟨E', hE', hPB, hOB⟩ := hD
  have hP := hPB.toSeqProfileI
  have hO := CoreMemDesign.seqOblB_I hOB
  obtain ⟨hdrivers, htopo, hinputs, hsources, hreads, hedge, hconverted⟩ :=
    CoreMemDesign.seqOblI_spec hO
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.edge_schedule_refines_step_guarded hP hdrivers htopo hinputs hsources hreads hedge hconverted
    hc hmc hty hslot hσ

theorem case_bridge {E : CoreMemDesign} (hE : caseF.e = .ok E) {st : CoreMemState}
    (hc : E.Coherent st) (hmc : E.MemCoherent st.memory) {entry : SvState}
    (hty : EntryTyped E.scalar.toDesign2 entry) {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    {ps : List CoreMemProc} (hσ : ps.Perm E.processes.toList) :
    ∃ p r r' st',
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) E.processes.toList = .ok r ∧
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧ E.memOf st'.memory = mv' := by
  have hD : SeqDesign caseF.e "clk" := by
    cases hX : caseF.e with
    | ok E' =>
        sv_seq_inst [caseF.e, caseF.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [caseF.e, caseF.pdesign] at hX
    | unsupported m => sv_seq_inst [caseF.e, caseF.pdesign] at hX
  obtain ⟨E', hE', hPB, hOB⟩ := hD
  have hP := hPB.toSeqProfileI
  have hO := CoreMemDesign.seqOblB_I hOB
  obtain ⟨hdrivers, htopo, hinputs, hsources, hreads, hedge, hconverted⟩ :=
    CoreMemDesign.seqOblI_spec hO
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.edge_schedule_refines_step_guarded hP hdrivers htopo hinputs hsources hreads hedge hconverted
    hc hmc hty hslot hσ

/-! Concrete scheduler-path receipts for the three source-shaped envelopes.
    The queue, disjointness, and evaluator receipts remain explicit premises.
    Each theorem therefore instantiates the scheduler relation on a real
    envelope without hiding a design-specific admission assumption. -/
theorem shreg_scheduler_terminal (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30)
    {E : CoreMemDesign} (hE : shreg.e N = .ok E)
    {s : EdgeScheduleState} (hs : s.pending = List.range E.processes.size)
    (F : Nat → NbaQueue2) {mv : MemV}
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ s.view s.view s.view mv p = .ok (F k))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ u' ∈ F j, u.1 ≠ u'.1)
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view mv E.processes.toList = .ok r) :
    ∃ n t, EdgeScheduleTerminalPath E s.view s.view s.view mv n s t ∧
      t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign (shreg.e N) "clk" := by
    cases hX : shreg.e N with
    | ok E' =>
        sv_seq_inst [shreg.e, shreg.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [shreg.e, shreg.pdesign] at hX
    | unsupported m => sv_seq_inst [shreg.e, shreg.pdesign] at hX
  obtain ⟨E', hE', _, _⟩ := hD
  have hEq : E' = E := Res.ok.inj (hE'.symm.trans hE)
  subst E'
  obtain ⟨n, t, hp⟩ := EdgeScheduleTerminalPath.exists_processes_range F hs hw hq hdisj hkeys
  obtain ⟨r', hr', hv⟩ := EdgeScheduleTerminalPath.view_eq_edgesV_processes_indexed F hs hw hq hdisj hkeys hp hroute
  have heq : r' = r := Res.ok.inj (hr'.symm.trans hroute)
  subst r'
  exact ⟨n, t, hp, hv⟩

theorem cnt_scheduler_terminal (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30)
    {E : CoreMemDesign} (hE : cnt.e N = .ok E)
    {s : EdgeScheduleState} (hs : s.pending = List.range E.processes.size)
    (F : Nat → NbaQueue2) {mv : MemV}
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ s.view s.view s.view mv p = .ok (F k))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ u' ∈ F j, u.1 ≠ u'.1)
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view mv E.processes.toList = .ok r) :
    ∃ n t, EdgeScheduleTerminalPath E s.view s.view s.view mv n s t ∧
      t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign (cnt.e N) "clk" := by
    cases hX : cnt.e N with
    | ok E' =>
        sv_seq_inst [cnt.e, cnt.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [cnt.e, cnt.pdesign] at hX
    | unsupported m => sv_seq_inst [cnt.e, cnt.pdesign] at hX
  obtain ⟨E', hE', _, _⟩ := hD
  have hEq : E' = E := Res.ok.inj (hE'.symm.trans hE)
  subst E'
  obtain ⟨n, t, hp⟩ := EdgeScheduleTerminalPath.exists_processes_range F hs hw hq hdisj hkeys
  obtain ⟨r', hr', hv⟩ := EdgeScheduleTerminalPath.view_eq_edgesV_processes_indexed F hs hw hq hdisj hkeys hp hroute
  have heq : r' = r := Res.ok.inj (hr'.symm.trans hroute)
  subst r'
  exact ⟨n, t, hp, hv⟩

theorem case_scheduler_terminal
    {E : CoreMemDesign} (hE : caseF.e = .ok E)
    {s : EdgeScheduleState} (hs : s.pending = List.range E.processes.size)
    (F : Nat → NbaQueue2) {mv : MemV}
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ s.view s.view s.view mv p = .ok (F k))
    (hdisj : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ u' ∈ F j, u.1 ≠ u'.1)
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view mv E.processes.toList = .ok r) :
    ∃ n t, EdgeScheduleTerminalPath E s.view s.view s.view mv n s t ∧
      t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign caseF.e "clk" := by
    cases hX : caseF.e with
    | ok E' =>
        sv_seq_inst [caseF.e, caseF.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [caseF.e, caseF.pdesign] at hX
    | unsupported m => sv_seq_inst [caseF.e, caseF.pdesign] at hX
  obtain ⟨E', hE', _, _⟩ := hD
  have hEq : E' = E := Res.ok.inj (hE'.symm.trans hE)
  subst E'
  obtain ⟨n, t, hp⟩ := EdgeScheduleTerminalPath.exists_processes_range F hs hw hq hdisj hkeys
  obtain ⟨r', hr', hv⟩ := EdgeScheduleTerminalPath.view_eq_edgesV_processes_indexed F hs hw hq hdisj hkeys hp hroute
  have heq : r' = r := Res.ok.inj (hr'.symm.trans hroute)
  subst r'
  exact ⟨n, t, hp, hv⟩

#print axioms shreg_bridge
#print axioms cnt_bridge
#print axioms case_bridge
#print axioms shreg_scheduler_terminal
#print axioms cnt_scheduler_terminal
#print axioms case_scheduler_terminal

/-! Driver-backed confluence receipts for the same three real envelopes.  The
    process-record distinctness premise stays explicit because the parser can
    represent duplicate empty-target records. -/
theorem shreg_confluent_drivers (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30)
    {E : CoreMemDesign} (hE : shreg.e N = .ok E)
    (hdrivers : E.oblDrivers = true)
    (hdistinct : ∀ (i j : Nat) (hi : i < E.processes.size) (hj : j < E.processes.size),
      i ≠ j → E.processes[i]'hi ≠ E.processes[j]'hj)
    {s : EdgeScheduleState} (F : Nat → NbaQueue2) (hs : s.pending = List.range E.processes.size)
    {mv : MemV}
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ s.view s.view s.view mv p = .ok (F k))
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view mv E.processes.toList = .ok r) :
    ∃ n t, EdgeScheduleTerminalPath E s.view s.view s.view mv n s t ∧
      (∀ n' t', EdgeScheduleTerminalPath E s.view s.view s.view mv n' s t' → t' = t) ∧
      t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign (shreg.e N) "clk" := by
    cases hX : shreg.e N with
    | ok E' =>
        sv_seq_inst [shreg.e, shreg.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [shreg.e, shreg.pdesign] at hX
    | unsupported m => sv_seq_inst [shreg.e, shreg.pdesign] at hX
  obtain ⟨E', hE', _, _⟩ := hD
  have hEq : E' = E := Res.ok.inj (hE'.symm.trans hE)
  subst E'
  exact EdgeScheduleTerminalPath.confluent_processes_range_drivers
    hdrivers hdistinct F hs hw hq hkeys hroute

/-! The end-to-end guarded NBA theorem instantiated on the real shift-register
 envelope.  All queue, source-order, state-coherence, and driver receipts stay
 explicit at this concrete boundary. -/
theorem shreg_nba_confluence_step (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30)
    {E : CoreMemDesign} (hE : shreg.e N = .ok E)
    {st : CoreMemState} (hc : E.Coherent st)
    (hmc : E.MemCoherent st.memory) {entry : SvState}
    (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    (hdrivers : E.oblDrivers = true)
    (hdistinct : ∀ (i j : Nat) (hi : i < E.processes.size) (hj : j < E.processes.size),
      i ≠ j → E.processes[i]'hi ≠ E.processes[j]'hj)
    {s : EdgeScheduleState} (F : Nat → NbaQueue2)
    (hs : s.pending = List.range E.processes.size)
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ s.view s.view s.view (E.memOf st.memory) p = .ok (F k))
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view (E.memOf st.memory) E.processes.toList = .ok r) :
    ∃ n t st',
      EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory) n s t ∧
      (∀ n' t', EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory) n' s t' →
        t' = t) ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' ∧ t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign (shreg.e N) "clk" := by
    cases hX : shreg.e N with
    | ok E' =>
        sv_seq_inst [shreg.e, shreg.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [shreg.e, shreg.pdesign] at hX
    | unsupported m => sv_seq_inst [shreg.e, shreg.pdesign] at hX
  obtain ⟨E', hE', hPB, hOB⟩ := hD
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.edge_nba_confluence_refines_step_guarded
    hPB.toSeqProfileI (CoreMemDesign.seqOblB_I hOB) hc hmc hty hslot
    hdrivers hdistinct F hs hw hq hkeys hroute

theorem cnt_confluent_drivers (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30)
    {E : CoreMemDesign} (hE : cnt.e N = .ok E)
    (hdrivers : E.oblDrivers = true)
    (hdistinct : ∀ (i j : Nat) (hi : i < E.processes.size) (hj : j < E.processes.size),
      i ≠ j → E.processes[i]'hi ≠ E.processes[j]'hj)
    {s : EdgeScheduleState} (F : Nat → NbaQueue2) (hs : s.pending = List.range E.processes.size)
    {mv : MemV}
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ s.view s.view s.view mv p = .ok (F k))
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view mv E.processes.toList = .ok r) :
    ∃ n t, EdgeScheduleTerminalPath E s.view s.view s.view mv n s t ∧
      (∀ n' t', EdgeScheduleTerminalPath E s.view s.view s.view mv n' s t' → t' = t) ∧
      t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign (cnt.e N) "clk" := by
    cases hX : cnt.e N with
    | ok E' =>
        sv_seq_inst [cnt.e, cnt.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [cnt.e, cnt.pdesign] at hX
    | unsupported m => sv_seq_inst [cnt.e, cnt.pdesign] at hX
  obtain ⟨E', hE', _, _⟩ := hD
  have hEq : E' = E := Res.ok.inj (hE'.symm.trans hE)
  subst E'
  exact EdgeScheduleTerminalPath.confluent_processes_range_drivers
    hdrivers hdistinct F hs hw hq hkeys hroute

theorem cnt_nba_confluence_step (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30)
    {E : CoreMemDesign} (hE : cnt.e N = .ok E)
    {st : CoreMemState} (hc : E.Coherent st)
    (hmc : E.MemCoherent st.memory) {entry : SvState}
    (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    (hdrivers : E.oblDrivers = true)
    (hdistinct : ∀ (i j : Nat) (hi : i < E.processes.size) (hj : j < E.processes.size),
      i ≠ j → E.processes[i]'hi ≠ E.processes[j]'hj)
    {s : EdgeScheduleState} (F : Nat → NbaQueue2)
    (hs : s.pending = List.range E.processes.size)
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ s.view s.view s.view (E.memOf st.memory) p = .ok (F k))
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view (E.memOf st.memory)
      E.processes.toList = .ok r) :
    ∃ n t st',
      EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory) n s t ∧
      (∀ n' t', EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory) n' s t' →
        t' = t) ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' ∧ t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign (cnt.e N) "clk" := by
    cases hX : cnt.e N with
    | ok E' =>
        sv_seq_inst [cnt.e, cnt.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [cnt.e, cnt.pdesign] at hX
    | unsupported m => sv_seq_inst [cnt.e, cnt.pdesign] at hX
  obtain ⟨E', hE', hPB, hOB⟩ := hD
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.edge_nba_confluence_refines_step_guarded
    hPB.toSeqProfileI (CoreMemDesign.seqOblB_I hOB) hc hmc hty hslot
    hdrivers hdistinct F hs hw hq hkeys hroute

theorem case_confluent_drivers
    {E : CoreMemDesign} (hE : caseF.e = .ok E)
    (hdrivers : E.oblDrivers = true)
    (hdistinct : ∀ (i j : Nat) (hi : i < E.processes.size) (hj : j < E.processes.size),
      i ≠ j → E.processes[i]'hi ≠ E.processes[j]'hj)
    {s : EdgeScheduleState} (F : Nat → NbaQueue2) (hs : s.pending = List.range E.processes.size)
    {mv : MemV}
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ s.view s.view s.view mv p = .ok (F k))
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view mv E.processes.toList = .ok r) :
    ∃ n t, EdgeScheduleTerminalPath E s.view s.view s.view mv n s t ∧
      (∀ n' t', EdgeScheduleTerminalPath E s.view s.view s.view mv n' s t' → t' = t) ∧
      t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign caseF.e "clk" := by
    cases hX : caseF.e with
    | ok E' =>
        sv_seq_inst [caseF.e, caseF.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [caseF.e, caseF.pdesign] at hX
    | unsupported m => sv_seq_inst [caseF.e, caseF.pdesign] at hX
  obtain ⟨E', hE', _, _⟩ := hD
  have hEq : E' = E := Res.ok.inj (hE'.symm.trans hE)
  subst E'
  exact EdgeScheduleTerminalPath.confluent_processes_range_drivers
    hdrivers hdistinct F hs hw hq hkeys hroute

theorem case_nba_confluence_step
    {E : CoreMemDesign} (hE : caseF.e = .ok E)
    {st : CoreMemState} (hc : E.Coherent st)
    (hmc : E.MemCoherent st.memory) {entry : SvState}
    (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    (hdrivers : E.oblDrivers = true)
    (hdistinct : ∀ (i j : Nat) (hi : i < E.processes.size) (hj : j < E.processes.size),
      i ≠ j → E.processes[i]'hi ≠ E.processes[j]'hj)
    {s : EdgeScheduleState} (F : Nat → NbaQueue2)
    (hs : s.pending = List.range E.processes.size)
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hq : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      E.procQ s.view s.view s.view (E.memOf st.memory) p = .ok (F k))
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view (E.memOf st.memory)
      E.processes.toList = .ok r) :
    ∃ n t st',
      EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory) n s t ∧
      (∀ n' t', EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory) n' s t' →
        t' = t) ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' ∧ t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign caseF.e "clk" := by
    cases hX : caseF.e with
    | ok E' =>
        sv_seq_inst [caseF.e, caseF.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [caseF.e, caseF.pdesign] at hX
    | unsupported m => sv_seq_inst [caseF.e, caseF.pdesign] at hX
  obtain ⟨E', hE', hPB, hOB⟩ := hD
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.edge_nba_confluence_refines_step_guarded
    hPB.toSeqProfileI (CoreMemDesign.seqOblB_I hOB) hc hmc hty hslot
    hdrivers hdistinct F hs hw hq hkeys hroute

#print axioms shreg_confluent_drivers
#print axioms cnt_confluent_drivers
#print axioms case_confluent_drivers

end Examples.«system-verilog».seq_cycle.confluence_proof
