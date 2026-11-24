import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.EdgeConfluence
import LeanModels.Sv.SeqCycleTactic

namespace Examples.«system-verilog».sem2.fsm_logic_confluence_e
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 fsm from
  "Examples/system-verilog/sem2/fsm_logic_confluence_e/fsm_logic_confluence_e.sv.json"

#guard match fsm.e with
  | .ok E => E.processes.size == 3 && E.seqOblI && E.oblDrivers && E.oblEdgeOrder
  | _ => false

example : SeqDesignI fsm.e := by
  refine SeqDesign.toI (clk := "clk") ?_
  cases hX : fsm.e with
  | ok E =>
      sv_seq_inst [fsm.e, fsm.pdesign] at hX
      cases hX
      exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
  | timeout => sv_seq_inst [fsm.e, fsm.pdesign] at hX
  | unsupported m => sv_seq_inst [fsm.e, fsm.pdesign] at hX

theorem fsm_nba_confluence
    {E : CoreMemDesign} (hE : fsm.e = .ok E)
    {st : CoreMemState} (hc : E.Coherent st)
    (hmc : E.MemCoherent st.memory) {entry : SvState}
    (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    (hdrivers : E.oblDrivers = true)
    (hdistinct : ∀ (i j : Nat) (hi : i < E.processes.size) (hj : j < E.processes.size),
      i ≠ j → E.processes[i]'hi ≠ E.processes[j]'hj)
    {s : EdgeScheduleState} (hs : s.pending = List.range E.processes.size)
    (hw : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p → p.nbaWholeP = true)
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view (E.memOf st.memory)
      E.processes.toList = .ok r) :
    ∃ n t st',
      EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory) n s t ∧
      (∀ n' t', EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory)
        n' s t' → t' = t) ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' ∧ t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign fsm.e "clk" := by
    cases hX : fsm.e with
    | ok E' =>
        sv_seq_inst [fsm.e, fsm.pdesign] at hX
        cases hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [fsm.e, fsm.pdesign] at hX
    | unsupported m => sv_seq_inst [fsm.e, fsm.pdesign] at hX
  obtain ⟨E', hE', hP, hO⟩ := hD
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.edge_nba_confluence_refines_step_guarded_of_defined
    hP.toSeqProfileI (CoreMemDesign.seqOblB_I hO) hc hmc hty hslot
    hdrivers hdistinct hs hw hkeys hroute

#print axioms fsm_nba_confluence
end Examples.«system-verilog».sem2.fsm_logic_confluence_e
