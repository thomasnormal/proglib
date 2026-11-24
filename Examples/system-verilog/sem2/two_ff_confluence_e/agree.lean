import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.EdgeConfluence
import LeanModels.Sv.SeqCycleTactic

/-! A real two-process NBA confluence witness.

Both processes are parser-retained edge processes on the same input clock.  They
write disjoint scalar targets with nonblocking assignments.  The canonical E
route therefore has two queue contributions whose order is erased by the
admitted driver guard. -/

namespace Examples.«system-verilog».sem2.two_ff_confluence_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 twoFf
  from "Examples/system-verilog/sem2/two_ff_confluence_e/two_ff_confluence_e.sv.json"

#guard match twoFf.e with
  | .ok E => E.processes.size == 2 && E.seqOblI && E.oblDrivers && E.oblEdgeOrder
  | _ => false

#guard match twoFf.e with
  | .ok E =>
      match runCoreMemRows E E.initial [
        [("clk", LVec.ofNat 1 0), ("a_in", LVec.ofNat 1 0), ("b_in", LVec.ofNat 1 1)],
        [("clk", LVec.ofNat 1 1), ("a_in", LVec.ofNat 1 0), ("b_in", LVec.ofNat 1 1)],
        [("clk", LVec.ofNat 1 0), ("a_in", LVec.ofNat 1 1), ("b_in", LVec.ofNat 1 0)],
        [("clk", LVec.ofNat 1 1), ("a_in", LVec.ofNat 1 1), ("b_in", LVec.ofNat 1 0)]] with
      | .ok rows =>
          (rows.map (fun st =>
            (SvState.showSignal (CoreMemState.view E st) "a_q",
             SvState.showSignal (CoreMemState.view E st) "b_q"))) ==
            [("x", "x"), ("0", "1"), ("0", "1"), ("1", "0")]
      | _ => false
  | _ => false


example : SeqDesignI twoFf.e := by
  refine SeqDesign.toI (clk := "clk") ?_
  cases hX : twoFf.e with
  | ok E =>
      sv_seq_inst [twoFf.e, twoFf.pdesign] at hX
      subst hX
      exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
  | timeout => sv_seq_inst [twoFf.e, twoFf.pdesign] at hX
  | unsupported m => sv_seq_inst [twoFf.e, twoFf.pdesign] at hX


/-! The concrete wrapper exposes the real guarded confluence theorem for this
multi-process envelope.  Queue separation is supplied by the design's
parser-derived driver obligation, while the scheduler and executor receipts
remain explicit at the theorem boundary. -/
theorem two_ff_nba_confluence
    {E : CoreMemDesign} (hE : twoFf.e = .ok E)
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
  have hD : SeqDesign (twoFf.e) "clk" := by
    cases hX : twoFf.e with
    | ok E' =>
        sv_seq_inst [twoFf.e, twoFf.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [twoFf.e, twoFf.pdesign] at hX
    | unsupported m => sv_seq_inst [twoFf.e, twoFf.pdesign] at hX
  obtain ⟨E', hE', hPB, hOB⟩ := hD
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.edge_nba_confluence_refines_step_guarded
    hPB.toSeqProfileI (CoreMemDesign.seqOblB_I hOB) hc hmc hty hslot
    hdrivers hdistinct F hs hw hq hkeys hroute

#print axioms two_ff_nba_confluence

/-! The same receipt with queue totality rather than a separately named queue
    function.  The adapter derives each queue from the real `procQ` evaluator,
    while the process-order and route receipts remain explicit. -/
theorem two_ff_nba_confluence_of_defined
    {E : CoreMemDesign} (hE : twoFf.e = .ok E)
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
    (hdefined : ∀ (k : Nat) (p : CoreMemProc), E.processes[k]? = some p →
      ∃ q, E.procQ s.view s.view s.view (E.memOf st.memory) p = .ok q)
    (hkeys : (s.view.map Prod.fst).Nodup)
    {r : ExecV} (hroute : E.edgesV s.view s.view s.view (E.memOf st.memory)
      E.processes.toList = .ok r) :
    ∃ n t st',
      EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory) n s t ∧
      (∀ n' t', EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory)
        n' s t' → t' = t) ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' ∧ t.view = commitNba2 s.view r.2.1 := by
  have hD : SeqDesign (twoFf.e) "clk" := by
    cases hX : twoFf.e with
    | ok E' =>
        sv_seq_inst [twoFf.e, twoFf.pdesign] at hX
        subst hX
        exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
    | timeout => sv_seq_inst [twoFf.e, twoFf.pdesign] at hX
    | unsupported m => sv_seq_inst [twoFf.e, twoFf.pdesign] at hX
  obtain ⟨E', hE', hPB, hOB⟩ := hD
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.edge_nba_confluence_refines_step_guarded_of_defined
    hPB.toSeqProfileI (CoreMemDesign.seqOblB_I hOB) hc hmc hty hslot
    hdrivers hdistinct hs hw hdefined hkeys hroute

#print axioms two_ff_nba_confluence_of_defined


end Examples.«system-verilog».sem2.two_ff_confluence_e
