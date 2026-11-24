import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Kernel.EdgeConfluence
import LeanModels.Sv.SeqCycleObl

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.clocked_derived_shift_e

load_design_sv2 derivedShift from
  "Examples/system-verilog/sem2/clocked_derived_shift_e/clocked_derived_shift_e.sv.json"

set_option maxRecDepth 100000 in
#guard match PDesign.instantiateCoreMem derivedShift.pdesign [4] with
  | .ok E => E.topoC == true && E.oblDrivers == true && E.oblInputsUndriven == true &&
      E.oblSources == true && E.oblNoSourceRead == true && E.oblEdgeOrder == true &&
      E.oblConverted == true
  | _ => false

end Examples.«system-verilog».sem2.clocked_derived_shift_e

namespace Examples.«system-verilog».sem2.clocked_derived_shift_e

/-! The source-specific scheduler receipt.  The profile and obligation records
remain explicit at this boundary because the direct route guard above is the
kernel check for the admitted E shape. -/
theorem derived_shift_nba_confluence_of_defined
    {E : CoreMemDesign}
    (_hE : PDesign.instantiateCoreMem derivedShift.pdesign [4] = .ok E)
    (hP : E.SeqProfileI) (hO : E.seqOblI = true)
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
    (∃ n t st',
      EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory) n s t ∧
      (∀ n' t', EdgeScheduleTerminalPath E s.view s.view s.view (E.memOf st.memory)
        n' s t' → t' = t) ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' ∧ t.view = commitNba2 s.view r.2.1) := by
  have hmain := CoreMemDesign.edge_nba_confluence_refines_step_guarded_of_defined
    hP hO hc hmc hty hslot
    hdrivers hdistinct hs hw hkeys hroute
  exact hmain

#print axioms derived_shift_nba_confluence_of_defined

end Examples.«system-verilog».sem2.clocked_derived_shift_e
