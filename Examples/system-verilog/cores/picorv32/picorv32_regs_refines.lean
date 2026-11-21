import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».cores.picorv32

/-! The real upstream `picorv32_regs` leaf reaches the instant clocked profile.
    This theorem applies the canonical E step theorem to that loaded design.
    The slot equation is an explicit premise, so the result is about the real
    `CoreMemDesign.step` and does not assume an architectural invariant. -/

set_option maxRecDepth 100000 in
load_design_sv2 regs from "Examples/system-verilog/cores/picorv32/picorv32_regs.sv.json"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
seq_mirror : regs.e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem picorv32_regs_step_refines {E : CoreMemDesign} (hE : regs.e = .ok E)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hv : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv')) :
    ∃ st', E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' ∧ E.Coherent st' ∧ E.MemCoherent st'.memory := by
  obtain ⟨E', hE', hP, hO⟩ := (show SeqDesignI regs.e by sv_structure)
  rw [hE] at hE'
  cases hE'
  exact CoreMemDesign.step_seqI hP hO hc hmc hty hv

#print axioms picorv32_regs_step_refines

/-! The register-file leaf has no scalar process targeting `wdata`.  The
    frame theorem therefore gives a concrete input-preservation fact for the
    loaded RTL, including all 4-state values accepted by `EntryTyped`. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem picorv32_regs_wdata_undriven {E : CoreMemDesign} (hE : regs.e = .ok E)
    {st : CoreMemState} (hc : E.Coherent st) {entry : SvState}
    (hty : EntryTyped E.scalar.toDesign2 entry) {v' : SvState} {mv' : MemV}
    (hv : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv')) :
    SvState.lookup v' "wdata" =
      SvState.lookup (E.applyRow (E.scalar.view st.scalar) entry) "wdata" := by
  obtain ⟨E', hE', hP, hO⟩ := (show SeqDesignI regs.e by sv_structure)
  rw [hE] at hE'
  cases hE'
  have hE0 : regs.mirror = E := Res.ok.inj ((regs.mirror_eq).symm.trans hE)
  subst hE0
  apply CoreMemDesign.slotV_undriven hP hc hty hv
  intro hx
  have hi := CoreMemDesign.driven_not_input hO hx
  apply hi
  simp [regs.mirror_def, Elab.toDesign2, Design2.inputNames]

#print axioms picorv32_regs_wdata_undriven

end Examples.«system-verilog».cores.picorv32
