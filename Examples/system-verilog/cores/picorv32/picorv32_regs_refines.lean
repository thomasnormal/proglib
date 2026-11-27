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

/-! A concrete quiet row of the loaded register-file leaf.  The row keeps the
    clock and write-enable low, so the two continuous reads observe indices
    30 and 29 without issuing a memory write. -/

private theorem regs_evalSized_not_signal (env : IEnv) (n : String) (msb lsb : PExpr) :
    evalSized env (.unary (.m0 .bnot) (.partSel (.ident n) msb lsb)) =
      .error s!"signal '{n}' in a constant context" := by
  rfl

private theorem regs_zero_scan :
    (Array.ofFn (n := 32) (fun _ : Fin 32 => Logic.l0)).any
        (fun a => a == Logic.l1) 0 1 = false := by
  simp [Array.any, Array.anyM, Array.anyM.loop]

def picorv32_regs_quiet_view (wd rd1 rd2 : LVec) : SvState :=
  [("clk", LVec.ofNat 1 0), ("wen", LVec.ofNat 1 0), ("waddr", LVec.ofNat 6 1),
   ("raddr1", LVec.ofNat 6 1), ("raddr2", LVec.ofNat 6 2), ("wdata", wd),
   ("rdata1", rd1), ("rdata2", rd2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem picorv32_regs_quiet_read_step {E : CoreMemDesign} (hE : regs.e = .ok E)
    (wd rd1 rd2 : LVec) (mv : MemV) (hwd : wd.width = 32)
    (hrd1 : rd1.width = 32) (hrd2 : rd2.width = 32)
    (hmv : ∀ k, (mv "regs" k).width = 32) :
    E.slotV (picorv32_regs_quiet_view wd rd1 rd2) mv
        [("clk", LVec.ofNat 1 0), ("wen", LVec.ofNat 1 0), ("waddr", LVec.ofNat 6 1),
         ("raddr1", LVec.ofNat 6 1), ("raddr2", LVec.ofNat 6 2), ("wdata", wd)] =
      .ok (picorv32_regs_quiet_view wd (memRd mv "regs" (some 30) 32)
        (memRd mv "regs" (some 29) 32), mv) := by
  obtain ⟨E', hE', hP, hO⟩ := (show SeqDesignI regs.e by sv_structure)
  rw [hE] at hE'
  cases hE'
  sv_seq_inst [regs.e, regs.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (picorv32_regs_quiet_view wd rd1 rd2) mv
      [("clk", LVec.ofNat 1 0), ("wen", LVec.ofNat 1 0), ("waddr", LVec.ofNat 6 1),
       ("raddr1", LVec.ofNat 6 1), ("raddr2", LVec.ofNat 6 2), ("wdata", wd)] using hE
      [picorv32_regs_quiet_view, hwd, hrd1, hrd2, regs_evalSized_not_signal]
  rw [hcyc]
  simp [picorv32_regs_quiet_view, regs_evalSized_not_signal, memRd, memIss, commitMemV,
    isPosedge_self, seqK_index?, hmv, LVec.resizeU_of_width]
  all_goals simp [MemShape.inRange, LVec.resizeU_of_width, hmv]

/-! A rising-edge write row of the loaded register-file leaf.  The source uses
    `~waddr[4:0]`, so address one writes memory index 30.  The simultaneous
    read of that index observes the NBA value, while the read of index 29
    observes its previous memory value. -/

private def picorv32_regs_write_view (c wen wa ra1 ra2 wd rd1 rd2 : LVec) : SvState :=
  [("clk", c), ("wen", wen), ("waddr", wa), ("raddr1", ra1), ("raddr2", ra2), ("wdata", wd),
   ("rdata1", rd1), ("rdata2", rd2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem picorv32_regs_write_read_step {E : CoreMemDesign} (hE : regs.e = .ok E)
    (wd rd1 rd2 : LVec) (mv : MemV) (hwd : wd.width = 32)
    (hrd1 : rd1.width = 32) (hrd2 : rd2.width = 32)
    (hmv : ∀ k, (mv "regs" k).width = 32) :
    E.slotV (picorv32_regs_write_view (LVec.ofNat 1 0) (LVec.ofNat 1 1)
        (LVec.ofNat 6 1) (LVec.ofNat 6 1) (LVec.ofNat 6 2) wd rd1 rd2) mv
        [("clk", LVec.ofNat 1 1), ("wen", LVec.ofNat 1 1), ("waddr", LVec.ofNat 6 1),
         ("raddr1", LVec.ofNat 6 1), ("raddr2", LVec.ofNat 6 2), ("wdata", wd)] =
      .ok (picorv32_regs_write_view (LVec.ofNat 1 1) (LVec.ofNat 1 1)
        (LVec.ofNat 6 1) (LVec.ofNat 6 1) (LVec.ofNat 6 2) wd wd
        (memRd mv "regs" (some 29) 32),
        memWrite mv "regs" (some 30) wd) := by
  obtain ⟨E', hE', hP, hO⟩ := (show SeqDesignI regs.e by sv_structure)
  rw [hE] at hE'
  cases hE'
  sv_seq_inst [regs.e, regs.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (picorv32_regs_write_view (LVec.ofNat 1 0) (LVec.ofNat 1 1)
      (LVec.ofNat 6 1) (LVec.ofNat 6 1) (LVec.ofNat 6 2) wd rd1 rd2) mv
      [("clk", LVec.ofNat 1 1), ("wen", LVec.ofNat 1 1), ("waddr", LVec.ofNat 6 1),
       ("raddr1", LVec.ofNat 6 1), ("raddr2", LVec.ofNat 6 2), ("wdata", wd)] using hE
      [picorv32_regs_write_view, hwd, hrd1, hrd2, regs_evalSized_not_signal,
       LVec.xVec]
  rw [hcyc]
  have hpos : isPosedge (LVec.ofBitVec 0#1).bits[0] (LVec.ofBitVec 1#1).bits[0] = true := by rfl
  simp [hpos, picorv32_regs_write_view, memRd, memIss, commitMemV,
    seqK_index?, hmv, LVec.resizeU_of_width]
  all_goals simp [MemShape.inRange, LVec.resizeU_of_width, hmv, isPosedge,
    Array.any, Array.anyM, Array.anyM.loop]
  all_goals
    change (Array.ofFn (n := 32) (fun _ : Fin 32 => Logic.l0)).any
      (fun a => a == Logic.l1) 0 1 = false
    simp [Array.any, Array.anyM, Array.anyM.loop]

/-! A concrete zero-register row of the loaded register-file leaf.  The
    source's `~address[4:0]` maps address zero to the out-of-range label 31.
    E's exact §11.5.1 rule therefore makes the write a no-op and both reads
    all-x for the declared 32-bit element width. -/

private def picorv32_regs_zero_view (c wen wa ra1 ra2 wd rd1 rd2 : LVec) : SvState :=
  [("clk", c), ("wen", wen), ("waddr", wa), ("raddr1", ra1), ("raddr2", ra2), ("wdata", wd),
   ("rdata1", rd1), ("rdata2", rd2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem picorv32_regs_zero_write_step {E : CoreMemDesign} (hE : regs.e = .ok E)
    (wd rd1 rd2 : LVec) (mv : MemV) (hwd : wd.width = 32)
    (hrd1 : rd1.width = 32) (hrd2 : rd2.width = 32)
    (hmv : ∀ k, (mv "regs" k).width = 32) :
    E.slotV (picorv32_regs_zero_view (LVec.ofNat 1 0) (LVec.ofNat 1 1)
        (LVec.ofNat 6 0) (LVec.ofNat 6 0) (LVec.ofNat 6 0) wd rd1 rd2) mv
        [("clk", LVec.ofNat 1 1), ("wen", LVec.ofNat 1 1), ("waddr", LVec.ofNat 6 0),
         ("raddr1", LVec.ofNat 6 0), ("raddr2", LVec.ofNat 6 0), ("wdata", wd)] =
      .ok (picorv32_regs_zero_view (LVec.ofNat 1 1) (LVec.ofNat 1 1)
        (LVec.ofNat 6 0) (LVec.ofNat 6 0) (LVec.ofNat 6 0) wd
        (LVec.xVec 32) (LVec.xVec 32), mv) := by
  obtain ⟨E', hE', hP, hO⟩ := (show SeqDesignI regs.e by sv_structure)
  rw [hE] at hE'
  cases hE'
  sv_seq_inst [regs.e, regs.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (picorv32_regs_zero_view (LVec.ofNat 1 0) (LVec.ofNat 1 1)
      (LVec.ofNat 6 0) (LVec.ofNat 6 0) (LVec.ofNat 6 0) wd rd1 rd2) mv
      [("clk", LVec.ofNat 1 1), ("wen", LVec.ofNat 1 1), ("waddr", LVec.ofNat 6 0),
       ("raddr1", LVec.ofNat 6 0), ("raddr2", LVec.ofNat 6 0), ("wdata", wd)] using hE
      [picorv32_regs_zero_view, hwd, hrd1, hrd2, regs_evalSized_not_signal]
  rw [hcyc]
  have hpos : isPosedge (LVec.ofBitVec 0#1).bits[0] (LVec.ofBitVec 1#1).bits[0] = true := by rfl
  simp [hpos, picorv32_regs_zero_view, memRd, memIss, commitMemV,
    seqK_index?, hmv, LVec.resizeU_of_width]
  all_goals simp [MemShape.inRange, LVec.resizeU_of_width, hmv, isPosedge,
    Array.any, Array.anyM, Array.anyM.loop]

/-! The executor-side no-write corollary is restricted to a known zero write-enable.
    Unknown write-enable behavior belongs to the relation and is not asserted by this theorem. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem picorv32_regs_zero_wen_step {E : CoreMemDesign} (hE : regs.e = .ok E)
    (wd rd1 rd2 : LVec) (mv : MemV) (hwd : wd.width = 32)
    (hrd1 : rd1.width = 32) (hrd2 : rd2.width = 32)
    (hmv : ∀ k, (mv "regs" k).width = 32) :
    E.slotV (picorv32_regs_write_view (LVec.ofNat 1 0) (LVec.ofNat 1 0)
        (LVec.ofNat 6 1) (LVec.ofNat 6 1) (LVec.ofNat 6 2) wd rd1 rd2) mv
        [("clk", LVec.ofNat 1 1), ("wen", LVec.ofNat 1 0), ("waddr", LVec.ofNat 6 1),
         ("raddr1", LVec.ofNat 6 1), ("raddr2", LVec.ofNat 6 2), ("wdata", wd)] =
      .ok (picorv32_regs_write_view (LVec.ofNat 1 1) (LVec.ofNat 1 0)
        (LVec.ofNat 6 1) (LVec.ofNat 6 1) (LVec.ofNat 6 2) wd
        (memRd mv "regs" (some 30) 32) (memRd mv "regs" (some 29) 32), mv) := by
  obtain ⟨E', hE', hP, hO⟩ := (show SeqDesignI regs.e by sv_structure)
  rw [hE] at hE'
  cases hE'
  sv_seq_inst [regs.e, regs.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (picorv32_regs_write_view (LVec.ofNat 1 0) (LVec.ofNat 1 0)
      (LVec.ofNat 6 1) (LVec.ofNat 6 1) (LVec.ofNat 6 2) wd rd1 rd2) mv
      [("clk", LVec.ofNat 1 1), ("wen", LVec.ofNat 1 0), ("waddr", LVec.ofNat 6 1),
       ("raddr1", LVec.ofNat 6 1), ("raddr2", LVec.ofNat 6 2), ("wdata", wd)] using hE
      [picorv32_regs_write_view, hwd, hrd1, hrd2, regs_evalSized_not_signal,
       LVec.xVec,
       (by
          change (Array.ofFn (n := 32) (fun _ : Fin 32 => Logic.l0)).any
            (fun a => a == Logic.l1) 0 1 = false
          exact regs_zero_scan)]
  rw [hcyc]
  have hx : (LVec.ofNat 1 0).condTrue = false := by
    simp [LVec.condTrue, LVec.ofNat, Array.any, Array.anyM, Array.anyM.loop]
  have hpos : isPosedge (LVec.ofBitVec 0#1).bits[0] (LVec.ofBitVec 1#1).bits[0] = true := by rfl
  simp [hx, hpos, picorv32_regs_write_view, memRd, memIss, commitMemV,
    seqK_index?, hmv, LVec.resizeU_of_width]
  all_goals simp [MemShape.inRange, LVec.resizeU_of_width, hmv, isPosedge,
    Array.any, Array.anyM, Array.anyM.loop]
  all_goals try
    change (Array.ofFn (n := 32) (fun _ : Fin 32 => Logic.l0)).any
      (fun a => a == Logic.l1) 0 1 = false
    simp [Array.any, Array.anyM, Array.anyM.loop]

#print axioms picorv32_regs_wdata_undriven
#print axioms picorv32_regs_quiet_read_step
#print axioms picorv32_regs_write_read_step
#print axioms picorv32_regs_zero_write_step
#print axioms picorv32_regs_zero_wen_step

/-! The zero-enable boundary is universal over the loaded leaf's address and
data vectors.  The concrete rows above pin the complement-address mapping.
This theorem carries the same fact for every typed read/write address and
value, which is the memory-preservation clause needed by a whole-core
register-file invariant. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem picorv32_regs_zero_wen_universal {E : CoreMemDesign} (hE : regs.e = .ok E)
    (wa ra1 ra2 wd rd1 rd2 : LVec) (mv : MemV)
    (hwa : wa.width = 6) (hra1 : ra1.width = 6) (hra2 : ra2.width = 6)
    (hwd : wd.width = 32) (hrd1 : rd1.width = 32) (hrd2 : rd2.width = 32)
    (hmv : ∀ k, (mv "regs" k).width = 32) :
    ∃ v', E.slotV (picorv32_regs_write_view (LVec.ofNat 1 0) (LVec.ofNat 1 0)
        wa ra1 ra2 wd rd1 rd2) mv
        [("clk", LVec.ofNat 1 1), ("wen", LVec.ofNat 1 0), ("waddr", wa),
         ("raddr1", ra1), ("raddr2", ra2), ("wdata", wd)] = .ok (v', mv) := by
  obtain ⟨E', hE', hP, hO⟩ := (show SeqDesignI regs.e by sv_structure)
  rw [hE] at hE'
  cases hE'
  sv_seq_inst [regs.e, regs.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (picorv32_regs_write_view (LVec.ofNat 1 0) (LVec.ofNat 1 0)
      wa ra1 ra2 wd rd1 rd2) mv
      [("clk", LVec.ofNat 1 1), ("wen", LVec.ofNat 1 0), ("waddr", wa),
       ("raddr1", ra1), ("raddr2", ra2), ("wdata", wd)] using hE
      [picorv32_regs_write_view, hwa, hra1, hra2, hwd, hrd1, hrd2,
       regs_evalSized_not_signal, LVec.xVec]
  rw [hcyc]
  refine ⟨_, rfl⟩

#print axioms picorv32_regs_zero_wen_universal

end Examples.«system-verilog».cores.picorv32
