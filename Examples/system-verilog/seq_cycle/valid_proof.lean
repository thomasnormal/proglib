import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleTactic

/-!
# A valid/ready register with synchronous reset and continuous outputs, on the ordinary E route, over every run

The census design `seq_valid_chain/valid_chain_profile` (flip-flops and continuous assigns, the largest class):

```systemverilog
module valid_chain_profile #(parameter integer W = 8) (input logic clk, rst, valid_i, ready_i,
    input logic [W-1:0] data_i, output logic valid_o, output logic [W-1:0] data_o);
  logic valid_q; logic [W-1:0] data_q;
  always_ff @(posedge clk) begin
    if (rst) begin valid_q <= 1'b0; data_q <= '0; end
    else if (ready_i) begin valid_q <= valid_i; data_q <= data_i; end
  end
  assign valid_o = valid_q;
  assign data_o = data_q;
endmodule
```

1. **Structure** (`vc_structure`): the instantiation at every `1 ≤ W < 2^30`, in the clocked profile (an edge
   process and two continuous assigns in topological order).
2. **Cycle equations** (`vc_cycle`): the outputs in the pre sample are the old registers (the assigns settled); in the
   post sample the registers and the outputs are `vcNext` of the pre sample (cleared on reset, loaded when ready,
   held otherwise).
3. **The claim** (`vc_runs`): in every run, from every coherent state, on every typed stimulus, through the OUTPUT ports
   (the continuous assigns): a cycle that sees `rst = 1` shows `valid_o = 0`, `data_o = 0`; one that sees `rst = 0`,
   `ready_i = 1` shows the inputs `valid_i`, `data_i` it saw; one that sees `rst = 0`, `ready_i = 0` shows what the
   previous cycle showed. The decisions read known values (rule 4's cheap sufficient condition).

Oracle: Icarus Verilog 12.0 (stable), a testbench outside the repository.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.valid_proof

load_design_sv2 vc from "Examples/system-verilog/seq_valid_chain/valid_chain_profile.sv.json"

-- A run on the route at `W = 8` (compiled): reset, load 0x5a, hold, load 0x3c.
#guard (match vc.e 8 with
  | .ok E => match runCoreMemRows E E.initial (cycleRows "clk"
      [[("rst", .ofNat 1 1), ("valid_i", .ofNat 1 0), ("ready_i", .ofNat 1 0), ("data_i", .ofNat 8 0)],
       [("rst", .ofNat 1 0), ("valid_i", .ofNat 1 1), ("ready_i", .ofNat 1 1), ("data_i", .ofNat 8 0x5a)],
       [("rst", .ofNat 1 0), ("valid_i", .ofNat 1 0), ("ready_i", .ofNat 1 0), ("data_i", .ofNat 8 0xff)],
       [("rst", .ofNat 1 0), ("valid_i", .ofNat 1 1), ("ready_i", .ofNat 1 1), ("data_i", .ofNat 8 0x3c)]]) with
    | .ok rows => (cyclePairs rows).map (fun pp => SvState.showSignal (CoreMemState.view E pp.2) "valid_o" ++ ":" ++
        SvState.showSignal (CoreMemState.view E pp.2) "data_o") ==
        ["0:00000000", "1:01011010", "1:01011010", "1:00111100"]
    | _ => false
  | _ => false)

/-! ## 1. Structure -/

set_option maxHeartbeats 1000000 in
theorem vc_structure (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) :
    SeqDesign (vc.e W) "clk" := by
  cases hE : vc.e W with
  | ok E =>
      sv_seq_inst [vc.e, vc.pdesign] at hE
      subst hE
      exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
  | timeout => sv_seq_inst [vc.e, vc.pdesign] at hE
  | unsupported m => sv_seq_inst [vc.e, vc.pdesign] at hE

/-- **The interface**: the ports with their declared widths, in declaration order. -/
theorem vc_ports (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) :
    SeqPorts (vc.e W) [("clk", 1), ("rst", 1), ("valid_i", 1), ("ready_i", 1), ("data_i", W)] [("valid_o", 1), ("data_o", W)] := by
  obtain ⟨E, hE, -, -⟩ := vc_structure W h1 h2
  refine ⟨E, hE, ?_⟩
  sv_seq_inst [vc.e, vc.pdesign] at hE
  subst hE
  constructor <;> sv_seq_ports

/-! ## 2. The cycle equations -/

/-- A register's next value: `zero` on reset, `x` when ready, else `old` (the route's `if` reads `condTrue`). -/
def vcNext (r ry x old zero : LVec) : LVec :=
  if r.condTrue then zero else if ry.condTrue then x else old

/-- The input an entry applies: its own value, or the held one. -/
def applied (d : SvState) (n : String) (old : LVec) : LVec := (SvState.lookup d n).getD old

/-- The shape of a view of this design. -/
def vcView (c r vi ry di vo dout vq dq : LVec) : SvState :=
  [("clk", c), ("rst", r), ("valid_i", vi), ("ready_i", ry), ("data_i", di), ("valid_o", vo), ("data_o", dout),
    ("valid_q", vq), ("data_q", dq)]

set_option maxHeartbeats 4000000 in
/-- **The cycle equations**: the pre sample holds the applied inputs and the old registers on the outputs; the post
sample holds `vcNext` of the pre sample in the registers and on the outputs. -/
theorem vc_cycle (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : vc.e W = .ok E)
    (c r vi ry di vo dout vq dq : LVec) (hr : r.width = 1) (hvi : vi.width = 1) (hry : ry.width = 1)
    (hdi : di.width = W) (hdout : dout.width = W) (hvq : vq.width = 1) (hdq : dq.width = W)
    (d : SvState) (hd : E.DataTyped "clk" d) :
    let r' := applied d "rst" r
    let vi' := applied d "valid_i" vi
    let ry' := applied d "ready_i" ry
    let di' := applied d "data_i" di
    r'.width = 1 ∧ vi'.width = 1 ∧ ry'.width = 1 ∧ di'.width = W ∧
      E.cycleV "clk" (vcView c r vi ry di vo dout vq dq) d =
        .ok (vcView ⟨#[.l0]⟩ r' vi' ry' di' vq dq vq dq,
          vcView ⟨#[.l1]⟩ r' vi' ry' di' (vcNext r' ry' vi' vq ⟨#[.l0]⟩) (vcNext r' ry' di' dq (LVec.ofBitVec 0#W))
            (vcNext r' ry' vi' vq ⟨#[.l0]⟩) (vcNext r' ry' di' dq (LVec.ofBitVec 0#W))) := by
  intro r' vi' ry' di'
  sv_seq_inst [vc.e, vc.pdesign] at hE
  -- the widths of the applied inputs (the entry is typed)
  have hw : ∀ n old w, ((n = "rst" ∨ n = "valid_i" ∨ n = "ready_i") ∧ w = 1 ∨ n = "data_i" ∧ w = W) →
      old.width = w → (applied d n old).width = w := by
    intro n old w hn hold
    unfold applied
    cases hl : SvState.lookup d n with
    | none => exact hold
    | some v =>
        have hin : n ∈ E.scalar.toDesign2.inputNames.toList := by
          subst hE; rcases hn with ⟨rfl | rfl | rfl, -⟩ | ⟨rfl, -⟩ <;> simp [Elab.toDesign2, Design2.inputNames]
        have hdw : E.scalar.toDesign2.declWidth n = some w := by
          subst hE; rcases hn with ⟨rfl | rfl | rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [Elab.toDesign2, Design2.declWidth]
        have := hd n v hin (by
          rcases hn with ⟨rfl | rfl | rfl, -⟩ | ⟨rfl, -⟩ <;> simp [lowEntry, SvState.lookup, hl])
        rw [hdw] at this
        simp only [Option.getD_some]
        exact (Option.some.inj this).symm
  have hrw : r'.width = 1 := hw "rst" r 1 (Or.inl ⟨Or.inl rfl, rfl⟩) hr
  have hviw : vi'.width = 1 := hw "valid_i" vi 1 (Or.inl ⟨Or.inr (Or.inl rfl), rfl⟩) hvi
  have hryw : ry'.width = 1 := hw "ready_i" ry 1 (Or.inl ⟨Or.inr (Or.inr rfl), rfl⟩) hry
  have hdiw : di'.width = W := hw "data_i" di W (Or.inr ⟨rfl, rfl⟩) hdi
  refine ⟨hrw, hviw, hryw, hdiw, ?_⟩
  -- the cycle reads the entry only through the inputs it applies
  rw [CoreMemDesign.cycleV_congr_data E "clk" _ d
    [("rst", r'), ("valid_i", vi'), ("ready_i", ry'), ("data_i", di')] (by
      subst hE
      simp only [r', vi', ry', di', applied, applyInputs2, Elab.toDesign2, lowEntry, vcView]
      cases h1 : SvState.lookup d "rst" <;> cases h2 : SvState.lookup d "valid_i" <;>
        cases h3 : SvState.lookup d "ready_i" <;> cases h4 : SvState.lookup d "data_i" <;>
        simp [h1, h2, h3, h4, SvState.lookup, SvState.set])]
  clear_value r' vi' ry' di'
  unfold vcView
  by_cases hr1 : r'.condTrue = true
  · sv_seq_cycle hcyc : E.cycleV "clk" [("clk", c), ("rst", r), ("valid_i", vi), ("ready_i", ry), ("data_i", di),
        ("valid_o", vo), ("data_o", dout), ("valid_q", vq), ("data_q", dq)]
        [("rst", r'), ("valid_i", vi'), ("ready_i", ry'), ("data_i", di')] using hE
        [hr1, hrw, hviw, hryw, hdiw, hr, hvi, hry, hdi, hdout, hvq, hdq]
    rw [hcyc, seqE_insertAt_zero (show (⟨#[.l0]⟩ : LVec).width = vq.width by rw [hvq]; rfl),
      seqE_insertAt_zero (show (LVec.ofBitVec 0#W).width = dq.width by simp [hdq])]
    simp [vcNext, hr1]
  · by_cases hy1 : ry'.condTrue = true
    · sv_seq_cycle hcyc : E.cycleV "clk" [("clk", c), ("rst", r), ("valid_i", vi), ("ready_i", ry),
          ("data_i", di), ("valid_o", vo), ("data_o", dout), ("valid_q", vq), ("data_q", dq)]
          [("rst", r'), ("valid_i", vi'), ("ready_i", ry'), ("data_i", di')] using hE
          [hr1, hy1, hrw, hviw, hryw, hdiw, hr, hvi, hry, hdi, hdout, hvq, hdq]
      rw [hcyc]
      simp [vcNext, hr1, hy1, seqE_insertAt_zero, hvq, hdq, hviw, hdiw]
    · sv_seq_cycle hcyc : E.cycleV "clk" [("clk", c), ("rst", r), ("valid_i", vi), ("ready_i", ry),
          ("data_i", di), ("valid_o", vo), ("data_o", dout), ("valid_q", vq), ("data_q", dq)]
          [("rst", r'), ("valid_i", vi'), ("ready_i", ry'), ("data_i", di')] using hE
          [hr1, hy1, hrw, hviw, hryw, hdiw, hr, hvi, hry, hdi, hdout, hvq, hdq]
      rw [hcyc]
      simp [vcNext, hr1, hy1]


/-! ## 3. The claim, over every run -/

/-- **The register's claim** through its output ports, about the samples of a run: a cycle that sees `rst = 1` shows
`valid_o = 0`, `data_o = 0`; one that sees `rst = 0`, `ready_i = 1` shows the `valid_i`, `data_i` it saw; one that
sees `rst = 0`, `ready_i = 0` shows what the previous cycle showed. -/
def VcClaim (W : Nat) (tr : List (SvState × SvState)) : Prop :=
  ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc →
    (SvState.lookup pc.1 "rst" = some (LVec.ofNat 1 1) →
      SvState.lookup pc.2 "valid_o" = some (LVec.ofNat 1 0) ∧ SvState.lookup pc.2 "data_o" = some (LVec.ofNat W 0)) ∧
    (SvState.lookup pc.1 "rst" = some (LVec.ofNat 1 0) → SvState.lookup pc.1 "ready_i" = some (LVec.ofNat 1 1) →
      SvState.lookup pc.2 "valid_o" = SvState.lookup pc.1 "valid_i" ∧
        SvState.lookup pc.2 "data_o" = SvState.lookup pc.1 "data_i") ∧
    (SvState.lookup pc.1 "rst" = some (LVec.ofNat 1 0) → SvState.lookup pc.1 "ready_i" = some (LVec.ofNat 1 0) →
      ∀ (c' : Nat) (pp : SvState × SvState), c = c' + 1 → tr[c']? = some pp →
        SvState.lookup pc.2 "valid_o" = SvState.lookup pp.2 "valid_o" ∧
          SvState.lookup pc.2 "data_o" = SvState.lookup pp.2 "data_o")

theorem vcNext_width {w : Nat} {r ry x old zero : LVec} (hx : x.width = w) (ho : old.width = w)
    (hz : zero.width = w) : (vcNext r ry x old zero).width = w := by
  unfold vcNext
  split
  · exact hz
  · split
    · exact hx
    · exact ho

/-- One cycle of a run of the register: its applied inputs and the registers it starts from. -/
structure VCyc (W : Nat) (pp : SvState × SvState) (r vi ry di vq dq : LVec) : Prop where
  pre : pp.1 = vcView ⟨#[.l0]⟩ r vi ry di vq dq vq dq
  post : pp.2 = vcView ⟨#[.l1]⟩ r vi ry di (vcNext r ry vi vq ⟨#[.l0]⟩) (vcNext r ry di dq (LVec.ofBitVec 0#W))
    (vcNext r ry vi vq ⟨#[.l0]⟩) (vcNext r ry di dq (LVec.ofBitVec 0#W))
  wr : r.width = 1
  wvi : vi.width = 1
  wry : ry.width = 1
  wdi : di.width = W
  wvq : vq.width = 1
  wdq : dq.width = W

theorem VCyc.unique {W : Nat} {pp : SvState × SvState} {r vi ry di vq dq r' vi' ry' di' vq' dq' : LVec}
    (h : VCyc W pp r vi ry di vq dq) (h' : VCyc W pp r' vi' ry' di' vq' dq') :
    r = r' ∧ vi = vi' ∧ ry = ry' ∧ di = di' ∧ vq = vq' ∧ dq = dq' := by
  have := h.pre.symm.trans h'.pre
  simp only [vcView, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at this
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1⟩

set_option maxHeartbeats 1000000 in
/-- **The trace of a run**: every cycle is a `VCyc`; every later cycle starts from the registers its predecessor's
post sample shows. -/
theorem vc_trace (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : vc.e W = .ok E) :
    ∀ (ins : List SvState) (c0 r0 vi0 ry0 di0 vo0 do0 vq0 dq0 : LVec), r0.width = 1 → vi0.width = 1 →
      ry0.width = 1 → di0.width = W → do0.width = W → vq0.width = 1 → dq0.width = W →
      (∀ d ∈ ins, E.DataTyped "clk" d) → ∀ tr,
      E.runV "clk" (vcView c0 r0 vi0 ry0 di0 vo0 do0 vq0 dq0) ins = .ok tr →
      ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc → ∃ r vi ry di vq dq, VCyc W pc r vi ry di vq dq ∧
        (c = 0 → vq = vq0 ∧ dq = dq0) ∧ ∀ (c' : Nat) (pc' : SvState × SvState) (r' vi' ry' di' vq' dq' : LVec), c = c' + 1 → tr[c']? = some pc' →
          VCyc W pc' r' vi' ry' di' vq' dq' →
            vq = vcNext r' ry' vi' vq' ⟨#[.l0]⟩ ∧ dq = vcNext r' ry' di' dq' (LVec.ofBitVec 0#W)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, tr, htr => by
      simp only [CoreMemDesign.runV, Res.ok.injEq] at htr
      subst htr
      intro c pc hc
      simp at hc
  | d :: ds, c0, r0, vi0, ry0, di0, vo0, do0, vq0, dq0, hr0, hvi0, hry0, hdi0, hdo0, hvq0, hdq0, hd, tr, htr => by
      obtain ⟨hrw, hviw, hryw, hdiw, hcyc⟩ :=
        vc_cycle W h1 h2 hE c0 r0 vi0 ry0 di0 vo0 do0 vq0 dq0 hr0 hvi0 hry0 hdi0 hdo0 hvq0 hdq0 d (hd d (by simp))
      simp only [CoreMemDesign.runV, hcyc, Res.ok_bind, Res.bind_eq_ok, Res.ok.injEq] at htr
      obtain ⟨rest, hrest, rfl⟩ := htr
      have hvqn := vcNext_width (r := applied d "rst" r0) (ry := applied d "ready_i" ry0) hviw hvq0
        (show (⟨#[.l0]⟩ : LVec).width = 1 from rfl)
      have hdqn := vcNext_width (r := applied d "rst" r0) (ry := applied d "ready_i" ry0) hdiw hdq0
        (show (LVec.ofBitVec 0#W).width = W by simp)
      have hcyc0 : VCyc W (vcView ⟨#[.l0]⟩ (applied d "rst" r0) (applied d "valid_i" vi0)
          (applied d "ready_i" ry0) (applied d "data_i" di0) vq0 dq0 vq0 dq0, vcView ⟨#[.l1]⟩
          (applied d "rst" r0) (applied d "valid_i" vi0) (applied d "ready_i" ry0) (applied d "data_i" di0)
          (vcNext (applied d "rst" r0) (applied d "ready_i" ry0) (applied d "valid_i" vi0) vq0 ⟨#[.l0]⟩)
          (vcNext (applied d "rst" r0) (applied d "ready_i" ry0) (applied d "data_i" di0) dq0 (LVec.ofBitVec 0#W))
          (vcNext (applied d "rst" r0) (applied d "ready_i" ry0) (applied d "valid_i" vi0) vq0 ⟨#[.l0]⟩)
          (vcNext (applied d "rst" r0) (applied d "ready_i" ry0) (applied d "data_i" di0) dq0 (LVec.ofBitVec 0#W)))
          (applied d "rst" r0) (applied d "valid_i" vi0) (applied d "ready_i" ry0) (applied d "data_i" di0) vq0 dq0 :=
        ⟨rfl, rfl, hrw, hviw, hryw, hdiw, hvq0, hdq0⟩
      have ih := vc_trace W h1 h2 hE ds _ _ _ _ _ _ _ _ _ hrw hviw hryw hdiw hdqn hvqn hdqn
        (fun d' hd' => hd d' (by simp [hd'])) rest hrest
      intro c pc hc
      cases c with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst hc
          exact ⟨_, _, _, _, _, _, hcyc0, fun _ => ⟨rfl, rfl⟩,
            fun c' _ _ _ _ _ _ _ h _ _ => absurd h (by omega)⟩
      | succ c =>
          simp only [List.getElem?_cons_succ] at hc
          obtain ⟨r, vi, ry, di, vq, dq, hpc, h0, hlink⟩ := ih c pc hc
          refine ⟨r, vi, ry, di, vq, dq, hpc, fun h => absurd h (by omega),
            fun c' pc' r'' vi'' ry'' di'' vq'' dq'' hcc hpc' hcyc' => ?_⟩
          obtain rfl : c' = c := by omega
          cases c' with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hpc'
              subst hpc'
              obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hcyc0.unique hcyc'
              exact h0 rfl
          | succ c'' =>
              simp only [List.getElem?_cons_succ] at hpc'
              exact hlink c'' pc' r'' vi'' ry'' di'' vq'' dq'' rfl hpc' hcyc'


/-- **The claim from the trace.** -/
theorem vcClaim_of_trace (W : Nat) (tr : List (SvState × SvState))
    (htr : ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc → ∃ r vi ry di vq dq,
      VCyc W pc r vi ry di vq dq ∧ ∀ (c' : Nat) (pc' : SvState × SvState) (r' vi' ry' di' vq' dq' : LVec),
        c = c' + 1 → tr[c']? = some pc' → VCyc W pc' r' vi' ry' di' vq' dq' →
          vq = vcNext r' ry' vi' vq' ⟨#[.l0]⟩ ∧ dq = vcNext r' ry' di' dq' (LVec.ofBitVec 0#W)) :
    VcClaim W tr := by
  intro c pc hc
  obtain ⟨r, vi, ry, di, vq, dq, hcyc, hlink⟩ := htr c pc hc
  have hpre : ∀ n, SvState.lookup pc.1 n = SvState.lookup (vcView ⟨#[.l0]⟩ r vi ry di vq dq vq dq) n := by
    intro n; rw [hcyc.pre]
  have hpost := hcyc.post
  refine ⟨fun hr => ?_, fun hr hy => ?_, fun hr hy c' pp hcc hpp => ?_⟩
  · rw [hpre] at hr
    simp only [vcView, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
      Option.some.injEq] at hr
    subst hr
    rw [hpost]
    simp [vcView, SvState.lookup, vcNext]
    decide
  · rw [hpre] at hr hy
    simp only [vcView, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
      Option.some.injEq] at hr hy
    subst hr hy
    rw [hpost, hcyc.pre]
    simp [vcView, SvState.lookup, vcNext]
  · rw [hpre] at hr hy
    simp only [vcView, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
      Option.some.injEq] at hr hy
    subst hr hy
    obtain ⟨r', vi', ry', di', vq', dq', hcyc', -⟩ := htr c' pp hpp
    obtain ⟨hvq, hdq⟩ := hlink c' pp r' vi' ry' di' vq' dq' hcc hpp hcyc'
    rw [hpost, hcyc'.post]
    simp [vcView, SvState.lookup, vcNext, hvq, hdq]

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state, on every typed stimulus, the outputs show 0
after a reset cycle, the inputs after a loading cycle, and the previous outputs after a holding cycle. -/
theorem vc_runs (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) : SeqRuns (vc.e W) "clk" (VcClaim W) := by
  obtain ⟨E, hE, hP, -⟩ := vc_structure W h1 h2
  have hE0 := hE
  sv_seq_inst [vc.e, vc.pdesign] at hE0
  refine SeqRuns.intro hE hP (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
    (fun v => ∃ c r vi ry di vo dout vq dq, v = vcView c r vi ry di vo dout vq dq ∧ r.width = 1 ∧
      vi.width = 1 ∧ ry.width = 1 ∧ di.width = W ∧ dout.width = W ∧ vq.width = 1 ∧ dq.width = W) ?_ ?_ ?_
  · intro v hs
    subst hE0
    obtain ⟨hk, hw⟩ := hs
    rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨⟨n5, x5⟩, _ |
      ⟨⟨n6, x6⟩, _ | ⟨⟨n7, x7⟩, _ | ⟨⟨n8, x8⟩, _ | ⟨⟨n9, x9⟩, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at hk hw
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hk
    exact ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, rfl, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1,
      hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2⟩
  · rintro v d ⟨c, r, vi, ry, di, vo, dout, vq, dq, rfl, hr, hvi, hry, hdi, hdout, hvq, hdq⟩ hd
    obtain ⟨hrw, hviw, hryw, hdiw, hcyc⟩ := vc_cycle W h1 h2 hE c r vi ry di vo dout vq dq hr hvi hry hdi hdout
      hvq hdq d hd
    exact ⟨_, _, hcyc, ⟨_, _, _, _, _, _, _, _, _, rfl, hrw, hviw, hryw, hdiw,
      vcNext_width hdiw hdq (by simp), vcNext_width hviw hvq (show (⟨#[.l0]⟩ : LVec).width = 1 from rfl),
      vcNext_width hdiw hdq (by simp)⟩⟩
  · rintro v ins tr ⟨c, r, vi, ry, di, vo, dout, vq, dq, rfl, hr, hvi, hry, hdi, hdout, hvq, hdq⟩ hd htr
    refine vcClaim_of_trace W tr fun c' pc hc => ?_
    obtain ⟨r1, vi1, ry1, di1, vq1, dq1, hcyc, -, hlink⟩ :=
      vc_trace W h1 h2 hE ins c r vi ry di vo dout vq dq hr hvi hry hdi hdout hvq hdq hd tr htr c' pc hc
    exact ⟨r1, vi1, ry1, di1, vq1, dq1, hcyc, hlink⟩

#print axioms vc_structure
#print axioms vc_ports
#print axioms vc_cycle
#print axioms vc_runs

end Examples.«system-verilog».seq_cycle.valid_proof
