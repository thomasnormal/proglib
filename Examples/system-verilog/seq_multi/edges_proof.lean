import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# Falling edges: a falling-edge register, and a register on each edge of one clock, over every sequence of instants

Two designs whose events include a falling clock edge (outside the single-clock profile `posedge clk`; in the instant
view `{negedge clk}` is an instant of its own):

```systemverilog
module negedge_e (input logic clk, input logic d, output logic q);   // sem2/negedge_e
  always_ff @(negedge clk) q <= d;
endmodule

module ddr_reg #(parameter int W = 4) (input logic clk, input logic [W-1:0] d,   // seq_multi/ddr_reg
    output logic [W-1:0] qp, qn);
  always_ff @(posedge clk) qp <= d;
  always_ff @(negedge clk) qn <= d;
endmodule
```

For each: the instant structure, the computed events, the row equations from the mirror, and the claim over every
sequence of instants and data rows keeping the input discipline: the register of a falling edge takes the value its
data input had before the fall (§9.4.2: 1→0, 1→x, 1→z, x→0, z→0 are falls) and holds otherwise; the double-data-rate
pair does so on each edge, a rising edge never touching the falling register and a falling edge never the rising one.

Oracle: Icarus Verilog 12.0 (stable), a testbench outside the repository: 30 rows per design in the `#guard`s below
(falls and rises from 1, 0, x and z, data rows that move the clock in a direction no process watches).
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_multi.edges_proof

load_design_sv2 ng from "Examples/system-verilog/sem2/negedge_e/negedge_e.sv.json"
load_design_sv2 dd from "Examples/system-verilog/seq_multi/ddr_reg/ddr_reg.sv.json"

-- Icarus Verilog 12.0's samples of a run (every signal, after each row), from the x start.
#guard (match ng.e with
  | .ok E => match runCoreMemRows E E.initial
      [[("d", ⟨#[.l1]⟩), ("clk", ⟨#[.lz]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l0]⟩), ("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l1]⟩)],
   [("d", ⟨#[.l1]⟩), ("clk", ⟨#[.lz]⟩)],
   [("clk", ⟨#[.lx]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l0]⟩), ("clk", ⟨#[.lz]⟩)],
   [("d", ⟨#[.l0]⟩)],
   [("d", ⟨#[.lx]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("clk", ⟨#[.lx]⟩)],
   [("d", ⟨#[.l1]⟩)],
   [("d", ⟨#[.l1]⟩), ("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l1]⟩), ("clk", ⟨#[.l1]⟩)],
   [("d", ⟨#[.l1]⟩)],
   [("d", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l0]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l1]⟩), ("clk", ⟨#[.lz]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l1]⟩), ("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l0]⟩)],
   [("clk", ⟨#[.lx]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("d", ⟨#[.l1]⟩)]] with
    | .ok outs => outs.map (fun st => ["clk", "d", "q"].map (SvState.showSignal (CoreMemState.view E st))) ==
      [["z", "1", "x"],
     ["0", "1", "1"],
     ["1", "0", "1"],
     ["0", "0", "0"],
     ["0", "1", "0"],
     ["z", "1", "0"],
     ["x", "1", "0"],
     ["0", "1", "1"],
     ["z", "0", "1"],
     ["z", "0", "1"],
     ["z", "x", "1"],
     ["0", "x", "x"],
     ["x", "x", "x"],
     ["x", "1", "x"],
     ["1", "1", "x"],
     ["0", "1", "1"],
     ["1", "1", "1"],
     ["1", "1", "1"],
     ["1", "0", "1"],
     ["1", "0", "1"],
     ["0", "0", "0"],
     ["z", "1", "0"],
     ["0", "1", "1"],
     ["0", "0", "1"],
     ["1", "1", "1"],
     ["0", "1", "1"],
     ["0", "0", "1"],
     ["x", "0", "1"],
     ["1", "0", "1"],
     ["1", "1", "1"]]
    | _ => false
  | _ => false)

-- the same at `W = 4`
#guard (match dd.e 4 with
  | .ok E => match runCoreMemRows E E.initial
      [[("d", ⟨#[.l1, .l0, .l0, .l1]⟩), ("clk", ⟨#[.lz]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("d", ⟨#[.l1, .l0, .l1, .l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l1, .l0, .l1, .lz]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.lz]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l1, .lx, .l1, .l1]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("d", ⟨#[.l1, .l0, .l0, .l1]⟩)],
   [("d", ⟨#[.l0, .l1, .l1, .l0]⟩)],
   [("clk", ⟨#[.lz]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("d", ⟨#[.l1, .l0, .l0, .l1]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("d", ⟨#[.l1, .lx, .l1, .l0]⟩)],
   [("clk", ⟨#[.l0]⟩)],
   [("clk", ⟨#[.l1]⟩)],
   [("d", ⟨#[.l1, .l1, .l1, .l1]⟩)]] with
    | .ok outs => outs.map (fun st => ["clk", "d", "qp", "qn"].map (SvState.showSignal (CoreMemState.view E st))) ==
      [["z", "1001", "xxxx", "xxxx"],
     ["1", "1001", "1001", "xxxx"],
     ["1", "1101", "1001", "xxxx"],
     ["0", "1101", "1001", "1101"],
     ["1", "1101", "1101", "1101"],
     ["0", "1101", "1101", "1101"],
     ["0", "z101", "1101", "1101"],
     ["1", "z101", "z101", "1101"],
     ["0", "z101", "z101", "z101"],
     ["1", "z101", "z101", "z101"],
     ["z", "z101", "z101", "z101"],
     ["1", "z101", "z101", "z101"],
     ["0", "z101", "z101", "z101"],
     ["0", "11x1", "z101", "z101"],
     ["1", "11x1", "11x1", "z101"],
     ["0", "11x1", "11x1", "11x1"],
     ["1", "11x1", "11x1", "11x1"],
     ["0", "11x1", "11x1", "11x1"],
     ["1", "11x1", "11x1", "11x1"],
     ["1", "1001", "11x1", "11x1"],
     ["1", "0110", "11x1", "11x1"],
     ["z", "0110", "11x1", "0110"],
     ["1", "0110", "0110", "0110"],
     ["0", "0110", "0110", "0110"],
     ["0", "1001", "0110", "0110"],
     ["1", "1001", "1001", "0110"],
     ["1", "01x1", "1001", "0110"],
     ["0", "01x1", "1001", "01x1"],
     ["1", "01x1", "01x1", "01x1"],
     ["1", "1111", "01x1", "01x1"]]
    | _ => false
  | _ => false)

set_option maxHeartbeats 4000000 in
seq_mirror (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) : dd.e W

/-- The edge tests of §9.4.2 on bit 0. -/
def rise (a b : LVec) : Bool := isPosedge (a.bits[0]?.getD .lx) (b.bits[0]?.getD .lx)
def fall (a b : LVec) : Bool := isNegedge (a.bits[0]?.getD .lx) (b.bits[0]?.getD .lx)
def riseAt (s s' : SvState) (n : String) : Bool := isPosedge (s.bit0 n) (s'.bit0 n)
def fallAt (s s' : SvState) (n : String) : Bool := isNegedge (s.bit0 n) (s'.bit0 n)

theorem riseAt_eq {s s' : SvState} {n : String} {x y : LVec} (hx : SvState.lookup s n = some x)
    (hy : SvState.lookup s' n = some y) : riseAt s s' n = rise x y := by
  simp only [riseAt, SvState.bit0, hx, hy, rise]

theorem fallAt_eq {s s' : SvState} {n : String} {x y : LVec} (hx : SvState.lookup s n = some x)
    (hy : SvState.lookup s' n = some y) : fallAt s s' n = fall x y := by
  simp only [fallAt, SvState.bit0, hx, hy, fall]

/-! ## The falling-edge register -/

set_option maxHeartbeats 4000000 in
theorem ng_structure : SeqDesignI ng.e := by
  sv_structure

set_option maxHeartbeats 4000000 in
theorem ng_domains {E : CoreMemDesign} (hE : ng.e = .ok E) :
    E.events = [⟨"clk", .negedge⟩] ∧ E.domains = [(⟨"clk", .negedge⟩, ["q"])] ∧ E.crossings = [] := by
  sv_domains
  exact ⟨hevents, hdomains, hcrossings⟩

def ngView (c d q : LVec) : SvState := [("clk", c), ("d", d), ("q", q)]

set_option maxHeartbeats 4000000 in
/-- **The row equations**: `q` takes the applied `d` when `clk` fell, else holds. -/
theorem ng_row {E : CoreMemDesign} (hE : ng.e = .ok E) (c d q c' d' : LVec) (hc : c.width = 1)
    (hd : d.width = 1) (hq : q.width = 1) (hc' : c'.width = 1) (hd' : d'.width = 1) (mv : MemV) :
    E.slotV (ngView c d q) mv [("clk", c'), ("d", d')] = .ok (ngView c' d' (if fall c c' then d' else q), mv) := by
  sv_seq_inst [ng.e, ng.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (ngView c d q) mv [("clk", c'), ("d", d')] using hE [ngView, hc, hd, hq, hc', hd']
  rw [hcyc]
  simp only [seqE_getElem_zero, ngView, fall]
  rfl

/-- **The claim**: in every step of a run, `q` takes the value `d` had before the step when `clk` fell in it, else
holds. -/
def NgClaim (tr : List (SvState × MemV)) : Prop :=
  ∀ (k : Nat) (s s' : SvState × MemV), tr[k]? = some s → tr[k + 1]? = some s' →
    SvState.lookup s'.1 "q" = (if fallAt s.1 s'.1 "clk" then SvState.lookup s.1 "d" else SvState.lookup s.1 "q")

def NgInv (σ : SvState × MemV) : Prop :=
  ∃ c d q : LVec, σ.1 = ngView c d q ∧ c.width = 1 ∧ d.width = 1 ∧ q.width = 1

def NgStep (σ : SvState × MemV) (r : SvState) (σ' : SvState × MemV) : Prop :=
  NgInv σ ∧ ∃ c d q : LVec, σ.1 = ngView c d q ∧
    σ'.1 = ngView (appliedIn r σ.1 "clk") (appliedIn r σ.1 "d") (if fall c (appliedIn r σ.1 "clk") then appliedIn r σ.1 "d" else q)

set_option maxHeartbeats 4000000 in
theorem ng_facts {E : CoreMemDesign} (hE : ng.e = .ok E) :
    E.SeqProfileI ∧ E.seqOblI = true ∧
      (∀ v, E.ShapeV v ↔ ∃ c d q : LVec, v = ngView c d q ∧ c.width = 1 ∧ d.width = 1 ∧ q.width = 1) ∧
      (∀ r v, E.appliedRow r v = [("clk", appliedIn r v "clk"), ("d", appliedIn r v "d")]) ∧
      E.scalar.toDesign2.inputNames.toList = ["clk", "d"] ∧
      E.scalar.toDesign2.declWidth "clk" = some 1 ∧ E.scalar.toDesign2.declWidth "d" = some 1 ∧
      E.sources = ["clk"] := by
  obtain ⟨E', hE', hP, hO⟩ := ng_structure
  rw [hE] at hE'
  cases hE'
  refine ⟨hP, hO, ?_⟩
  have hev := (ng_domains hE).1
  sv_seq_inst [ng.e, ng.pdesign] at hE
  subst hE
  refine ⟨fun v => ?_, fun r v => by simp [CoreMemDesign.appliedRow, Elab.toDesign2, Design2.inputNames],
    by simp [Elab.toDesign2, Design2.inputNames], by simp [Elab.toDesign2, Design2.declWidth],
    by simp [Elab.toDesign2, Design2.declWidth], by simp [CoreMemDesign.sources, hev]⟩
  constructor
  · rintro ⟨hk, hw⟩
    rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hk hw
    obtain ⟨rfl, rfl, rfl⟩ := hk
    exact ⟨x1, x2, x3, rfl, hw⟩
  · rintro ⟨c, d, q, rfl, hc, hd, hq⟩
    exact ⟨by simp [ngView], by simp [ngView, hc, hd, hq]⟩

set_option maxHeartbeats 4000000 in
/-- **THE CLAIM, over every sequence of instants**. -/
theorem ng_runs : SeqRunsI ng.e fun _ tr => NgClaim tr := by
  obtain ⟨E, hE, hP, hO⟩ := ng_structure
  obtain ⟨-, -, hsh, happ, hin, hwc, hwd, hsrc⟩ := ng_facts hE
  have hev := (ng_domains hE).1
  refine SeqRunsI.of_rowEqs hE hP hO NgInv (fun st hc _ => (hsh _).mp hc.shape) NgStep ?_ ?_
  · rintro ⟨v, mv⟩ r ⟨c, d, q, hv, hc, hd, hq⟩ _ hty
    simp only at hv
    subst hv
    have hs : E.ShapeV (ngView c d q) := (hsh _).mpr ⟨c, d, q, rfl, hc, hd, hq⟩
    have w1 := CoreMemDesign.appliedIn_width_row hty (n := "clk") (x := c) (v := ngView c d q) (by simp [hin]) hwc
      (by simp [ngView, SvState.lookup]) hc
    have w2 := CoreMemDesign.appliedIn_width_row hty (n := "d") (x := d) (v := ngView c d q) (by simp [hin]) hwd
      (by simp [ngView, SvState.lookup]) hd
    rw [CoreMemDesign.slotV_applied hP hs mv r, happ, ng_row hE c d q _ _ hc hd hq w1 w2 mv]
    refine ⟨_, rfl, ⟨_, _, _, rfl, w1, w2, ?_⟩, ⟨⟨c, d, q, rfl, hc, hd, hq⟩, c, d, q, rfl, rfl⟩⟩
    split <;> assumption
  · intro σ rows trs _ _ hsat k s s' hk hk1
    obtain ⟨σc, row, -, ⟨⟨hinv, c, d, q, hv, hv'⟩, hrow⟩, -, hprev⟩ := RunSatS.get hsat hk1
    have hσc : σc = s := hprev s (by simpa using hk) (by omega)
    subst hσc
    obtain ⟨v, mv⟩ := σc
    simp only at hv hv' hrow hinv
    subst hv
    obtain ⟨v', mv'⟩ := s'
    simp only at hv'
    subst hv'
    have hs : E.ShapeV (ngView c d q) := (hsh _).mpr hinv
    show SvState.lookup (ngView _ _ _) "q" = _
    rw [fallAt_eq (n := "clk") (x := c) (y := appliedIn row (ngView c d q) "clk") (by simp [ngView, SvState.lookup])
      (by simp [ngView, SvState.lookup])]
    simp only [show ∀ a b e : LVec, SvState.lookup (ngView a b e) "q" = some e by intro a b e; simp [ngView, SvState.lookup],
      show ∀ a b e : LVec, SvState.lookup (ngView a b e) "d" = some b by intro a b e; simp [ngView, SvState.lookup]]
    by_cases hr : fall c (appliedIn row (ngView c d q) "clk") = true
    · rw [if_pos hr, if_pos hr]
      have := CoreMemDesign.applied_still hP hs hrow (e := ⟨"clk", .negedge⟩) (by rw [hev]; simp) (by simp [hin])
        (by simpa [edgeOf, SvState.bit0, ngView, SvState.lookup, fall] using hr) (x := "d") (by simp [hin])
        (by rw [hsrc]; simp)
      rw [this]
      simp [ngView, SvState.lookup]
    · rw [if_neg hr, if_neg hr]

/-! ## The register on each edge -/

set_option maxHeartbeats 4000000 in
theorem dd_structure (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) : SeqDesignI (dd.e W) := by
  sv_structure

set_option maxHeartbeats 4000000 in
theorem dd_domains (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : dd.e W = .ok E) :
    E.events = [⟨"clk", .posedge⟩, ⟨"clk", .negedge⟩] ∧
      E.domains = [(⟨"clk", .posedge⟩, ["qp"]), (⟨"clk", .negedge⟩, ["qn"])] ∧ E.crossings = [] := by
  sv_domains
  exact ⟨hevents, hdomains, hcrossings⟩

def ddView (c d p n : LVec) : SvState := [("clk", c), ("d", d), ("qp", p), ("qn", n)]

set_option maxHeartbeats 4000000 in
/-- **The row equations**: `qp` takes the applied `d` when `clk` rose, `qn` when it fell. -/
theorem dd_row (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : dd.e W = .ok E)
    (c d p n c' d' : LVec) (hc : c.width = 1) (hd : d.width = W) (hp : p.width = W) (hn : n.width = W)
    (hc' : c'.width = 1) (hd' : d'.width = W) (mv : MemV) :
    E.slotV (ddView c d p n) mv [("clk", c'), ("d", d')] =
      .ok (ddView c' d' (if rise c c' then d' else p) (if fall c c' then d' else n), mv) := by
  sv_seq_use [dd.mirror_eq W h1 h2, dd.mirror_def] at hE
  sv_seq_cycle hcyc : E.slotV (ddView c d p n) mv [("clk", c'), ("d", d')] using hE
    [ddView, hc, hd, hp, hn, hc', hd']
  rw [hcyc]
  simp only [seqE_getElem_zero, ddView, rise, fall]
  rfl

set_option maxHeartbeats 4000000 in
/-- **One equation set per event** (the instant function at each of the design's two events, from the mirror): from a
low clock the instant `{posedge clk}` loads `qp` and leaves `qn`; from a high clock `{negedge clk}` loads `qn` and
leaves `qp`. -/
theorem dd_ticks (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : dd.e W = .ok E)
    (d p n : LVec) (hd : d.width = W) (hp : p.width = W) (hn : n.width = W) (mv : MemV) :
    E.tick (Instant.rise "clk") (ddView ⟨#[.l0]⟩ d p n, mv) = .ok (ddView ⟨#[.l1]⟩ d d n, mv) ∧
      E.tick (Instant.fall "clk") (ddView ⟨#[.l1]⟩ d p n, mv) = .ok (ddView ⟨#[.l0]⟩ d p d, mv) := by
  refine ⟨?_, ?_⟩ <;> simp only [ddView] <;> sv_equations

/-- **The claim**: in every step of a run, `qp` takes the value `d` had before the step when `clk` rose in it, `qn`
when it fell; each holds otherwise. -/
def DdClaim (tr : List (SvState × MemV)) : Prop :=
  ∀ (k : Nat) (s s' : SvState × MemV), tr[k]? = some s → tr[k + 1]? = some s' →
    SvState.lookup s'.1 "qp" = (if riseAt s.1 s'.1 "clk" then SvState.lookup s.1 "d" else SvState.lookup s.1 "qp") ∧
      SvState.lookup s'.1 "qn" = (if fallAt s.1 s'.1 "clk" then SvState.lookup s.1 "d" else SvState.lookup s.1 "qn")

def DdInv (W : Nat) (σ : SvState × MemV) : Prop :=
  ∃ c d p n : LVec, σ.1 = ddView c d p n ∧ c.width = 1 ∧ d.width = W ∧ p.width = W ∧ n.width = W

def DdStep (W : Nat) (σ : SvState × MemV) (r : SvState) (σ' : SvState × MemV) : Prop :=
  DdInv W σ ∧ ∃ c d p n : LVec, σ.1 = ddView c d p n ∧
    σ'.1 = ddView (appliedIn r σ.1 "clk") (appliedIn r σ.1 "d")
      (if rise c (appliedIn r σ.1 "clk") then appliedIn r σ.1 "d" else p)
      (if fall c (appliedIn r σ.1 "clk") then appliedIn r σ.1 "d" else n)

set_option maxHeartbeats 4000000 in
theorem dd_facts (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : dd.e W = .ok E) :
    E.SeqProfileI ∧ E.seqOblI = true ∧
      (∀ v, E.ShapeV v ↔ ∃ c d p n : LVec, v = ddView c d p n ∧ c.width = 1 ∧ d.width = W ∧ p.width = W ∧
        n.width = W) ∧
      (∀ r v, E.appliedRow r v = [("clk", appliedIn r v "clk"), ("d", appliedIn r v "d")]) ∧
      E.scalar.toDesign2.inputNames.toList = ["clk", "d"] ∧
      E.scalar.toDesign2.declWidth "clk" = some 1 ∧ E.scalar.toDesign2.declWidth "d" = some W ∧
      E.sources = ["clk", "clk"] := by
  obtain ⟨E', hE', hP, hO⟩ := dd_structure W h1 h2
  rw [hE] at hE'
  cases hE'
  refine ⟨hP, hO, ?_⟩
  have hev := (dd_domains W h1 h2 hE).1
  sv_seq_use [dd.mirror_eq W h1 h2, dd.mirror_def] at hE
  subst hE
  refine ⟨fun v => ?_, fun r v => by simp [CoreMemDesign.appliedRow, Elab.toDesign2, Design2.inputNames],
    by simp [Elab.toDesign2, Design2.inputNames], by simp [Elab.toDesign2, Design2.declWidth],
    by simp [Elab.toDesign2, Design2.declWidth], by simp [CoreMemDesign.sources, hev]⟩
  constructor
  · rintro ⟨hk, hw⟩
    rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hk hw
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
    exact ⟨x1, x2, x3, x4, rfl, hw⟩
  · rintro ⟨c, d, p, n, rfl, hc, hd, hp, hn⟩
    exact ⟨by simp [ddView], by simp [ddView, hc, hd, hp, hn]⟩

set_option maxHeartbeats 4000000 in
/-- **THE CLAIM, over every sequence of instants**. -/
theorem dd_runs (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) : SeqRunsI (dd.e W) fun _ tr => DdClaim tr := by
  obtain ⟨E, hE, hP, hO⟩ := dd_structure W h1 h2
  obtain ⟨-, -, hsh, happ, hin, hwc, hwd, hsrc⟩ := dd_facts W h1 h2 hE
  have hev := (dd_domains W h1 h2 hE).1
  refine SeqRunsI.of_rowEqs hE hP hO (DdInv W) (fun st hc _ => (hsh _).mp hc.shape) (DdStep W) ?_ ?_
  · rintro ⟨v, mv⟩ r ⟨c, d, p, n, hv, hc, hd, hp, hn⟩ _ hty
    simp only at hv
    subst hv
    have hs : E.ShapeV (ddView c d p n) := (hsh _).mpr ⟨c, d, p, n, rfl, hc, hd, hp, hn⟩
    have w1 := CoreMemDesign.appliedIn_width_row hty (n := "clk") (x := c) (v := ddView c d p n) (by simp [hin]) hwc
      (by simp [ddView, SvState.lookup]) hc
    have w2 := CoreMemDesign.appliedIn_width_row hty (n := "d") (x := d) (v := ddView c d p n) (by simp [hin]) hwd
      (by simp [ddView, SvState.lookup]) hd
    rw [CoreMemDesign.slotV_applied hP hs mv r, happ, dd_row W h1 h2 hE c d p n _ _ hc hd hp hn w1 w2 mv]
    refine ⟨_, rfl, ⟨_, _, _, _, rfl, w1, w2, ?_, ?_⟩, ⟨⟨c, d, p, n, rfl, hc, hd, hp, hn⟩, c, d, p, n, rfl, rfl⟩⟩
    · split <;> assumption
    · split <;> assumption
  · intro σ rows trs _ _ hsat k s s' hk hk1
    obtain ⟨σc, row, -, ⟨⟨hinv, c, d, p, n, hv, hv'⟩, hrow⟩, -, hprev⟩ := RunSatS.get hsat hk1
    have hσc : σc = s := hprev s (by simpa using hk) (by omega)
    subst hσc
    obtain ⟨v, mv⟩ := σc
    simp only at hv hv' hrow hinv
    subst hv
    obtain ⟨v', mv'⟩ := s'
    simp only at hv'
    subst hv'
    have hs : E.ShapeV (ddView c d p n) := (hsh _).mpr hinv
    show SvState.lookup (ddView _ _ _ _) "qp" = _ ∧ SvState.lookup (ddView _ _ _ _) "qn" = _
    rw [riseAt_eq (n := "clk") (x := c) (y := appliedIn row (ddView c d p n) "clk") (by simp [ddView, SvState.lookup])
        (by simp [ddView, SvState.lookup]),
      fallAt_eq (n := "clk") (x := c) (y := appliedIn row (ddView c d p n) "clk") (by simp [ddView, SvState.lookup])
        (by simp [ddView, SvState.lookup])]
    simp only [show ∀ a b e f : LVec, SvState.lookup (ddView a b e f) "qp" = some e by
        intro a b e f; simp [ddView, SvState.lookup],
      show ∀ a b e f : LVec, SvState.lookup (ddView a b e f) "qn" = some f by
        intro a b e f; simp [ddView, SvState.lookup],
      show ∀ a b e f : LVec, SvState.lookup (ddView a b e f) "d" = some b by
        intro a b e f; simp [ddView, SvState.lookup]]
    have hdv : ∀ (e : SeqEvent) (t : Bool), e ∈ E.events → e.src = "clk" →
        edgeOf e.kind (c.bits[0]?.getD .lx) ((appliedIn row (ddView c d p n) "clk").bits[0]?.getD .lx) = true →
        appliedIn row (ddView c d p n) "d" = d := by
      intro e _ he hes ho
      have := CoreMemDesign.applied_still hP hs hrow he (by rw [hes]; simp [hin])
        (by rw [hes]; simpa [SvState.bit0, ddView, SvState.lookup] using ho) (x := "d") (by simp [hin])
        (by rw [hsrc]; simp)
      rw [this]
      simp [ddView, SvState.lookup]
    refine ⟨?_, ?_⟩
    · by_cases hr : rise c (appliedIn row (ddView c d p n) "clk") = true
      · rw [if_pos hr, if_pos hr, hdv ⟨"clk", .posedge⟩ true (by rw [hev]; simp) rfl (by simpa [edgeOf, rise] using hr)]
      · rw [if_neg hr, if_neg hr]
    · by_cases hr : fall c (appliedIn row (ddView c d p n) "clk") = true
      · rw [if_pos hr, if_pos hr, hdv ⟨"clk", .negedge⟩ true (by rw [hev]; simp) rfl (by simpa [edgeOf, fall] using hr)]
      · rw [if_neg hr, if_neg hr]

#print axioms ng_structure
#print axioms ng_domains
#print axioms ng_row
#print axioms ng_runs
#print axioms dd_structure
#print axioms dd_domains
#print axioms dd_row
#print axioms dd_ticks
#print axioms dd_runs

end Examples.«system-verilog».seq_multi.edges_proof
