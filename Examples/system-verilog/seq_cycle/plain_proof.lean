import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# A plain `always @(posedge clk or negedge rst_n)` register, on the ordinary E route, at every `N ≥ 1`

The design (`plain_arst.sv`, Verilog-2001 style: an untyped parameter, `reg`, a plain `always`):

```systemverilog
module plain_arst #(parameter N = 4) (input clk, input rst_n, input en, input [N-1:0] d, output reg [N-1:0] q);
  always @(posedge clk or negedge rst_n)
    if (!rst_n) q <= {N{1'b0}};
    else if (en) q <= d;
endmodule
```

Ingestion keeps the process as an EVENT process (`CoreMemProc.event`, the event list as written). IEEE 1800-2017
§9.2.2.1 and §9.2.2.4: `always_ff` restricts `always`, it does not change how the body executes. In the clocked
theory that is a proved fact about the route (`coreMemEventEdge?_spec`, `CoreMemDesign.runEdges_event`: an event list
of one clock edge with an optional reset edge fires by the same §9.4.2 edge table and runs the same body as the edge
process), so the clocked profile reads the process as its edge process (`CoreMemProc.edge?`) and every clocked
theorem applies to the design as loaded.

1. **Structure** (`pa_structure`, `sv_structure`): the instantiation at every `1 ≤ N < 2^30`, in the single-clock
   profile, with the obligations.
2. **The slot equation** (`pa_row`): one row of inputs, on a symbolic 4-state view, computed from the route's
   definitions; `paNext` is its `q` entry.
3. **The contract** (`pa_step`): from EVERY coherent state and on EVERY typed input row (any subset of the inputs,
   every value 0, 1, x or z) the route's step succeeds, stays coherent, and `q` afterwards is `paNext`: the process
   fires when the clock rises (0→1, 0→x, 0→z, x→1, z→1) or the reset falls (1→0, 1→x, 1→z, x→0, z→0); fired with
   the reset 0 it clears; fired with the reset 1, x or z it loads `d` when `en` is 1 and holds when `en` is 0, x or z;
   otherwise it holds (`pa_reset`, `pa_load`, `pa_keep`, `pa_hold`).
4. **The twin** (`pa_eq_ff`): on every view and row of the shape, the slot of this design IS the slot of its
   `always_ff` twin `sem2/clk_arst`, for every `N`: §9.2.2.4 as a theorem about the two loaded designs.

Oracle: Icarus Verilog 12.0 (stable). The three runs below (N = 1, 4, 8; 30 rows each, with x and z on the clock,
the reset, the enable and the data, from the x start) are the rows of a testbench outside the repository; the expected
lists are Icarus's samples of `q` one time unit after each row (90 rows, 0 mismatches). No Xcelium result is claimed.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.plain_proof

load_design_sv2 pa from "Examples/system-verilog/seq_cycle/plain_arst.sv.json"
load_design_sv2 ff from "Examples/system-verilog/sem2/clk_arst/clk_arst.sv.json"

/-! ## 0. Runs of the route against Icarus Verilog 12.0 (row by row, x and z included) -/

#guard (match pa.e 1 with
  | .ok E => match runCoreMemRows E E.initial
      [[("rst_n", ⟨#[.l1]⟩), ("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("d", ⟨#[.l1]⟩)],
       [("rst_n", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l0]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("en", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.lz]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.lx]⟩)],
       [("d", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.lz]⟩)],
       [("rst_n", ⟨#[.l1]⟩)],
       [("en", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩), ("d", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["x", "1", "1", "1", "0", "0", "0", "0", "1", "1", "1", "1", "1", "1", "1", "1", "1", "1", "1", "0", "0", "0", "0", "0", "0", "0", "0", "x", "x", "0"]
    | _ => false
  | _ => false)


#guard (match pa.e 4 with
  | .ok E => match runCoreMemRows E E.initial
      [[("rst_n", ⟨#[.l1]⟩), ("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩), ("d", ⟨#[.l1, .l0, .l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("d", ⟨#[.l1, .l0, .l0, .l1]⟩)],
       [("rst_n", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("en", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.lz]⟩), ("d", ⟨#[.lz, .l0, .lx, .l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.lx]⟩)],
       [("d", ⟨#[.l0, .l1, .l1, .l0]⟩)],
       [("rst_n", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.lz]⟩)],
       [("rst_n", ⟨#[.l1]⟩)],
       [("en", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩), ("d", ⟨#[.lx, .lx, .lx, .lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l0, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxx", "0101", "0101", "0101", "0000", "0000", "0000", "0000", "1001", "1001", "1001", "1001", "1001", "0011", "0011", "1x0z", "1x0z", "1x0z", "1x0z", "0000", "0000", "0000", "0000", "0000", "0000", "0000", "0000", "xxxx", "xxxx", "1010"]
    | _ => false
  | _ => false)


#guard (match pa.e 8 with
  | .ok E => match runCoreMemRows E E.initial
      [[("rst_n", ⟨#[.l1]⟩), ("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩), ("d", ⟨#[.l1, .l0, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("d", ⟨#[.l1, .l0, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("rst_n", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l0, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("en", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.lz]⟩), ("d", ⟨#[.lz, .l0, .lx, .l1, .lz, .l0, .lx, .l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.lx]⟩)],
       [("d", ⟨#[.l0, .l1, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("rst_n", ⟨#[.l0]⟩)],
       [("rst_n", ⟨#[.lz]⟩)],
       [("rst_n", ⟨#[.l1]⟩)],
       [("en", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩), ("d", ⟨#[.lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxxxxxx", "00000101", "00000101", "00000101", "00000000", "00000000", "00000000", "00000000", "00001001", "00001001", "00001001", "00001001", "00001001", "00000011", "00000011", "1x0z1x0z", "1x0z1x0z", "1x0z1x0z", "1x0z1x0z", "00000000", "00000000", "00000000", "00000000", "00000000", "00000000", "00000000", "00000000", "xxxxxxxx", "xxxxxxxx", "00001010"]
    | _ => false
  | _ => false)


-- The loaded process is an event process, and the clocked theory reads it as the edge process.
#guard (match pa.e 4 with
  | .ok E => E.processes.toList.map (fun p => (p matches .event _ _, p.isEdge)) == [(true, true)]
  | _ => false)

/-! ## 1. Structure and interface -/

set_option maxHeartbeats 4000000 in
theorem pa_structure (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) : SeqDesign (pa.e N) "clk" := by
  sv_structure

set_option maxHeartbeats 4000000 in
theorem pa_ports (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) :
    SeqPorts (pa.e N) [("clk", 1), ("rst_n", 1), ("en", 1), ("d", N)] [("q", N)] := by
  sv_interface

set_option maxHeartbeats 4000000 in
theorem ff_structure (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) : SeqDesign (ff.e N) "clk" := by
  sv_structure

/-! ## 2. The slot equation -/

/-- The view, in declaration order. -/
def paView (c r e d q : LVec) : SvState := [("clk", c), ("rst_n", r), ("en", e), ("d", d), ("q", q)]

/-- Bit 0 of a signal, as the edge table reads it. -/
def b0 (x : LVec) : Logic := x.bits[0]?.getD .lx

/-- IEEE 1800-2017 §9.4.2: a rise is 0→1, 0→x, 0→z, x→1, z→1; a fall is 1→0, 1→x, 1→z, x→0, z→0. -/
def rise (a b : LVec) : Bool := isPosedge (b0 a) (b0 b)
def fall (a b : LVec) : Bool := isNegedge (b0 a) (b0 b)

/-- **The contract function**: `q` after a row that moves the clock from `c` to `c1` and the reset from `r` to `r1`,
with the enable `e1` and the data `d1` after the row. -/
def paNext (N : Nat) (c r q c1 r1 e1 d1 : LVec) : LVec :=
  if rise c c1 = true ∨ fall r r1 = true then
    if (evalUnaryOp .lnot r1).condTrue = true then LVec.ofBitVec 0#N else if e1.condTrue = true then d1 else q
  else q

set_option maxHeartbeats 4000000 in
/-- **The slot equation**, computed from the route's own definitions on a symbolic view. -/
theorem pa_row (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : pa.e N = .ok E)
    (c r e d q c1 r1 e1 d1 : LVec) (hc : c.width = 1) (hr : r.width = 1) (he : e.width = 1) (hd : d.width = N)
    (hq : q.width = N) (hc1 : c1.width = 1) (hr1 : r1.width = 1) (he1 : e1.width = 1) (hd1 : d1.width = N)
    (mv : MemV) :
    E.slotV (paView c r e d q) mv [("clk", c1), ("rst_n", r1), ("en", e1), ("d", d1)] =
      .ok (paView c1 r1 e1 d1 (paNext N c r q c1 r1 e1 d1), mv) := by
  sv_seq_inst [pa.e, pa.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (paView c r e d q) mv [("clk", c1), ("rst_n", r1), ("en", e1), ("d", d1)] using hE
      [paView, hc, hr, he, hd, hq, hc1, hr1, he1, hd1]
  rw [hcyc]
  simp only [seqE_getElem_zero, paView, paNext, rise, fall, b0]
  rfl

set_option maxHeartbeats 4000000 in
/-- The same slot equation for the `always_ff` twin. -/
theorem ff_row (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : ff.e N = .ok E)
    (c r e d q c1 r1 e1 d1 : LVec) (hc : c.width = 1) (hr : r.width = 1) (he : e.width = 1) (hd : d.width = N)
    (hq : q.width = N) (hc1 : c1.width = 1) (hr1 : r1.width = 1) (he1 : e1.width = 1) (hd1 : d1.width = N)
    (mv : MemV) :
    E.slotV (paView c r e d q) mv [("clk", c1), ("rst_n", r1), ("en", e1), ("d", d1)] =
      .ok (paView c1 r1 e1 d1 (paNext N c r q c1 r1 e1 d1), mv) := by
  sv_seq_inst [ff.e, ff.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (paView c r e d q) mv [("clk", c1), ("rst_n", r1), ("en", e1), ("d", d1)] using hE
      [paView, hc, hr, he, hd, hq, hc1, hr1, he1, hd1]
  rw [hcyc]
  simp only [seqE_getElem_zero, paView, paNext, rise, fall, b0]
  rfl

/-- **THE TWIN**: the plain `always` design and its `always_ff` twin have the same slot, on every view and row of the
shape, at every `N` (IEEE 1800-2017 §9.2.2.4, proved on the two loaded designs). -/
theorem pa_eq_ff (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E F : CoreMemDesign} (hE : pa.e N = .ok E)
    (hF : ff.e N = .ok F) (c r e d q c1 r1 e1 d1 : LVec) (hc : c.width = 1) (hr : r.width = 1) (he : e.width = 1)
    (hd : d.width = N) (hq : q.width = N) (hc1 : c1.width = 1) (hr1 : r1.width = 1) (he1 : e1.width = 1)
    (hd1 : d1.width = N) (mv : MemV) :
    E.slotV (paView c r e d q) mv [("clk", c1), ("rst_n", r1), ("en", e1), ("d", d1)] =
      F.slotV (paView c r e d q) mv [("clk", c1), ("rst_n", r1), ("en", e1), ("d", d1)] := by
  rw [pa_row N h1 h2 hE c r e d q c1 r1 e1 d1 hc hr he hd hq hc1 hr1 he1 hd1 mv,
    ff_row N h1 h2 hF c r e d q c1 r1 e1 d1 hc hr he hd hq hc1 hr1 he1 hd1 mv]

/-! ## 3. The facts of the design (the shape of a view, the input list, the widths) -/

set_option maxHeartbeats 4000000 in
theorem pa_facts (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : pa.e N = .ok E) :
    E.SeqProfileI ∧ E.seqOblI = true ∧
      (∀ v, E.ShapeV v ↔ ∃ c r e d q : LVec, v = paView c r e d q ∧ c.width = 1 ∧ r.width = 1 ∧ e.width = 1 ∧
        d.width = N ∧ q.width = N) ∧
      (∀ r v, E.appliedRow r v = [("clk", appliedIn r v "clk"), ("rst_n", appliedIn r v "rst_n"),
        ("en", appliedIn r v "en"), ("d", appliedIn r v "d")]) ∧
      E.scalar.toDesign2.inputNames.toList = ["clk", "rst_n", "en", "d"] ∧
      E.scalar.toDesign2.declWidth "clk" = some 1 ∧ E.scalar.toDesign2.declWidth "rst_n" = some 1 ∧
      E.scalar.toDesign2.declWidth "en" = some 1 ∧ E.scalar.toDesign2.declWidth "d" = some N := by
  obtain ⟨E', hE', hP, hO⟩ := pa_structure N h1 h2
  rw [hE] at hE'
  cases hE'
  refine ⟨hP.toSeqProfileI, CoreMemDesign.seqOblB_I hO, ?_⟩
  sv_seq_inst [pa.e, pa.pdesign] at hE
  subst hE
  refine ⟨fun v => ?_, fun r v => by simp [CoreMemDesign.appliedRow, Elab.toDesign2, Design2.inputNames],
    by simp [Elab.toDesign2, Design2.inputNames], by simp [Elab.toDesign2, Design2.declWidth],
    by simp [Elab.toDesign2, Design2.declWidth], by simp [Elab.toDesign2, Design2.declWidth],
    by simp [Elab.toDesign2, Design2.declWidth]⟩
  constructor
  · rintro ⟨hk, hw⟩
    rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨⟨n5, x5⟩, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      simp at hk hw
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk
    exact ⟨x1, x2, x3, x4, x5, rfl, hw⟩
  · rintro ⟨c, r, e, d, q, rfl, hc, hr, he, hd, hq⟩
    exact ⟨by simp [paView], by simp [paView, hc, hr, he, hd, hq]⟩

/-! ## 4. The contract: every coherent state, every typed row -/

set_option maxHeartbeats 4000000 in
/-- **THE CONTRACT.** From every coherent state `st` (the x start, the time-zero state, every state a run reaches), on
every typed input row (any subset of the inputs, any 4-state values), the route's step succeeds, the state after it is
coherent again, and its view is the applied inputs with `q' = paNext …`. `appliedIn row v n` is the row's value for
`n` when the row drives `n`, else the value `v` holds. -/
theorem pa_step (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : pa.e N = .ok E)
    (st : CoreMemState) (hc : E.Coherent st) (hmc : E.MemCoherent st.memory) (row : SvState)
    (hty : EntryTyped E.scalar.toDesign2 row) :
    ∃ st', E.step st row = .ok st' ∧ E.Coherent st' ∧ E.MemCoherent st'.memory ∧
      ∃ c r e d q : LVec, CoreMemState.view E st = paView c r e d q ∧
        c.width = 1 ∧ r.width = 1 ∧ e.width = 1 ∧ d.width = N ∧ q.width = N ∧
        let v := paView c r e d q
        CoreMemState.view E st' =
          paView (appliedIn row v "clk") (appliedIn row v "rst_n") (appliedIn row v "en") (appliedIn row v "d")
            (paNext N c r q (appliedIn row v "clk") (appliedIn row v "rst_n") (appliedIn row v "en")
              (appliedIn row v "d")) := by
  obtain ⟨hP, hO, hsh, happ, hin, hwc, hwr, hwe, hwd⟩ := pa_facts N h1 h2 hE
  obtain ⟨c, r, e, d, q, hv, hc', hr, he, hd, hq⟩ := (hsh _).mp hc.shape
  have w1 := CoreMemDesign.appliedIn_width_row hty (n := "clk") (x := c) (v := paView c r e d q) (by simp [hin]) hwc
    (by simp [paView, SvState.lookup]) hc'
  have w2 := CoreMemDesign.appliedIn_width_row hty (n := "rst_n") (x := r) (v := paView c r e d q) (by simp [hin])
    hwr (by simp [paView, SvState.lookup]) hr
  have w3 := CoreMemDesign.appliedIn_width_row hty (n := "en") (x := e) (v := paView c r e d q) (by simp [hin]) hwe
    (by simp [paView, SvState.lookup]) he
  have w4 := CoreMemDesign.appliedIn_width_row hty (n := "d") (x := d) (v := paView c r e d q) (by simp [hin]) hwd
    (by simp [paView, SvState.lookup]) hd
  have hslot := pa_row N h1 h2 hE c r e d q _ _ _ _ hc' hr he hd hq w1 w2 w3 w4 (E.memOf st.memory)
  rw [← happ, ← CoreMemDesign.slotV_applied hP ((hsh _).mpr ⟨c, r, e, d, q, rfl, hc', hr, he, hd, hq⟩), ← hv]
    at hslot
  obtain ⟨st', hs', hv', -, hc1, hmc1⟩ := CoreMemDesign.step_seqI hP hO hc hmc hty hslot
  rw [hv] at hv'
  exact ⟨st', hs', hc1, hmc1, c, r, e, d, q, hv, hc', hr, he, hd, hq, hv'⟩

/-- The contract applies to runs: the x start is coherent with a coherent memory, and `pa_step` keeps both. -/
theorem pa_start (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : pa.e N = .ok E) :
    E.Coherent E.initial ∧ E.MemCoherent E.initial.memory :=
  ⟨E.initial_coherent, CoreMemDesign.initial_memCoherent (pa_facts N h1 h2 hE).1.mems⟩

/-! ## 5. Reading the contract -/

theorem eq_b0 {x : LVec} (h : x.width = 1) : x = ⟨#[b0 x]⟩ := (LVec.eq_bit0 h).symm

/-- `!r` reads true exactly when the one-bit `r` is 0: an x or z reset does not read as asserted. -/
theorem lnot_condTrue {r : LVec} (h : r.width = 1) : (evalUnaryOp .lnot r).condTrue = (b0 r == .l0) := by
  rw [eq_b0 h]
  cases b0 r <;> simp [evalUnaryOp, LVec.lnot, LVec.condTrue, LVec.isKnownZero, LVec.ofLogic, b0] <;> decide

/-- A one-bit enable reads true exactly when it is 1 (x and z read false). -/
theorem en_condTrue {e : LVec} (h : e.width = 1) : e.condTrue = (b0 e == .l1) := by
  rw [eq_b0 h]
  cases b0 e <;> simp [LVec.condTrue, LVec.isKnownZero, b0] <;> decide

/-- Reset: the process fired and the reset is 0 after the row: `q` is 0. -/
theorem pa_reset {N : Nat} {c r q c1 r1 e1 d1 : LVec} (hr1 : r1.width = 1)
    (hfire : rise c c1 = true ∨ fall r r1 = true) (hlow : b0 r1 = .l0) :
    paNext N c r q c1 r1 e1 d1 = LVec.ofBitVec 0#N := by
  simp [paNext, hfire, lnot_condTrue hr1, hlow]

/-- Load: the process fired, the reset is not 0 after the row (1, x or z) and the enable is 1: `q` is the applied `d`,
bit for bit (x and z included). -/
theorem pa_load {N : Nat} {c r q c1 r1 e1 d1 : LVec} (hr1 : r1.width = 1) (he1 : e1.width = 1)
    (hfire : rise c c1 = true ∨ fall r r1 = true) (hhigh : b0 r1 ≠ .l0) (hen : b0 e1 = .l1) :
    paNext N c r q c1 r1 e1 d1 = d1 := by
  simp [paNext, hfire, lnot_condTrue hr1, hhigh, en_condTrue he1, hen]

/-- Keep: the process fired, the reset is not 0 and the enable is not 1 (0, x or z): `q` holds. -/
theorem pa_keep {N : Nat} {c r q c1 r1 e1 d1 : LVec} (hr1 : r1.width = 1) (he1 : e1.width = 1)
    (hhigh : b0 r1 ≠ .l0) (hen : b0 e1 ≠ .l1) : paNext N c r q c1 r1 e1 d1 = q := by
  simp [paNext, lnot_condTrue hr1, hhigh, en_condTrue he1, hen]

/-- Hold: no rise of the clock and no fall of the reset: `q` holds (also while the reset is held at 0). -/
theorem pa_hold {N : Nat} {c r q c1 r1 e1 d1 : LVec} (hc : rise c c1 = false) (hr : fall r r1 = false) :
    paNext N c r q c1 r1 e1 d1 = q := by
  simp [paNext, hc, hr]

#print axioms pa_structure
#print axioms pa_ports
#print axioms pa_row
#print axioms pa_eq_ff
#print axioms pa_facts
#print axioms pa_step
#print axioms pa_start
#print axioms pa_reset
#print axioms pa_load
#print axioms pa_keep
#print axioms pa_hold

end Examples.«system-verilog».seq_cycle.plain_proof
