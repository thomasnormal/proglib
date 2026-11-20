import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# Parameters of an unsigned type: a zero-extending register, at every `W ≥ 1` and every `G`

The design (`unsigned_ext.sv`):

```systemverilog
module unsigned_ext #(parameter int unsigned W = 4, parameter int unsigned G = 2)
  (input logic clk, input logic en, input logic [W-1:0] d, output logic [W+G-1:0] q);
  always_ff @(posedge clk) if (en) q <= d;
endmodule
```

Over `parameter int unsigned` a dimension such as `[W-1:0]` or `[W+G-1:0]` is not an INT-class expression: the
instantiation sizes it (IEEE 1800-2017 §11.6: `evalSized`) and wraps every value to the unsigned 32-bit type. The
clocked instantiation pass evaluates that route at symbolic parameters (`seqE_evalAt_*`), and reads the wrapped
values as themselves where the parameter hypotheses place them in `[0, 2^32)`: here `W-1` needs `1 ≤ W` (at `W = 0`
the unsigned `W-1` wraps to `2^32 - 1`, a different design, and the hypothesis says so).

1. **Structure** (`ue_structure`): the instantiation at every `1 ≤ W < 2^30`, `G < 2^30`, in the single-clock
   profile, with the obligations.
2. **The slot equation** (`ue_row`) and **the contract** (`ue_step`): from every coherent state, on every typed input
   row (any 4-state values), `q` afterwards is `ueNext`: on a rise of the clock with `en` reading true, `d`
   zero-extended to `W + G` bits (bit for bit: an x or z bit of `d` stays, the `G` bits above are 0); otherwise `q`.
3. **On known data** (`ue_load_known`): the loaded value is `BitVec.zeroExtend`.

Oracle: Icarus Verilog 12.0 (stable). The three runs below ((W, G) = (1, 0), (4, 2), (8, 3); 14 rows each, with x and
z on the clock, the enable and the data, from the x start) are the rows of a testbench outside the repository; the
expected lists are Icarus's samples of `q` one time unit after each row (42 rows, 0 mismatches). No Xcelium result is
claimed.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.unsigned_proof

load_design_sv2 ue from "Examples/system-verilog/seq_cycle/unsigned_ext.sv.json"

/-! ## 0. Runs of the route against Icarus Verilog 12.0 -/

#guard (match ue.e 1 0 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l0]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩), ("en", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.lx]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["x", "1", "1", "0", "0", "0", "0", "1", "1", "z", "z", "z", "z", "1"]
    | _ => false
  | _ => false)


#guard (match ue.e 4 2 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩), ("d", ⟨#[.l1, .l0, .l1, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l0, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩), ("en", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .lx, .l1, .lz]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.lx]⟩), ("d", ⟨#[.l1, .l1, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxxxx", "001101", "001101", "000110", "000110", "000110", "000110", "001001", "001001", "00z1x0", "00z1x0", "00z1x0", "00z1x0", "000011"]
    | _ => false
  | _ => false)


#guard (match ue.e 8 3 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩), ("d", ⟨#[.l1, .l0, .l1, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩), ("en", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .lx, .l1, .lz, .l0, .lx, .l1, .lz]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.lx]⟩), ("d", ⟨#[.l1, .l1, .l0, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("en", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxxxxxxxxx", "00000001101", "00000001101", "00000000110", "00000000110", "00000000110", "00000000110", "00000001001", "00000001001", "000z1x0z1x0", "000z1x0z1x0", "000z1x0z1x0", "000z1x0z1x0", "00000000011"]
    | _ => false
  | _ => false)


/-! ## 1. Structure and interface -/

set_option maxHeartbeats 4000000 in
theorem ue_structure (W G : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : G < 2 ^ 30) :
    SeqDesign (ue.e W G) "clk" := by
  sv_structure

set_option maxHeartbeats 4000000 in
theorem ue_ports (W G : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : G < 2 ^ 30) :
    SeqPorts (ue.e W G) [("clk", 1), ("en", 1), ("d", W)] [("q", W + G)] := by
  sv_interface

/-! ## 2. The slot equation -/

/-- The view, in declaration order. -/
def ueView (c e d q : LVec) : SvState := [("clk", c), ("en", e), ("d", d), ("q", q)]

/-- Bit 0 of a signal, as the edge table reads it. -/
def b0 (x : LVec) : Logic := x.bits[0]?.getD .lx

/-- IEEE 1800-2017 §9.4.2: a rise is 0→1, 0→x, 0→z, x→1, z→1. -/
def rise (a b : LVec) : Bool := isPosedge (b0 a) (b0 b)

/-- **The contract function**: `q` after a row that moves the clock from `c` to `c1`, with the enable `e1` and the
data `d1` after the row. -/
def ueNext (W G : Nat) (c q c1 e1 d1 : LVec) : LVec :=
  if rise c c1 = true then
    if e1.condTrue = true then d1.resizeU (W + G) else q
  else q

set_option maxHeartbeats 4000000 in
/-- **The slot equation**, computed from the route's own definitions on a symbolic view. -/
theorem ue_row (W G : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : G < 2 ^ 30) {E : CoreMemDesign}
    (hE : ue.e W G = .ok E) (c e d q c1 e1 d1 : LVec) (hc : c.width = 1) (he : e.width = 1) (hd : d.width = W)
    (hq : q.width = W + G) (hc1 : c1.width = 1) (he1 : e1.width = 1) (hd1 : d1.width = W) (mv : MemV) :
    E.slotV (ueView c e d q) mv [("clk", c1), ("en", e1), ("d", d1)] =
      .ok (ueView c1 e1 d1 (ueNext W G c q c1 e1 d1), mv) := by
  sv_seq_inst [ue.e, ue.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (ueView c e d q) mv [("clk", c1), ("en", e1), ("d", d1)] using hE
      [ueView, hc, he, hd, hq, hc1, he1, hd1]
  rw [hcyc]
  simp only [seqE_getElem_zero, ueView, ueNext, rise, b0]
  rfl

/-! ## 3. The facts of the design -/

set_option maxHeartbeats 4000000 in
theorem ue_facts (W G : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : G < 2 ^ 30) {E : CoreMemDesign}
    (hE : ue.e W G = .ok E) :
    E.SeqProfileI ∧ E.seqOblI = true ∧
      (∀ v, E.ShapeV v ↔ ∃ c e d q : LVec, v = ueView c e d q ∧ c.width = 1 ∧ e.width = 1 ∧ d.width = W ∧
        q.width = W + G) ∧
      (∀ r v, E.appliedRow r v = [("clk", appliedIn r v "clk"), ("en", appliedIn r v "en"),
        ("d", appliedIn r v "d")]) ∧
      E.scalar.toDesign2.inputNames.toList = ["clk", "en", "d"] ∧
      E.scalar.toDesign2.declWidth "clk" = some 1 ∧ E.scalar.toDesign2.declWidth "en" = some 1 ∧
      E.scalar.toDesign2.declWidth "d" = some W := by
  obtain ⟨E', hE', hP, hO⟩ := ue_structure W G h1 h2 h3
  rw [hE] at hE'
  cases hE'
  refine ⟨hP.toSeqProfileI, CoreMemDesign.seqOblB_I hO, ?_⟩
  sv_seq_inst [ue.e, ue.pdesign] at hE
  subst hE
  refine ⟨fun v => ?_, fun r v => by simp [CoreMemDesign.appliedRow, Elab.toDesign2, Design2.inputNames],
    by simp [Elab.toDesign2, Design2.inputNames], by simp [Elab.toDesign2, Design2.declWidth],
    by simp [Elab.toDesign2, Design2.declWidth], by simp [Elab.toDesign2, Design2.declWidth]⟩
  constructor
  · rintro ⟨hk, hw⟩
    rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hk hw
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
    exact ⟨x1, x2, x3, x4, rfl, hw⟩
  · rintro ⟨c, e, d, q, rfl, hc, he, hd, hq⟩
    exact ⟨by simp [ueView], by simp [ueView, hc, he, hd, hq]⟩

/-! ## 4. The contract: every coherent state, every typed row -/

set_option maxHeartbeats 4000000 in
/-- **THE CONTRACT.** From every coherent state (the x start, the time-zero state, every state a run reaches), on
every typed input row (any subset of the inputs, any 4-state values), the route's step succeeds, the state after it is
coherent again, and its view is the applied inputs with `q' = ueNext …`. -/
theorem ue_step (W G : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : G < 2 ^ 30) {E : CoreMemDesign}
    (hE : ue.e W G = .ok E) (st : CoreMemState) (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    (row : SvState) (hty : EntryTyped E.scalar.toDesign2 row) :
    ∃ st', E.step st row = .ok st' ∧ E.Coherent st' ∧ E.MemCoherent st'.memory ∧
      ∃ c e d q : LVec, CoreMemState.view E st = ueView c e d q ∧
        c.width = 1 ∧ e.width = 1 ∧ d.width = W ∧ q.width = W + G ∧
        let v := ueView c e d q
        CoreMemState.view E st' =
          ueView (appliedIn row v "clk") (appliedIn row v "en") (appliedIn row v "d")
            (ueNext W G c q (appliedIn row v "clk") (appliedIn row v "en") (appliedIn row v "d")) := by
  obtain ⟨hP, hO, hsh, happ, hin, hwc, hwe, hwd⟩ := ue_facts W G h1 h2 h3 hE
  obtain ⟨c, e, d, q, hv, hc', he, hd, hq⟩ := (hsh _).mp hc.shape
  have w1 := CoreMemDesign.appliedIn_width_row hty (n := "clk") (x := c) (v := ueView c e d q) (by simp [hin]) hwc
    (by simp [ueView, SvState.lookup]) hc'
  have w2 := CoreMemDesign.appliedIn_width_row hty (n := "en") (x := e) (v := ueView c e d q) (by simp [hin]) hwe
    (by simp [ueView, SvState.lookup]) he
  have w3 := CoreMemDesign.appliedIn_width_row hty (n := "d") (x := d) (v := ueView c e d q) (by simp [hin]) hwd
    (by simp [ueView, SvState.lookup]) hd
  have hslot := ue_row W G h1 h2 h3 hE c e d q _ _ _ hc' he hd hq w1 w2 w3 (E.memOf st.memory)
  rw [← happ, ← CoreMemDesign.slotV_applied hP ((hsh _).mpr ⟨c, e, d, q, rfl, hc', he, hd, hq⟩), ← hv] at hslot
  obtain ⟨st', hs', hv', -, hc1, hmc1⟩ := CoreMemDesign.step_seqI hP hO hc hmc hty hslot
  rw [hv] at hv'
  exact ⟨st', hs', hc1, hmc1, c, e, d, q, hv, hc', he, hd, hq, hv'⟩

/-! ## 5. Reading the contract -/

/-- Load on known data: the clock rose and the enable reads true: `q` is the data zero-extended to `W + G` bits. -/
theorem ue_load_known {W G : Nat} {c q c1 e1 : LVec} (x : BitVec W) (hr : rise c c1 = true)
    (he : e1.condTrue = true) :
    ueNext W G c q c1 e1 (LVec.ofBitVec x) = LVec.ofBitVec (x.zeroExtend (W + G)) := by
  simp [ueNext, hr, he]

/-- Hold: no rise of the clock, or the enable does not read true (0, x or z): `q` holds. -/
theorem ue_hold {W G : Nat} {c q c1 e1 d1 : LVec} (h : rise c c1 = false ∨ e1.condTrue = false) :
    ueNext W G c q c1 e1 d1 = q := by
  rcases h with h | h <;> simp [ueNext, h]

#print axioms ue_structure
#print axioms ue_ports
#print axioms ue_row
#print axioms ue_facts
#print axioms ue_step
#print axioms ue_load_known
#print axioms ue_hold

end Examples.«system-verilog».seq_cycle.unsigned_proof
