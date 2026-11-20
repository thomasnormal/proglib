import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# A conditional generate construct: an optional register stage, at every `W ≥ 1` and every `REG`

The design (`gen_bypass.sv`):

```systemverilog
module gen_bypass #(parameter int W = 4, parameter int REG = 1)
  (input logic clk, en, input logic [W-1:0] d, output logic [W-1:0] q);
  generate if (REG > 0) begin : g_reg
    logic [W-1:0] r;
    always_ff @(posedge clk) if (en) r <= d;
    assign q = r;
  end else begin : g_wire
    assign q = d;
  end endgenerate
endmodule
```

The route instantiates the arm its condition selects (`evalGenGuard`, IEEE 1800-2017 §27.5) with the declarations of
that arm; the other arm does not exist. The clocked instantiation pass evaluates the condition at symbolic
parameters and decides it from the hypotheses on the parameters, so the family splits where the design does: one
structure theorem for `1 ≤ REG` (every such `REG`: the register arm) and one for `REG = 0` (the wire arm). Nothing is
unrolled or rewritten: each theorem is about the loaded design at its parameters.

1. **Structure** (`gb_reg_structure`, `gb_wire_structure`).
2. **The register arm** (`gb_reg_row`, `gb_reg_step`): from every coherent state, on every typed 4-state input row,
   the route's step succeeds and `r` (and `q`, its continuous assign) is `gbNext`: the data on a rise of the clock
   with `en` reading true, else held.
3. **The wire arm** (`gb_wire_row`): the slot's `q` is the applied `d`, whatever the clock does.

Oracle: Icarus Verilog 12.0 (stable). The four runs below ((W, REG) = (4, 1), (1, 3), (4, 0), (8, 0); 14 rows each,
with x and z on the clock, the enable and the data, from the x start) are the rows of a testbench outside the
repository; the expected lists are Icarus's samples of `q` one time unit after each row (56 rows, 0 mismatches). No
Xcelium result is claimed.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.gen_proof

load_design_sv2 gb from "Examples/system-verilog/seq_cycle/gen_bypass.sv.json"

/-! ## 0. Runs of the route against Icarus Verilog 12.0 -/

#guard (match gb.e 4 1 with
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
        ["xxxx", "1101", "1101", "0110", "0110", "0110", "0110", "1001", "1001", "z1x0", "z1x0", "z1x0", "z1x0", "0011"]
    | _ => false
  | _ => false)


#guard (match gb.e 1 3 with
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


#guard (match gb.e 4 0 with
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
        ["1101", "1101", "0110", "0110", "1001", "1001", "1001", "1001", "z1x0", "z1x0", "0011", "0011", "0011", "0011"]
    | _ => false
  | _ => false)


#guard (match gb.e 8 0 with
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
        ["00001101", "00001101", "00000110", "00000110", "00001001", "00001001", "00001001", "00001001", "z1x0z1x0", "z1x0z1x0", "00000011", "00000011", "00000011", "00000011"]
    | _ => false
  | _ => false)


/-! ## 1. Structure -/

set_option maxHeartbeats 4000000 in
theorem gb_reg_structure (W REG : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : 1 ≤ REG) (h4 : REG < 2 ^ 30) :
    SeqDesign (gb.e W REG) "clk" := by
  sv_structure

set_option maxHeartbeats 4000000 in
theorem gb_wire_structure (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) : SeqDesign (gb.e W 0) "clk" := by
  sv_structure

set_option maxHeartbeats 4000000 in
theorem gb_reg_ports (W REG : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : 1 ≤ REG) (h4 : REG < 2 ^ 30) :
    SeqPorts (gb.e W REG) [("clk", 1), ("en", 1), ("d", W)] [("q", W)] := by
  sv_interface

/-! ## 2. The register arm (`1 ≤ REG`) -/

/-- The view of the register arm, in declaration order (the generate block's `r` after the ports). -/
def regView (c e d q r : LVec) : SvState := [("clk", c), ("en", e), ("d", d), ("q", q), ("r", r)]

/-- Bit 0 of a signal, as the edge table reads it. -/
def b0 (x : LVec) : Logic := x.bits[0]?.getD .lx

/-- IEEE 1800-2017 §9.4.2: a rise is 0→1, 0→x, 0→z, x→1, z→1. -/
def rise (a b : LVec) : Bool := isPosedge (b0 a) (b0 b)

/-- **The contract function**: the register after a row that moves the clock from `c` to `c1`, with the enable `e1`
and the data `d1` after the row. -/
def gbNext (c r c1 e1 d1 : LVec) : LVec :=
  if rise c c1 = true then
    if e1.condTrue = true then d1 else r
  else r

set_option maxHeartbeats 4000000 in
/-- **The slot equation of the register arm**: `r` is `gbNext`, and `q` shows it. -/
theorem gb_reg_row (W REG : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : 1 ≤ REG) (h4 : REG < 2 ^ 30)
    {E : CoreMemDesign} (hE : gb.e W REG = .ok E) (c e d q r c1 e1 d1 : LVec) (hc : c.width = 1)
    (he : e.width = 1) (hd : d.width = W) (hq : q.width = W) (hr : r.width = W) (hc1 : c1.width = 1)
    (he1 : e1.width = 1) (hd1 : d1.width = W) (mv : MemV) :
    E.slotV (regView c e d q r) mv [("clk", c1), ("en", e1), ("d", d1)] =
      .ok (regView c1 e1 d1 (gbNext c r c1 e1 d1) (gbNext c r c1 e1 d1), mv) := by
  sv_seq_inst [gb.e, gb.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (regView c e d q r) mv [("clk", c1), ("en", e1), ("d", d1)] using hE
      [regView, hc, he, hd, hq, hr, hc1, he1, hd1]
  rw [hcyc]
  simp only [seqE_getElem_zero, regView, gbNext, rise, b0]
  rfl

set_option maxHeartbeats 4000000 in
theorem gb_reg_facts (W REG : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : 1 ≤ REG) (h4 : REG < 2 ^ 30)
    {E : CoreMemDesign} (hE : gb.e W REG = .ok E) :
    E.SeqProfileI ∧ E.seqOblI = true ∧
      (∀ v, E.ShapeV v ↔ ∃ c e d q r : LVec, v = regView c e d q r ∧ c.width = 1 ∧ e.width = 1 ∧ d.width = W ∧
        q.width = W ∧ r.width = W) ∧
      (∀ r v, E.appliedRow r v = [("clk", appliedIn r v "clk"), ("en", appliedIn r v "en"),
        ("d", appliedIn r v "d")]) ∧
      E.scalar.toDesign2.inputNames.toList = ["clk", "en", "d"] ∧
      E.scalar.toDesign2.declWidth "clk" = some 1 ∧ E.scalar.toDesign2.declWidth "en" = some 1 ∧
      E.scalar.toDesign2.declWidth "d" = some W := by
  obtain ⟨E', hE', hP, hO⟩ := gb_reg_structure W REG h1 h2 h3 h4
  rw [hE] at hE'
  cases hE'
  refine ⟨hP.toSeqProfileI, CoreMemDesign.seqOblB_I hO, ?_⟩
  sv_seq_inst [gb.e, gb.pdesign] at hE
  subst hE
  refine ⟨fun v => ?_, fun r v => by simp [CoreMemDesign.appliedRow, Elab.toDesign2, Design2.inputNames],
    by simp [Elab.toDesign2, Design2.inputNames], by simp [Elab.toDesign2, Design2.declWidth],
    by simp [Elab.toDesign2, Design2.declWidth], by simp [Elab.toDesign2, Design2.declWidth]⟩
  constructor
  · rintro ⟨hk, hw⟩
    rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨⟨n5, x5⟩, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      simp at hk hw
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk
    exact ⟨x1, x2, x3, x4, x5, rfl, hw⟩
  · rintro ⟨c, e, d, q, r, rfl, hc, he, hd, hq, hr⟩
    exact ⟨by simp [regView], by simp [regView, hc, he, hd, hq, hr]⟩

set_option maxHeartbeats 4000000 in
/-- **THE CONTRACT of the register arm.** From every coherent state, on every typed input row (any subset of the
inputs, any 4-state values), the route's step succeeds, the state after it is coherent again, and both `r` and `q`
are `gbNext` of the state's `r` and the applied inputs. -/
theorem gb_reg_step (W REG : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h3 : 1 ≤ REG) (h4 : REG < 2 ^ 30)
    {E : CoreMemDesign} (hE : gb.e W REG = .ok E) (st : CoreMemState) (hc : E.Coherent st)
    (hmc : E.MemCoherent st.memory) (row : SvState) (hty : EntryTyped E.scalar.toDesign2 row) :
    ∃ st', E.step st row = .ok st' ∧ E.Coherent st' ∧ E.MemCoherent st'.memory ∧
      ∃ c e d q r : LVec, CoreMemState.view E st = regView c e d q r ∧
        c.width = 1 ∧ e.width = 1 ∧ d.width = W ∧ q.width = W ∧ r.width = W ∧
        let v := regView c e d q r
        let n := gbNext c r (appliedIn row v "clk") (appliedIn row v "en") (appliedIn row v "d")
        CoreMemState.view E st' =
          regView (appliedIn row v "clk") (appliedIn row v "en") (appliedIn row v "d") n n := by
  obtain ⟨hP, hO, hsh, happ, hin, hwc, hwe, hwd⟩ := gb_reg_facts W REG h1 h2 h3 h4 hE
  obtain ⟨c, e, d, q, r, hv, hc', he, hd, hq, hr⟩ := (hsh _).mp hc.shape
  have w1 := CoreMemDesign.appliedIn_width_row hty (n := "clk") (x := c) (v := regView c e d q r) (by simp [hin])
    hwc (by simp [regView, SvState.lookup]) hc'
  have w2 := CoreMemDesign.appliedIn_width_row hty (n := "en") (x := e) (v := regView c e d q r) (by simp [hin]) hwe
    (by simp [regView, SvState.lookup]) he
  have w3 := CoreMemDesign.appliedIn_width_row hty (n := "d") (x := d) (v := regView c e d q r) (by simp [hin]) hwd
    (by simp [regView, SvState.lookup]) hd
  have hslot := gb_reg_row W REG h1 h2 h3 h4 hE c e d q r _ _ _ hc' he hd hq hr w1 w2 w3 (E.memOf st.memory)
  rw [← happ, ← CoreMemDesign.slotV_applied hP ((hsh _).mpr ⟨c, e, d, q, r, rfl, hc', he, hd, hq, hr⟩), ← hv]
    at hslot
  obtain ⟨st', hs', hv', -, hc1, hmc1⟩ := CoreMemDesign.step_seqI hP hO hc hmc hty hslot
  rw [hv] at hv'
  exact ⟨st', hs', hc1, hmc1, c, e, d, q, r, hv, hc', he, hd, hq, hr, hv'⟩

/-- Hold: no rise of the clock, or the enable does not read true (0, x or z): the register holds. -/
theorem gb_hold {c r c1 e1 d1 : LVec} (h : rise c c1 = false ∨ e1.condTrue = false) : gbNext c r c1 e1 d1 = r := by
  rcases h with h | h <;> simp [gbNext, h]

/-- Load: the clock rose and the enable reads true: the register takes the data, bit for bit. -/
theorem gb_load {c r c1 e1 d1 : LVec} (hr : rise c c1 = true) (he : e1.condTrue = true) :
    gbNext c r c1 e1 d1 = d1 := by
  simp [gbNext, hr, he]

/-! ## 3. The wire arm (`REG = 0`) -/

/-- The view of the wire arm, in declaration order (no `r`: the register arm does not exist at `REG = 0`). -/
def wireView (c e d q : LVec) : SvState := [("clk", c), ("en", e), ("d", d), ("q", q)]

set_option maxHeartbeats 4000000 in
/-- **The slot equation of the wire arm**: `q` is the applied data, whatever the clock and the enable do. -/
theorem gb_wire_row (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : gb.e W 0 = .ok E)
    (c e d q c1 e1 d1 : LVec) (hc : c.width = 1) (he : e.width = 1) (hd : d.width = W) (hq : q.width = W)
    (hc1 : c1.width = 1) (he1 : e1.width = 1) (hd1 : d1.width = W) (mv : MemV) :
    E.slotV (wireView c e d q) mv [("clk", c1), ("en", e1), ("d", d1)] = .ok (wireView c1 e1 d1 d1, mv) := by
  sv_seq_inst [gb.e, gb.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (wireView c e d q) mv [("clk", c1), ("en", e1), ("d", d1)] using hE
      [wireView, hc, he, hd, hq, hc1, he1, hd1]
  rw [hcyc]
  simp only [wireView]

#print axioms gb_reg_structure
#print axioms gb_wire_structure
#print axioms gb_reg_ports
#print axioms gb_reg_row
#print axioms gb_reg_facts
#print axioms gb_reg_step
#print axioms gb_hold
#print axioms gb_load
#print axioms gb_wire_row

end Examples.«system-verilog».seq_cycle.gen_proof
