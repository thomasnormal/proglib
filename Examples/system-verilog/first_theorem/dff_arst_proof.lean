import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# A clocked module's step contract, for every width, every state and every 4-state input row

The clocked worked example of `README.md` in this directory. The design is `dff_arst.sv`, a `W`-bit D register with
an active-low asynchronous reset:

```systemverilog
module dff_arst #(parameter int W = 4)
  (input logic clk, rst_n, input logic [W-1:0] d, output logic [W-1:0] q);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= '0;
    else q <= d;
endmodule
```

To adapt the file to another clocked module: change the envelope path, the view (one value per declaration, in
declaration order), the contract function and the widths. The proof text of sections 1, 3 and 4 stays as it is up to
those names.

The envelope is generated, never edited. From the repository root:

```console
$ python3.12 extractors/sv/extract.py --top dff_arst Examples/system-verilog/first_theorem/dff_arst.sv \
    -o Examples/system-verilog/first_theorem/dff_arst.sv.json
```

Oracle: Icarus Verilog 12.0 (stable), the testbench in `README.md`, on the stimulus of section 6 at `W = 4`: the 12
rows agree.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».first_theorem.dff_arst_proof

load_design_sv2 dff from "Examples/system-verilog/first_theorem/dff_arst.sv.json"

/-! ## 1. Structure: the design instantiates in the clocked profile (any number of edge events) -/

set_option maxHeartbeats 4000000 in
theorem dff_structure (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) : SeqDesignI (dff.e W) := by
  sv_structure

/-! ## 2. What you write: the view (declaration order), the contract function, the slot equation -/

/-- The view: one value per declaration, in declaration order (see `hE` after `sv_seq_inst`, field `decls`). -/
def dfView (c r d q : LVec) : SvState := [("clk", c), ("rst_n", r), ("d", d), ("q", q)]

/-- Bit 0 of a signal, as the edge table reads it. -/
def b0 (x : LVec) : Logic := x.bits[0]?.getD .lx

/-- IEEE 1800-2023 §9.4.2: a rise is 0→1, 0→x, 0→z, x→1, z→1; a fall is 1→0, 1→x, 1→z, x→0, z→0. -/
def rise (a b : LVec) : Bool := isPosedge (b0 a) (b0 b)
def fall (a b : LVec) : Bool := isNegedge (b0 a) (b0 b)

/-- **The contract function**: `q` after a row. Written by reading `hcyc` (the computed slot equation) once. -/
def dfNext (W : Nat) (c r q c1 r1 d1 : LVec) : LVec :=
  if rise c c1 = true ∨ fall r r1 = true then
    if (evalUnaryOp .lnot r1).condTrue = true then LVec.ofBitVec 0#W else d1
  else q

set_option maxHeartbeats 4000000 in
/-- **The slot equation**, computed from the semantics' own definitions on a symbolic view. -/
theorem dff_row (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : dff.e W = .ok E)
    (c r d q c1 r1 d1 : LVec) (hc : c.width = 1) (hr : r.width = 1) (hd : d.width = W) (hq : q.width = W)
    (hc1 : c1.width = 1) (hr1 : r1.width = 1) (hd1 : d1.width = W) (mv : MemV) :
    E.slotV (dfView c r d q) mv [("clk", c1), ("rst_n", r1), ("d", d1)] =
      .ok (dfView c1 r1 d1 (dfNext W c r q c1 r1 d1), mv) := by
  sv_seq_inst [dff.e, dff.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (dfView c r d q) mv [("clk", c1), ("rst_n", r1), ("d", d1)] using hE
      [dfView, hc, hr, hd, hq, hc1, hr1, hd1]
  -- put `trace_state` here to read `hcyc`: it IS the design's behaviour; `dfNext` is its `q` entry
  rw [hcyc]
  simp only [seqE_getElem_zero, dfView, dfNext, rise, fall, b0]
  rfl

/-! ## 3. The facts of the design (plumbing: shape of a view, the input list, the widths) -/

set_option maxHeartbeats 4000000 in
theorem dff_facts (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : dff.e W = .ok E) :
    E.SeqProfileI ∧ E.seqOblI = true ∧
      (∀ v, E.ShapeV v ↔ ∃ c r d q : LVec, v = dfView c r d q ∧ c.width = 1 ∧ r.width = 1 ∧ d.width = W ∧
        q.width = W) ∧
      (∀ r v, E.appliedRow r v = [("clk", appliedIn r v "clk"), ("rst_n", appliedIn r v "rst_n"),
        ("d", appliedIn r v "d")]) ∧
      E.scalar.toDesign2.inputNames.toList = ["clk", "rst_n", "d"] ∧
      E.scalar.toDesign2.declWidth "clk" = some 1 ∧ E.scalar.toDesign2.declWidth "rst_n" = some 1 ∧
      E.scalar.toDesign2.declWidth "d" = some W := by
  obtain ⟨E', hE', hP, hO⟩ := dff_structure W h1 h2
  rw [hE] at hE'
  cases hE'
  refine ⟨hP, hO, ?_⟩
  sv_seq_inst [dff.e, dff.pdesign] at hE
  subst hE
  refine ⟨fun v => ?_, fun r v => by simp [CoreMemDesign.appliedRow, Elab.toDesign2, Design2.inputNames],
    by simp [Elab.toDesign2, Design2.inputNames], by simp [Elab.toDesign2, Design2.declWidth],
    by simp [Elab.toDesign2, Design2.declWidth], by simp [Elab.toDesign2, Design2.declWidth]⟩
  constructor
  · rintro ⟨hk, hw⟩
    -- one `⟨⟨n, x⟩, _ | …⟩` per declaration, then the closing `_ | ⟨_, _⟩`
    rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hk hw
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
    exact ⟨x1, x2, x3, x4, rfl, hw⟩
  · rintro ⟨c, r, d, q, rfl, hc, hr, hd, hq⟩
    exact ⟨by simp [dfView], by simp [dfView, hc, hr, hd, hq]⟩

/-! ## 4. The contract: every coherent state, every typed row -/

set_option maxHeartbeats 4000000 in
/-- **THE CONTRACT.** From every coherent state `st` (the x start, the time-zero state, every state a run reaches),
on every typed input row (any subset of the inputs, any 4-state values), the semantics' step succeeds, the state
after it is coherent again, and its view is the applied inputs with `q' = dfNext …`. `appliedIn row v n` is the
row's value for `n` when the row drives `n`, else the value `v` holds. -/
theorem dff_step (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : dff.e W = .ok E)
    (st : CoreMemState) (hc : E.Coherent st) (hmc : E.MemCoherent st.memory) (row : SvState)
    (hty : EntryTyped E.scalar.toDesign2 row) :
    ∃ st', E.step st row = .ok st' ∧ E.Coherent st' ∧ E.MemCoherent st'.memory ∧
      ∃ c r d q : LVec, CoreMemState.view E st = dfView c r d q ∧
        c.width = 1 ∧ r.width = 1 ∧ d.width = W ∧ q.width = W ∧
        let v := dfView c r d q
        CoreMemState.view E st' =
          dfView (appliedIn row v "clk") (appliedIn row v "rst_n") (appliedIn row v "d")
            (dfNext W c r q (appliedIn row v "clk") (appliedIn row v "rst_n") (appliedIn row v "d")) := by
  obtain ⟨hP, hO, hsh, happ, hin, hwc, hwr, hwd⟩ := dff_facts W h1 h2 hE
  obtain ⟨c, r, d, q, hv, hc', hr, hd, hq⟩ := (hsh _).mp hc.shape
  have w1 := CoreMemDesign.appliedIn_width_row hty (n := "clk") (x := c) (v := dfView c r d q) (by simp [hin]) hwc
    (by simp [dfView, SvState.lookup]) hc'
  have w2 := CoreMemDesign.appliedIn_width_row hty (n := "rst_n") (x := r) (v := dfView c r d q) (by simp [hin]) hwr
    (by simp [dfView, SvState.lookup]) hr
  have w3 := CoreMemDesign.appliedIn_width_row hty (n := "d") (x := d) (v := dfView c r d q) (by simp [hin]) hwd
    (by simp [dfView, SvState.lookup]) hd
  have hslot := dff_row W h1 h2 hE c r d q _ _ _ hc' hr hd hq w1 w2 w3 (E.memOf st.memory)
  rw [← happ, ← CoreMemDesign.slotV_applied hP ((hsh _).mpr ⟨c, r, d, q, rfl, hc', hr, hd, hq⟩), ← hv] at hslot
  obtain ⟨st', hs', hv', -, hc1, hmc1⟩ := CoreMemDesign.step_seqI hP hO hc hmc hty hslot
  rw [hv] at hv'
  exact ⟨st', hs', hc1, hmc1, c, r, d, q, hv, hc', hr, hd, hq, hv'⟩

/-- The contract applies to runs: the x start is coherent with a coherent memory, and `dff_step` keeps both. -/
theorem dff_start (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : dff.e W = .ok E) :
    E.Coherent E.initial ∧ E.MemCoherent E.initial.memory :=
  ⟨E.initial_coherent, CoreMemDesign.initial_memCoherent (dff_facts W h1 h2 hE).1.mems⟩

/-! ## 5. Reading the contract: the clauses an engineer states -/

theorem eq_b0 {x : LVec} (h : x.width = 1) : x = ⟨#[b0 x]⟩ := (LVec.eq_bit0 h).symm

/-- `!r` reads true exactly when the one-bit `r` is 0: an x or z reset does not read as asserted (IEEE 1800-2023
§12.4: an `if` whose condition is x or z runs its `else` branch). -/
theorem lnot_condTrue {r : LVec} (h : r.width = 1) : (evalUnaryOp .lnot r).condTrue = (b0 r == .l0) := by
  rw [eq_b0 h]
  cases b0 r <;> simp [evalUnaryOp, LVec.lnot, LVec.condTrue, LVec.isKnownZero, LVec.ofLogic, b0] <;> decide

/-- Reset: the process fired and the reset is 0 after the row: `q` is 0. -/
theorem dff_reset {W : Nat} {c r q c1 r1 d1 : LVec} (hr1 : r1.width = 1)
    (hfire : rise c c1 = true ∨ fall r r1 = true) (hlow : b0 r1 = .l0) :
    dfNext W c r q c1 r1 d1 = LVec.ofBitVec 0#W := by
  simp [dfNext, hfire, lnot_condTrue hr1, hlow]

/-- Load: the process fired and the reset is not 0 after the row (1, x or z): `q` is the applied `d`, bit for bit. -/
theorem dff_load {W : Nat} {c r q c1 r1 d1 : LVec} (hr1 : r1.width = 1)
    (hfire : rise c c1 = true ∨ fall r r1 = true) (hhigh : b0 r1 ≠ .l0) : dfNext W c r q c1 r1 d1 = d1 := by
  simp [dfNext, hfire, lnot_condTrue hr1, hhigh]

/-- Hold: no rise of the clock and no fall of the reset: `q` holds. -/
theorem dff_hold {W : Nat} {c r q c1 r1 d1 : LVec} (hc : rise c c1 = false) (hr : fall r r1 = false) :
    dfNext W c r q c1 r1 d1 = q := by
  simp [dfNext, hc, hr]

/-! ## 6. Non-vacuity

A compiled run of the semantics at `W = 4` from the x start, one row per line, with x and z on the clock, the reset and
the data. Row 3 is the asynchronous reset: `rst_n` falls while `clk` stays 1, and `q` clears with no clock edge. Row 8
is the reset falling 1→x: the process fires and `!rst_n` reads x, so the `else` branch loads `d`. Row 10 is 0→z on the
reset, a rise and not a fall: no event. -/

#guard (match dff.e 4 with
  | .ok E => match runCoreMemRows E E.initial
      [[("rst_n", .ofNat 1 1), ("clk", .ofNat 1 0), ("d", .ofNat 4 5)],
       [("clk", .ofNat 1 1)],
       [("rst_n", .ofNat 1 0)],
       [("clk", .ofNat 1 0), ("rst_n", .ofNat 1 1)],
       [("clk", ⟨#[.lx]⟩)],
       [("d", .xVec 4)],
       [("clk", .ofNat 1 1)],
       [("d", .ofNat 4 3), ("rst_n", ⟨#[.lx]⟩)],
       [("rst_n", .ofNat 1 0)],
       [("rst_n", ⟨#[.lz]⟩), ("d", .ofNat 4 10)],
       [("clk", .ofNat 1 0)],
       [("clk", ⟨#[.lz]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxx", "0101", "0000", "0000", "0101", "0101", "xxxx", "0011", "0000", "0000", "0000", "1010"]
    | _ => false
  | _ => false)

/-- A WRONG contract, kept to show that the slot equation's check bites: the contract of a register with a
SYNCHRONOUS reset (the process fires on the clock's rise only). -/
def dfSync (W : Nat) (c _r q c1 r1 d1 : LVec) : LVec :=
  if rise c c1 = true then
    if (evalUnaryOp .lnot r1).condTrue = true then LVec.ofBitVec 0#W else d1
  else q

-- The linter reads the final proof term, which is only `trivial` here: every hypothesis would be reported unused.
set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
/-- A wrong contract fails: the computed slot equation (the first two steps of `dff_row`, which succeed) does not
close the slot equation stated with `dfSync` (the last three steps of `dff_row`, with `dfSync` unfolded in place of
`dfNext`, fail on it, at `rfl`). -/
example (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) {E : CoreMemDesign} (hE : dff.e W = .ok E)
    (c r d q c1 r1 d1 : LVec) (hc : c.width = 1) (hr : r.width = 1) (hd : d.width = W) (hq : q.width = W)
    (hc1 : c1.width = 1) (hr1 : r1.width = 1) (hd1 : d1.width = W) (mv : MemV) : True := by
  sv_seq_inst [dff.e, dff.pdesign] at hE
  sv_seq_cycle hcyc : E.slotV (dfView c r d q) mv [("clk", c1), ("rst_n", r1), ("d", d1)] using hE
      [dfView, hc, hr, hd, hq, hc1, hr1, hd1]
  fail_if_success
    have : E.slotV (dfView c r d q) mv [("clk", c1), ("rst_n", r1), ("d", d1)] =
        .ok (dfView c1 r1 d1 (dfSync W c r q c1 r1 d1), mv) := by
      rw [hcyc]
      simp only [seqE_getElem_zero, dfView, dfSync, rise, b0]
      rfl
  trivial

/-! ## 7. The axioms: only `propext`, `Classical.choice`, `Quot.sound` -/

#print axioms dff_structure
#print axioms dff_row
#print axioms dff_facts
#print axioms dff_step
#print axioms dff_start
#print axioms dff_reset
#print axioms dff_load
#print axioms dff_hold

end Examples.«system-verilog».first_theorem.dff_arst_proof
