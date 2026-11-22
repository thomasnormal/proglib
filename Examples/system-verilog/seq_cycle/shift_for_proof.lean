import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# A shift register written with a procedural `for` loop, at every depth `N` and width `W`, over every run

```systemverilog
module shift_for #(parameter int W = 8, parameter int N = 4)
  (input logic clk, input logic [W-1:0] d, output logic [W-1:0] q);
  logic [W-1:0] pipe [0:N-1];
  always_ff @(posedge clk) begin
    pipe[0] <= d;
    for (int i = 1; i < N; i++) pipe[i] <= pipe[i-1];
  end
  assign q = pipe[N-1];
endmodule
```

The loop is never unrolled. The route runs it as the header's value list (`forValues2`: for this header the list
`intRange 1 (N - 1)`, a function of the parameter) and the body folded over it under the iterator's binding; the
clocked views mirror exactly that (`execLoopV`), and the cycle equations carry the loop as ONE write equation over the
list (`memWriteL`). Its closed form is the shift: element 0 loads `d`, element `k` loads what element `k - 1` held
BEFORE the edge (nonblocking assignments sample at issue, IEEE 1800-2017 §10.4.2), 4-state exact.

1. **Structure** (`sf_structure`, `sv_structure`): the instantiation at every `1 ≤ W < 2^30`, `1 ≤ N ≤ 4000`, in the
   clocked profile with the obligations. The bound on `N` is a fact about the route, visible here as a hypothesis:
   the route runs a loop one unit of its statement fuel (4096) per iteration and answers `timeout` beyond
   (`PStmt.need`: `2 + trips + need body`); the stage bounds the trip count `N - 1` by `omega` from `h2`.
2. **The cycle equations** (`sf_cycle`): one cycle is `sfF`: the post memory is `shiftM` (`sf_post`: the loop's write
   equation in closed form), `q` shows element `N - 1`.
3. **The claim over every run** (`sf_runs`), from every coherent state (the x start, every power-up contents), on every
   typed stimulus: `pipe' k = if k = 0 then d else pipe (k - 1)` for every `0 ≤ k < N` in every cycle, the low slot
   writing nothing, `q = pipe (N - 1)`; and THE DELAY (`sf_runs_delay`): the post sample of `q` in cycle `c + N - 1`
   is the `d` applied in cycle `c`, whatever the earlier contents were.
4. **The same register written with a plain `always`**, a module-level `integer i` and the step `i = i + 1`
   (`shift_v2001.sv`; `sp_structure`, `sp_cycle`, `sp_runs`, `sp_runs_delay`): the same cycle function, the same claim.

Oracle: Icarus Verilog 12.0 (stable). The `#guard` runs below are the route's runs (`runCoreMemRows` from the x start);
their expected lists are Icarus's samples of the same row stimuli (a row is a set of input changes at one instant,
sampled one time unit later), at `(W, N)` = (8, 4), (1, 2), (4, 3), (3, 1): 88 rows, with x and z on `clk` (a 0 → x and
a 0 → z transition are rises, §9.4.2) and on `d`. No Xcelium result is claimed.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.shift_for_proof

set_option maxRecDepth 100000 in
load_design_sv2 sf from "Examples/system-verilog/seq_cycle/shift_for.sv.json"

-- The instantiation at every width and depth, computed once (`sf.mirror`, `sf.mirror_eq`); the stages read it.
set_option maxHeartbeats 1000000 in
seq_mirror (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) : sf.e W N

/-! ## Runs on the route, against Icarus Verilog 12.0 -/

-- W = 8, N = 4 (28 rows)
#guard (match sf.e 8 4 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l0, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("d", ⟨#[.lz, .l0, .lx, .l1, .lz, .l0, .lx, .l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l0, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "00000101", "00000101", "00000110", "00000110", "00000110", "00000111", "00001000", "00001000", "00001000", "00001001", "00001001", "1x0z1x0z", "1x0z1x0z", "1x0z1x0z", "1x0z1x0z", "00000011", "00000011", "xxxxxxxx", "xxxxxxxx", "00001001", "00001001"]
    | _ => false
  | _ => false)

-- W = 1, N = 2 (20 rows)
#guard (match sf.e 1 2 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0]⟩)],
       [("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["x", "x", "x", "1", "1", "0", "0", "0", "1", "1", "1", "1", "1", "1", "1", "1", "x", "x", "1", "1"]
    | _ => false
  | _ => false)

-- W = 4, N = 3 (24 rows)
#guard (match sf.e 4 3 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l0, .l0, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l0, .l1]⟩)],
       [("d", ⟨#[.lz, .l0, .lx, .l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l0, .l0]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.lx, .lx, .lx, .lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l0, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxx", "xxxx", "xxxx", "xxxx", "xxxx", "0101", "0101", "0110", "0110", "0110", "0111", "1000", "1000", "1000", "1x0z", "1x0z", "1x0z", "1x0z", "0011", "0011", "xxxx", "xxxx", "1001", "1001"]
    | _ => false
  | _ => false)

-- W = 3, N = 1 (16 rows)
#guard (match sf.e 3 1 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l1]⟩)],
       [("d", ⟨#[.l0, .lx, .l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l0]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.lx, .lx, .lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxx", "101", "101", "110", "110", "110", "1x0", "1x0", "1x0", "1x0", "011", "011", "xxx", "xxx", "001", "001"]
    | _ => false
  | _ => false)

/-! ## 1. Structure and interface -/

set_option maxHeartbeats 1000000 in
theorem sf_structure (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqDesign (sf.e W N) "clk" := by
  sv_structure

set_option maxHeartbeats 1000000 in
theorem sf_ports (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqPorts (sf.e W N) [("clk", 1), ("d", W)] [("q", W)] := by
  sv_interface

/-! ## 2. The cycle equations -/

/-- The view of the design, in declaration order. -/
def view (c d q : LVec) : SvState := [("clk", c), ("d", d), ("q", q)]

/-- A signal of a view. -/
def lk (v : SvState) (n : String) : LVec := (SvState.lookup v n).getD ⟨#[]⟩

/-- **The shift**: element 0 of `pipe` loads `d`; element `k` (`1 ≤ k < N`) loads what element `k - 1` held; every
other label and every other memory is unchanged. -/
def shiftM (N : Nat) (mv : MemV) (d : LVec) : MemV := fun n k =>
  if n = "pipe" ∧ 0 ≤ k ∧ k < (N : Int) then (if k = 0 then d else mv "pipe" (k - 1)) else mv n k

/-- **The cycle function**: the applied input; the pre sample reads the memory before the edge; the post memory is the
shift; the post sample reads the shifted memory. -/
def sfF (N : Nat) (σ : SvState × MemV) (dt : SvState) : (SvState × MemV) × (SvState × MemV) :=
  let d := appliedIn dt σ.1 "d"
  let m' := shiftM N σ.2 d
  ((view ⟨#[.l0]⟩ d (σ.2 "pipe" ((N : Int) - 1)), σ.2), (view ⟨#[.l1]⟩ d (m' "pipe" ((N : Int) - 1)), m'))

/-- **The index decision** of the route on the declared range `[0:N-1]` at a loop's index (a 32-bit integer): the label
itself below `N`, nothing at or beyond it (§11.5.1). -/
theorem sf_index {N : Nat} (hN : 1 ≤ N) {m : MemShape} (h0 : m.msb = 0) (h1 : m.lsb = (N : Int) - 1) {i : Int} (hi0 : 0 ≤ i)
    (hi1 : i < 4294967296) : m.index? false (LVec.ofInt 32 i) = if i < (N : Int) then some i else none := by
  rw [seqK_index?_ofInt32 m hi0 hi1]
  have hr : m.inRange i ↔ i < (N : Int) := by
    unfold MemShape.inRange
    rw [h0, h1]
    constructor <;> intro h <;> omega
  by_cases h : i < (N : Int)
  · rw [if_pos h, if_pos (hr.mpr h)]
  · rw [if_neg h, if_neg fun h' => h (hr.mp h')]

/-- **The loop's write equation in closed form**: the write of `d` at element 0 followed by the loop
`for (i = 1; i < N; i++) pipe[i] <= pipe[i-1]` (the loop's values `intRange 1 (N - 1)`, each iteration reading the
memory before the edge) is the shift. Proved from the list's membership (`mem_intRange`), not by unrolling. -/
theorem sf_post {W N : Nat} (h1 : 1 ≤ N) (h2 : N ≤ 4000) {m : MemShape} (h0 : m.msb = 0)
    (hl : m.lsb = (N : Int) - 1) (mv : MemV) (d : LVec) :
    memWriteL (memWrite mv "pipe" (m.index? false (LVec.ofInt 32 0)) d) "pipe" (intRange 1 (N - 1))
        (fun i => m.index? false (LVec.ofInt 32 i))
        (fun i => memRd mv "pipe" (m.index? false (LVec.ofInt 32 (i - 1))) W) = shiftM N mv d := by
  have hkey : ∀ i ∈ intRange 1 (N - 1), m.index? false (LVec.ofInt 32 i) = some i := by
    intro i hi
    rw [mem_intRange] at hi
    rw [sf_index h1 h0 hl (by omega) (by omega), if_pos (by omega)]
  have hzero : m.index? false (LVec.ofInt 32 0) = some 0 := by
    rw [sf_index h1 h0 hl (by omega) (by omega), if_pos (by omega)]
  funext n k
  rw [memWriteL_id hkey, hzero]
  unfold shiftM memWrite
  by_cases hn : n = "pipe"
  · subst hn
    by_cases hk : k ∈ intRange 1 (N - 1)
    · have hk' := mem_intRange.mp hk
      rw [if_pos ⟨rfl, hk⟩, if_pos ⟨rfl, by omega, by omega⟩, if_neg (by omega),
        sf_index h1 h0 hl (by omega) (by omega), if_pos (by omega)]
      rfl
    · have hk' : ¬ (1 ≤ k ∧ k < 1 + ((N - 1 : Nat) : Int)) := fun h => hk (mem_intRange.mpr h)
      rw [if_neg fun h => hk h.2]
      by_cases hk0 : k = 0
      · subst hk0
        rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, by omega, by omega⟩, if_pos rfl]
      · rw [if_neg fun h => hk0 (Option.some.inj h.2).symm, if_neg fun h => hk' ⟨by omega, by omega⟩]
  · rw [if_neg fun h => hn h.1, if_neg fun h => hn h.1, if_neg fun h => hn h.1]

/-- The read of the last element, at the constant index `N - 1`. -/
theorem sf_last {W N : Nat} (h1 : 1 ≤ N) (h2 : N ≤ 4000) {m : MemShape} (h0 : m.msb = 0)
    (hl : m.lsb = (N : Int) - 1) (mv : MemV) :
    memRd mv "pipe" (m.index? false (LVec.ofInt 32 ((N : Int) - 1))) W = mv "pipe" ((N : Int) - 1) := by
  rw [sf_index h1 h0 hl (by omega) (by omega), if_pos (by omega)]
  rfl

/-- The states the cycle keeps: the view's shape with its widths, every element of `pipe` `W` bits wide. -/
def SfInv (W : Nat) (σ : SvState × MemV) : Prop :=
  ∃ c d q, σ.1 = view c d q ∧ c.width = 1 ∧ d.width = W ∧ q.width = W ∧ ∀ k, (σ.2 "pipe" k).width = W

theorem shiftM_width {W N : Nat} {mv : MemV} {d : LVec} (hm : ∀ k, (mv "pipe" k).width = W) (hd : d.width = W)
    (k : Int) : (shiftM N mv d "pipe" k).width = W := by
  unfold shiftM
  split
  · split
    · exact hd
    · exact hm _
  · exact hm k

theorem sfF_inv {W N : Nat} {σ : SvState × MemV} {dt : SvState} (hm : ∀ k, (σ.2 "pipe" k).width = W)
    (hd : (appliedIn dt σ.1 "d").width = W) : SfInv W (sfF N σ dt).2 :=
  ⟨_, _, _, rfl, rfl, hd, shiftM_width hm hd _, fun k => shiftM_width hm hd k⟩

set_option maxHeartbeats 4000000 in
/-- **The cycle equations**: from every state of the shape, on every typed data entry, the route's cycle is `sfF`, and
the post state keeps the shape. -/
theorem sf_cycle (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) {E : CoreMemDesign}
    (hE : sf.e W N = .ok E) (σ : SvState × MemV) (dt : SvState) (hσ : SfInv W σ) (hd : E.DataTyped "clk" dt) :
    E.cycleMV "clk" σ dt = .ok (sfF N σ dt) ∧ SfInv W (sfF N σ dt).2 := by
  obtain ⟨E', hE', hP, -⟩ := sf_structure W N hW1 hW2 h1 h2
  rw [hE] at hE'
  cases hE'
  obtain ⟨v, mv⟩ := σ
  obtain ⟨c, d, q, hv, hc, hdw, hq, hmw⟩ := hσ
  dsimp only at hv hmw
  subst hv
  have hE0 : sf.mirror W N = E := Res.ok.inj ((sf.mirror_eq W N hW1 hW2 h1 h2).symm.trans hE)
  have hshape : E.ShapeV (view c d q) := by
    subst hE0; simp [sf.mirror_def, CoreMemDesign.ShapeV, view, hc, hdw, hq]
  have hdi : E.dataInputs "clk" = ["d"] := by
    subst hE0; simp [sf.mirror_def, CoreMemDesign.dataInputs, Elab.toDesign2, Design2.inputNames]
  have hd' : (appliedIn dt (view c d q) "d").width = W :=
    CoreMemDesign.appliedIn_width hd (by simp [hdi])
      (by subst hE0; simp [sf.mirror_def, Elab.toDesign2, Design2.declWidth]) (by simp [view, SvState.lookup]) hdw
  refine ⟨?_, sfF_inv hmw hd'⟩
  rw [CoreMemDesign.cycleMV_applied hP mv hshape dt, CoreMemDesign.appliedEntry, hdi]
  simp only [List.map_cons, List.map_nil]
  unfold sfF
  generalize appliedIn dt (view c d q) "d" = d' at hd' ⊢
  sv_seq_cycle hcyc : E.cycleMV "clk" (view c d q, mv) [("d", d')] using hE0
    [sf.mirror_def, view, hc, hdw, hq, hd', hmw]
  rw [hcyc]
  -- the loop's write equation in closed form, the read at `N - 1`
  simp only [sf_post h1 h2, sf_last h1 h2, view]

/-! ## 3. The claim, over every run -/

/-- **The shift register's claim** about the samples of a run (pre and post of each cycle, each a view and a memory
view): the shift, the low slot writing nothing, the output. -/
def SfClaim (N : Nat) (tr : List ((SvState × MemV) × (SvState × MemV))) : Prop :=
  ∀ (c : Nat) (pc : (SvState × MemV) × (SvState × MemV)), tr[c]? = some pc →
    -- the shift: element 0 loads `d`, element `k` loads what element `k - 1` held before the edge
    (∀ k : Int, 0 ≤ k → k < (N : Int) →
      pc.2.2 "pipe" k = if k = 0 then lk pc.1.1 "d" else pc.1.2 "pipe" (k - 1)) ∧
    -- the low slot writes nothing: the cycle starts from the previous cycle's memory
    (∀ pp, tr[c - 1]? = some pp → 1 ≤ c → pc.1.2 = pp.2.2) ∧
    -- the output is the last element, before and after the edge
    lk pc.1.1 "q" = pc.1.2 "pipe" ((N : Int) - 1) ∧ lk pc.2.1 "q" = pc.2.2 "pipe" ((N : Int) - 1)

/-- The state before cycle `c ≥ 1` of a run is the post sample of cycle `c - 1`. -/
theorem prev_cycle (N : Nat) (σ : SvState × MemV) (ins : List SvState) (c : Nat)
    (pp : (SvState × MemV) × (SvState × MemV)) (hc : 1 ≤ c) (hpp : (runF (sfF N) σ ins)[c - 1]? = some pp) :
    stF (sfF N) σ ins c = pp.2 := by
  rw [runF_getElem?] at hpp
  cases hin : ins[c - 1]? with
  | none => simp [hin] at hpp
  | some d =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpp
      subst hpp
      obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
      exact stF_succ (sfF N) σ ins k d (by simpa using hin)

/-- **The claim from the cycle function**, cycle by cycle. -/
theorem sfClaim_of_runF (N : Nat) (σ : SvState × MemV) (ins : List SvState) : SfClaim N (runF (sfF N) σ ins) := by
  intro c pc hpc
  have hpc' := hpc
  rw [runF_getElem?] at hpc
  cases hin : ins[c]? with
  | none => simp [hin] at hpc
  | some dt =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpc
      subst hpc
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk0 hkN
        simp [sfF, shiftM, lk, view, SvState.lookup, hk0, hkN]
      · intro pp hpp hc
        rw [show (sfF N (stF (sfF N) σ ins c) dt).1.2 = (stF (sfF N) σ ins c).2 from rfl,
          prev_cycle N σ ins c pp hc hpp]
      · simp [sfF, lk, view, SvState.lookup]
      · simp [sfF, lk, view, SvState.lookup]

/-- **Element `k` after cycle `c + k` holds the `d` of cycle `c`** (`k < N`): by induction on `k`, the shift once per
cycle. -/
theorem sf_tap {N : Nat} {tr : List ((SvState × MemV) × (SvState × MemV))} (h : SfClaim N tr) :
    ∀ (k : Nat), k < N → ∀ (c : Nat) (pc pc0 : (SvState × MemV) × (SvState × MemV)), tr[c + k]? = some pc →
      tr[c]? = some pc0 → pc.2.2 "pipe" (k : Int) = lk pc0.1.1 "d"
  | 0, hk, c, pc, pc0, hpc, hpc0 => by
      have e : pc0 = pc := by
        rw [Nat.add_zero, hpc0] at hpc
        exact Option.some.inj hpc
      subst e
      have := (h c pc0 hpc0).1 0 (by omega) (by omega)
      simpa using this
  | k + 1, hk, c, pc, pc0, hpc, hpc0 => by
      cases hprev : tr[c + k]? with
      | none =>
          have h1 := List.getElem?_eq_none_iff.mp hprev
          obtain ⟨h2, -⟩ := List.getElem?_eq_some_iff.mp hpc
          omega
      | some pp =>
          obtain ⟨hshift, hlow, -, -⟩ := h (c + (k + 1)) pc hpc
          have e1 := hshift ((k + 1 : Nat) : Int) (by omega) (by omega)
          rw [if_neg (by omega), hlow pp (by simpa using hprev) (by omega)] at e1
          rw [e1, show (((k + 1 : Nat) : Int) - 1) = (k : Int) by omega]
          exact sf_tap h k (by omega) c pp pc0 hprev hpc0

/-- **THE DELAY**: the post sample of `q` in cycle `c + N - 1` is the `d` applied in cycle `c`. -/
theorem sf_delay {N : Nat} (hN : 1 ≤ N) {tr : List ((SvState × MemV) × (SvState × MemV))} (h : SfClaim N tr)
    {c : Nat} {pc pc0 : (SvState × MemV) × (SvState × MemV)} (hpc : tr[c + (N - 1)]? = some pc)
    (hpc0 : tr[c]? = some pc0) : lk pc.2.1 "q" = lk pc0.1.1 "d" := by
  rw [(h (c + (N - 1)) pc hpc).2.2.2, ← sf_tap h (N - 1) (by omega) c pc pc0 hpc hpc0,
    show (((N - 1 : Nat) : Int)) = (N : Int) - 1 by omega]

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state (memory contents arbitrary), on every typed
stimulus. -/
theorem sf_runs (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqRunsM (sf.e W N) "clk" (SfClaim N) := by
  obtain ⟨E, hE, hP, hO⟩ := sf_structure W N hW1 hW2 h1 h2
  have hE0 : sf.mirror W N = E := Res.ok.inj ((sf.mirror_eq W N hW1 hW2 h1 h2).symm.trans hE)
  refine SeqRunsM.of_cycleFn hE hP hO (by subst hE0; simp [sf.mirror_def, Elab.toDesign2, Design2.declWidth])
    (SfInv W) ?_ (sfF N) (fun σ dt hσ hd => sf_cycle W N hW1 hW2 h1 h2 hE σ dt hσ hd)
    (fun σ ins _ _ => sfClaim_of_runF N σ ins)
  intro st hc hmc
  have hs := hc.shape
  have hms := CoreMemDesign.MemCoherent.shape hP.mems hmc
  obtain ⟨hk, hw⟩ := hs
  generalize E.scalar.view st.scalar = v at hk hw ⊢
  generalize E.memOf st.memory = mv at hms ⊢
  subst hE0
  simp [sf.mirror_def, CoreMemDesign.MemShapeV] at hms
  rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨_, _⟩⟩⟩⟩ <;> simp [sf.mirror_def] at hk hw
  obtain ⟨rfl, rfl, rfl⟩ := hk
  exact ⟨x1, x2, x3, rfl, hw.1, hw.2.1, hw.2.2, fun k => hms k⟩

/-- **THE DELAY, over every run**: in every run of the route, from every coherent state, on every typed stimulus, the
post sample of `q` in cycle `c + N - 1` is the `d` applied in cycle `c`. -/
theorem sf_runs_delay (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqRunsM (sf.e W N) "clk" fun tr => ∀ (c : Nat) (pc pc0 : (SvState × MemV) × (SvState × MemV)),
      tr[c + (N - 1)]? = some pc → tr[c]? = some pc0 → lk pc.2.1 "q" = lk pc0.1.1 "d" :=
  (sf_runs W N hW1 hW2 h1 h2).mono fun _ h _ _ _ hpc hpc0 => sf_delay h1 h hpc hpc0

/-! ## 4. The same register with a plain `always`, a module-level loop variable and the step `i = i + 1`

```systemverilog
module shift_v2001 #(parameter int W = 8, parameter int N = 4)
  (input logic clk, input logic [W-1:0] d, output logic [W-1:0] q);
  logic [W-1:0] pipe [0:N-1];
  integer i;
  always @(posedge clk) begin
    pipe[0] <= d;
    for (i = 1; i < N; i = i + 1) pipe[i] <= pipe[i-1];
  end
  assign q = pipe[N-1];
endmodule
```

The route keeps the plain `always` as an event process (read as its edge process, `CoreMemProc.edge?`) and the loop
with the header as written; the stages read the step `i = i + 1` as they read `i++`. The cycle is the SAME function
`sfF`, so the claim and the delay hold of this design too. (Oracle rows: 60, at `(W, N)` = (8, 4), (2, 5).) -/

set_option maxRecDepth 100000 in
load_design_sv2 sp from "Examples/system-verilog/seq_cycle/shift_v2001.sv.json"

set_option maxHeartbeats 1000000 in
seq_mirror (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) : sp.e W N

-- W = 8, N = 4 (28 rows)
#guard (match sp.e 8 4 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l0, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("d", ⟨#[.lz, .l0, .lx, .l1, .lz, .l0, .lx, .l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1, .l0, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "00000101", "00000101", "00000110", "00000110", "00000110", "00000111", "00001000", "00001000", "00001000", "00001001", "00001001", "1x0z1x0z", "1x0z1x0z", "1x0z1x0z", "1x0z1x0z", "00000011", "00000011", "xxxxxxxx", "xxxxxxxx", "00001001", "00001001"]
    | _ => false
  | _ => false)

-- W = 2, N = 5 (32 rows)
#guard (match sp.e 2 5 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l0, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1]⟩)],
       [("d", ⟨#[.lx, .l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l1]⟩)],
       [("clk", ⟨#[.lz]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.lx, .lx]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("d", ⟨#[.l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xx", "xx", "xx", "xx", "xx", "xx", "xx", "xx", "xx", "01", "01", "10", "10", "10", "11", "00", "00", "00", "01", "01", "10", "10", "1x", "1x", "1x", "1x", "11", "11", "xx", "xx", "01", "01"]
    | _ => false
  | _ => false)

set_option maxHeartbeats 1000000 in
theorem sp_structure (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqDesign (sp.e W N) "clk" := by
  sv_structure

set_option maxHeartbeats 4000000 in
/-- **The cycle equations** of the plain-`always` design: the same cycle function. -/
theorem sp_cycle (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) {E : CoreMemDesign}
    (hE : sp.e W N = .ok E) (σ : SvState × MemV) (dt : SvState) (hσ : SfInv W σ) (hd : E.DataTyped "clk" dt) :
    E.cycleMV "clk" σ dt = .ok (sfF N σ dt) ∧ SfInv W (sfF N σ dt).2 := by
  obtain ⟨E', hE', hP, -⟩ := sp_structure W N hW1 hW2 h1 h2
  rw [hE] at hE'
  cases hE'
  obtain ⟨v, mv⟩ := σ
  obtain ⟨c, d, q, hv, hc, hdw, hq, hmw⟩ := hσ
  dsimp only at hv hmw
  subst hv
  have hE0 : sp.mirror W N = E := Res.ok.inj ((sp.mirror_eq W N hW1 hW2 h1 h2).symm.trans hE)
  have hshape : E.ShapeV (view c d q) := by
    subst hE0; simp [sp.mirror_def, CoreMemDesign.ShapeV, view, hc, hdw, hq]
  have hdi : E.dataInputs "clk" = ["d"] := by
    subst hE0; simp [sp.mirror_def, CoreMemDesign.dataInputs, Elab.toDesign2, Design2.inputNames]
  have hd' : (appliedIn dt (view c d q) "d").width = W :=
    CoreMemDesign.appliedIn_width hd (by simp [hdi])
      (by subst hE0; simp [sp.mirror_def, Elab.toDesign2, Design2.declWidth]) (by simp [view, SvState.lookup]) hdw
  refine ⟨?_, sfF_inv hmw hd'⟩
  rw [CoreMemDesign.cycleMV_applied hP mv hshape dt, CoreMemDesign.appliedEntry, hdi]
  simp only [List.map_cons, List.map_nil]
  unfold sfF
  generalize appliedIn dt (view c d q) "d" = d' at hd' ⊢
  sv_seq_cycle hcyc : E.cycleMV "clk" (view c d q, mv) [("d", d')] using hE0
    [sp.mirror_def, view, hc, hdw, hq, hd', hmw]
  rw [hcyc]
  simp only [sf_post h1 h2, sf_last h1 h2, view]

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM** of the plain-`always` design, over every run. -/
theorem sp_runs (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqRunsM (sp.e W N) "clk" (SfClaim N) := by
  obtain ⟨E, hE, hP, hO⟩ := sp_structure W N hW1 hW2 h1 h2
  have hE0 : sp.mirror W N = E := Res.ok.inj ((sp.mirror_eq W N hW1 hW2 h1 h2).symm.trans hE)
  refine SeqRunsM.of_cycleFn hE hP hO (by subst hE0; simp [sp.mirror_def, Elab.toDesign2, Design2.declWidth])
    (SfInv W) ?_ (sfF N) (fun σ dt hσ hd => sp_cycle W N hW1 hW2 h1 h2 hE σ dt hσ hd)
    (fun σ ins _ _ => sfClaim_of_runF N σ ins)
  intro st hc hmc
  have hs := hc.shape
  have hms := CoreMemDesign.MemCoherent.shape hP.mems hmc
  obtain ⟨hk, hw⟩ := hs
  generalize E.scalar.view st.scalar = v at hk hw ⊢
  generalize E.memOf st.memory = mv at hms ⊢
  subst hE0
  simp [sp.mirror_def, CoreMemDesign.MemShapeV] at hms
  rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨_, _⟩⟩⟩⟩ <;> simp [sp.mirror_def] at hk hw
  obtain ⟨rfl, rfl, rfl⟩ := hk
  exact ⟨x1, x2, x3, rfl, hw.1, hw.2.1, hw.2.2, fun k => hms k⟩

/-- **THE DELAY** of the plain-`always` design, over every run. -/
theorem sp_runs_delay (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqRunsM (sp.e W N) "clk" fun tr => ∀ (c : Nat) (pc pc0 : (SvState × MemV) × (SvState × MemV)),
      tr[c + (N - 1)]? = some pc → tr[c]? = some pc0 → lk pc.2.1 "q" = lk pc0.1.1 "d" :=
  (sp_runs W N hW1 hW2 h1 h2).mono fun _ h _ _ _ hpc hpc0 => sf_delay h1 h hpc hpc0

#print axioms sf_structure
#print axioms sf_ports
#print axioms sf_post
#print axioms sf_cycle
#print axioms sf_tap
#print axioms sf_delay
#print axioms sf_runs
#print axioms sf_runs_delay
#print axioms sp_structure
#print axioms sp_cycle
#print axioms sp_runs
#print axioms sp_runs_delay

end Examples.«system-verilog».seq_cycle.shift_for_proof
