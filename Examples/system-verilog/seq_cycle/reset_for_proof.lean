import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.XResolve
import LeanModels.Sv.SeqCycleStages

/-!
# A memory cleared by a procedural `for` loop, at every depth `N` and width `W`, over every run

```systemverilog
module reset_for #(parameter int W = 8, parameter int N = 4)
  (input logic clk, input logic rst, input logic we, input logic [4:0] wa, input logic [W-1:0] wd,
   input logic [4:0] ra, output logic [W-1:0] rd);
  logic [W-1:0] mem [0:N-1];
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < N; i++) mem[i] <= '0;
    end else if (we) mem[wa] <= wd;
  end
  assign rd = mem[ra];
endmodule
```

The reset loop is never unrolled: the route runs it as the header's value list (`intRange 0 N`, a function of the
parameter) and the clocked views mirror that; the cycle equations carry it as ONE write equation over the list
(`memWriteL`), whose closed form is `clearM`: every element `0 ≤ k < N` is 0, every other label is unchanged. A `rst`
that does not read 1 (0, x, z) takes the write branch; a `we` that does not read 1 writes nothing; an address with an
x/z bit, or one at or beyond `N`, selects nothing (IEEE 1800-2017 §11.5.1).

1. **Structure** (`rz_structure`, `sv_structure`): the instantiation at every `1 ≤ W < 2^30`, `1 ≤ N ≤ 4000`, in the
   clocked profile with the obligations. The bound on `N` is the route's: a loop runs one unit of the statement fuel
   (4096) per iteration, and beyond it the route itself answers `timeout`.
2. **The cycle equations** (`rz_cycle`): one cycle is `rzF`: under `rst` the post memory is `clearM` (`rz_post`: the
   loop's write equation in closed form), else the write equation under `we`.
3. **The claim over every run** (`rz_runs`), from every coherent state (memory contents arbitrary), on every typed
   stimulus: in every cycle whose `rst` reads 1, `mem' k = 0` for every `0 ≤ k < N`; otherwise the write equation; the
   low slot writing nothing; the read equation; and READ AFTER RESET (`rz_runs_reset`): after a cycle whose `rst` reads
   1, a read of a known address `a < N` in the next cycle's pre sample shows 0, whatever the memory held.

Oracle: Icarus Verilog 12.0 (stable). The `#guard` runs below are the route's runs (`runCoreMemRows` from the x start);
their expected lists are Icarus's samples of the same row stimuli, at `(W, N)` = (8, 4), (1, 2), (4, 5): 75 rows, with
x and z on `rst`, `we`, `clk` (a 0 → x transition is a rise, §9.4.2), on the addresses and on the data. No Xcelium
result is claimed.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.reset_for_proof

set_option maxRecDepth 100000 in
load_design_sv2 rz from "Examples/system-verilog/seq_cycle/reset_for.sv.json"

-- The instantiation at every width and depth, computed once (`rz.mirror`, `rz.mirror_eq`); the stages read it.
set_option maxHeartbeats 1000000 in
seq_mirror (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) : rz.e W N

/-! ## Runs on the route, against Icarus Verilog 12.0 -/

-- W = 8, N = 4 (25 rows)
#guard (match rz.e 8 4 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l0]⟩), ("we", ⟨#[.l1]⟩), ("wa", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩), ("wd", ⟨#[.l1, .l0, .l1, .l0, .l0, .l0, .l0, .l0]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("wa", ⟨#[.l1, .l1, .l0, .l0, .l0]⟩), ("wd", ⟨#[.l1, .l1, .l1, .l0, .l0, .l0, .l0, .l0]⟩), ("ra", ⟨#[.l1, .l1, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l1]⟩), ("we", ⟨#[.l1]⟩), ("wd", ⟨#[.l1, .l0, .l0, .l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)],
       [("ra", ⟨#[.l1, .l1, .l0, .l0, .l0]⟩)],
       [("ra", ⟨#[.l0, .l0, .l1, .l0, .l0]⟩)],
       [("rst", ⟨#[.l0]⟩), ("we", ⟨#[.l1]⟩), ("wa", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩), ("wd", ⟨#[.lz, .l0, .lx, .l1, .lz, .l0, .lx, .l1]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.lx]⟩), ("wd", ⟨#[.l1, .l1, .l0, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.lz]⟩), ("we", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l0]⟩), ("we", ⟨#[.lx]⟩), ("wd", ⟨#[.l0, .l1, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("we", ⟨#[.l1]⟩), ("wa", ⟨#[.l0, .l0, .l0, .l0, .lx]⟩), ("wd", ⟨#[.l0, .l1, .l1, .l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("wa", ⟨#[.l0, .l0, .l1, .l0, .l0]⟩), ("ra", ⟨#[.l1, .l1, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .lz]⟩)],
       [("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "rd") ==
        ["xxxxxxxx", "00000101", "xxxxxxxx", "00000111", "00000111", "00000000", "00000000", "00000000", "xxxxxxxx", "00000000", "1x0z1x0z", "1x0z1x0z", "00000011", "00000011", "00000011", "00000011", "00000000", "00000000", "00000000", "00000000", "00000000", "00000000", "00000000", "xxxxxxxx", "00000000"]
    | _ => false
  | _ => false)

-- W = 1, N = 2 (25 rows)
#guard (match rz.e 1 2 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l0]⟩), ("we", ⟨#[.l1]⟩), ("wa", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩), ("wd", ⟨#[.l1]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("wa", ⟨#[.l1, .l0, .l0, .l0, .l0]⟩), ("wd", ⟨#[.l1]⟩), ("ra", ⟨#[.l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l1]⟩), ("we", ⟨#[.l1]⟩), ("wd", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)],
       [("ra", ⟨#[.l1, .l0, .l0, .l0, .l0]⟩)],
       [("ra", ⟨#[.l0, .l1, .l0, .l0, .l0]⟩)],
       [("rst", ⟨#[.l0]⟩), ("we", ⟨#[.l1]⟩), ("wa", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩), ("wd", ⟨#[.l1]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.lx]⟩), ("wd", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.lz]⟩), ("we", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l0]⟩), ("we", ⟨#[.lx]⟩), ("wd", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("we", ⟨#[.l1]⟩), ("wa", ⟨#[.l0, .l0, .l0, .l0, .lx]⟩), ("wd", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("wa", ⟨#[.l0, .l1, .l0, .l0, .l0]⟩), ("ra", ⟨#[.l1, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .lz]⟩)],
       [("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "rd") ==
        ["x", "1", "x", "1", "1", "0", "0", "0", "x", "0", "1", "1", "1", "1", "1", "1", "0", "0", "0", "0", "0", "0", "0", "x", "0"]
    | _ => false
  | _ => false)

-- W = 4, N = 5 (25 rows)
#guard (match rz.e 4 5 with
  | .ok E => match runCoreMemRows E E.initial
      [[("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l0]⟩), ("we", ⟨#[.l1]⟩), ("wa", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩), ("wd", ⟨#[.l1, .l0, .l1, .l0]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("wa", ⟨#[.l0, .l0, .l1, .l0, .l0]⟩), ("wd", ⟨#[.l1, .l1, .l1, .l0]⟩), ("ra", ⟨#[.l0, .l0, .l1, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l1]⟩), ("we", ⟨#[.l1]⟩), ("wd", ⟨#[.l1, .l0, .l0, .l1]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)],
       [("ra", ⟨#[.l0, .l0, .l1, .l0, .l0]⟩)],
       [("ra", ⟨#[.l1, .l0, .l1, .l0, .l0]⟩)],
       [("rst", ⟨#[.l0]⟩), ("we", ⟨#[.l1]⟩), ("wa", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩), ("wd", ⟨#[.lz, .l0, .lx, .l1]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.lx]⟩), ("wd", ⟨#[.l1, .l1, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.lz]⟩), ("we", ⟨#[.l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.lx]⟩)],
       [("clk", ⟨#[.l0]⟩), ("rst", ⟨#[.l0]⟩), ("we", ⟨#[.lx]⟩), ("wd", ⟨#[.l0, .l1, .l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("we", ⟨#[.l1]⟩), ("wa", ⟨#[.l0, .l0, .l0, .l0, .lx]⟩), ("wd", ⟨#[.l0, .l1, .l1, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("wa", ⟨#[.l1, .l0, .l1, .l0, .l0]⟩), ("ra", ⟨#[.l0, .l0, .l1, .l0, .l0]⟩)],
       [("clk", ⟨#[.l1]⟩)],
       [("clk", ⟨#[.l0]⟩), ("ra", ⟨#[.l0, .l0, .l0, .l0, .lz]⟩)],
       [("ra", ⟨#[.l0, .l0, .l0, .l0, .l0]⟩)]] with
    | .ok outs => outs.map (fun st => SvState.showSignal (CoreMemState.view E st) "rd") ==
        ["xxxx", "0101", "xxxx", "0111", "0111", "0000", "0000", "0000", "xxxx", "0000", "1x0z", "1x0z", "0011", "0011", "0011", "0011", "0000", "0000", "0000", "0000", "0000", "0000", "0000", "xxxx", "0000"]
    | _ => false
  | _ => false)

/-! ## 1. Structure and interface -/

set_option maxHeartbeats 1000000 in
theorem rz_structure (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqDesign (rz.e W N) "clk" := by
  sv_structure

set_option maxHeartbeats 1000000 in
theorem rz_ports (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqPorts (rz.e W N) [("clk", 1), ("rst", 1), ("we", 1), ("wa", 5), ("wd", W), ("ra", 5)] [("rd", W)] := by
  sv_interface

/-! ## 2. The cycle equations -/

/-- **The address decision** of the route (`MemShape.index?` of `[0:N-1]`) at a run-time address: a known address
below `N` selects its label; an address with an x/z bit, or one at or beyond `N`, selects nothing. -/
def rzIdx (N : Nat) (a : LVec) : Option Int :=
  match a.toNat? with
  | some k => if k < N then some (k : Int) else none
  | none => none

/-- The route's index decision on the declared range `[0:N-1]` is `rzIdx`. -/
theorem rz_index {N : Nat} (h : 1 ≤ N) {m : MemShape} (h0 : m.msb = 0) (h1 : m.lsb = (N : Int) - 1) (a : LVec) :
    m.index? false a = rzIdx N a := by
  unfold MemShape.index? rzIdx
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases a.toNat? with
  | none => rfl
  | some k =>
      simp only [Option.map_some]
      by_cases hk : k < N
      · have : m.inRange (k : Int) := by unfold MemShape.inRange; omega
        simp [this, hk]
      · have : ¬ m.inRange (k : Int) := by unfold MemShape.inRange; omega
        simp [this, hk]

/-- The view of the design, in declaration order. -/
def view (c rst we wa wd ra rd : LVec) : SvState :=
  [("clk", c), ("rst", rst), ("we", we), ("wa", wa), ("wd", wd), ("ra", ra), ("rd", rd)]

/-- A signal of a view. -/
def lk (v : SvState) (n : String) : LVec := (SvState.lookup v n).getD ⟨#[]⟩

/-- **The cleared memory**: every element `0 ≤ k < N` of `mem` is 0; every other label and every other memory is
unchanged. -/
def clearM (W N : Nat) (mv : MemV) : MemV := fun n k =>
  if n = "mem" ∧ 0 ≤ k ∧ k < (N : Int) then LVec.ofBitVec 0#W else mv n k

/-- **The cycle function**: the applied inputs; the pre sample reads the memory before the edge; the post memory is the
cleared memory when `rst` reads 1, else the write equation when `we` reads 1; the post sample reads the post memory. -/
def rzF (W N : Nat) (σ : SvState × MemV) (dt : SvState) : (SvState × MemV) × (SvState × MemV) :=
  let rst := appliedIn dt σ.1 "rst"
  let we := appliedIn dt σ.1 "we"
  let wa := appliedIn dt σ.1 "wa"
  let wd := appliedIn dt σ.1 "wd"
  let ra := appliedIn dt σ.1 "ra"
  let m' := if rst.condTrue then clearM W N σ.2 else
    if we.condTrue then memWrite σ.2 "mem" (rzIdx N wa) wd else σ.2
  ((view ⟨#[.l0]⟩ rst we wa wd ra (memRd σ.2 "mem" (rzIdx N ra) W), σ.2),
   (view ⟨#[.l1]⟩ rst we wa wd ra (memRd m' "mem" (rzIdx N ra) W), m'))

/-- **The loop's write equation in closed form**: `for (i = 0; i < N; i++) mem[i] <= '0` (the loop's values
`intRange 0 N`) is the cleared memory. Proved from the list's membership (`mem_intRange`), not by unrolling. -/
theorem rz_post {W N : Nat} (h1 : 1 ≤ N) (h2 : N ≤ 4000) {m : MemShape} (h0 : m.msb = 0)
    (hl : m.lsb = (N : Int) - 1) (mv : MemV) :
    memWriteL mv "mem" (intRange 0 N) (fun i => m.index? false (LVec.ofInt 32 i)) (fun _ => LVec.ofBitVec 0#W) =
      clearM W N mv := by
  have hkey : ∀ i ∈ intRange 0 N, m.index? false (LVec.ofInt 32 i) = some i := by
    intro i hi
    rw [mem_intRange] at hi
    have hr : m.inRange i := by unfold MemShape.inRange; omega
    rw [seqK_index?_ofInt32 m (by omega) (by omega), if_pos hr]
  funext n k
  rw [memWriteL_id hkey]
  unfold clearM
  by_cases h : n = "mem" ∧ k ∈ intRange 0 N
  · have hk := mem_intRange.mp h.2
    rw [if_pos h, if_pos ⟨h.1, by omega, by omega⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1, mem_intRange.mpr ⟨h'.2.1, by omega⟩⟩]

/-- The states the cycle keeps: the view's shape with its widths, every element of `mem` `W` bits wide. -/
def RzInv (W : Nat) (σ : SvState × MemV) : Prop :=
  ∃ c rst we wa wd ra rd, σ.1 = view c rst we wa wd ra rd ∧ c.width = 1 ∧ rst.width = 1 ∧ we.width = 1 ∧
    wa.width = 5 ∧ wd.width = W ∧ ra.width = 5 ∧ rd.width = W ∧ ∀ k, (σ.2 "mem" k).width = W

theorem clearM_width {W N : Nat} {mv : MemV} (hm : ∀ k, (mv "mem" k).width = W) (k : Int) :
    (clearM W N mv "mem" k).width = W := by
  unfold clearM
  split
  · simp
  · exact hm k

theorem rzF_inv {W N : Nat} {σ : SvState × MemV} {dt : SvState} (hm : ∀ k, (σ.2 "mem" k).width = W)
    (hrst : (appliedIn dt σ.1 "rst").width = 1) (hwe : (appliedIn dt σ.1 "we").width = 1)
    (hwa : (appliedIn dt σ.1 "wa").width = 5) (hwd : (appliedIn dt σ.1 "wd").width = W)
    (hra : (appliedIn dt σ.1 "ra").width = 5) : RzInv W (rzF W N σ dt).2 := by
  have hm' : ∀ k, ((if (appliedIn dt σ.1 "rst").condTrue = true then clearM W N σ.2 else
      if (appliedIn dt σ.1 "we").condTrue = true then
        memWrite σ.2 "mem" (rzIdx N (appliedIn dt σ.1 "wa")) (appliedIn dt σ.1 "wd") else σ.2) "mem" k).width = W := by
    intro k
    split
    · exact clearM_width hm k
    · split
      · exact seqE_memWrite_width hm hwd k
      · exact hm k
  exact ⟨_, _, _, _, _, _, _, rfl, rfl, hrst, hwe, hwa, hwd, hra, seqE_memRd_width hm' _, hm'⟩

set_option maxHeartbeats 4000000 in
/-- **The cycle equations**: from every state of the shape, on every typed data entry, the route's cycle is `rzF`, and
the post state keeps the shape. -/
theorem rz_cycle (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) {E : CoreMemDesign}
    (hE : rz.e W N = .ok E) (σ : SvState × MemV) (dt : SvState) (hσ : RzInv W σ) (hd : E.DataTyped "clk" dt) :
    E.cycleMV "clk" σ dt = .ok (rzF W N σ dt) ∧ RzInv W (rzF W N σ dt).2 := by
  obtain ⟨E', hE', hP, -⟩ := rz_structure W N hW1 hW2 h1 h2
  rw [hE] at hE'
  cases hE'
  obtain ⟨v, mv⟩ := σ
  obtain ⟨c, rst, we, wa, wd, ra, rd, hv, hc, hrst, hwe, hwa, hwd, hra, hrd, hmw⟩ := hσ
  dsimp only at hv hmw
  subst hv
  have hE0 : rz.mirror W N = E := Res.ok.inj ((rz.mirror_eq W N hW1 hW2 h1 h2).symm.trans hE)
  have hshape : E.ShapeV (view c rst we wa wd ra rd) := by
    subst hE0; simp [rz.mirror_def, CoreMemDesign.ShapeV, view, hc, hrst, hwe, hwa, hwd, hra, hrd]
  have hdi : E.dataInputs "clk" = ["rst", "we", "wa", "wd", "ra"] := by
    subst hE0; simp [rz.mirror_def, CoreMemDesign.dataInputs, Elab.toDesign2, Design2.inputNames]
  have hwidth : ∀ n w x, n ∈ E.dataInputs "clk" → E.scalar.toDesign2.declWidth n = some w →
      SvState.lookup (view c rst we wa wd ra rd) n = some x → x.width = w →
      (appliedIn dt (view c rst we wa wd ra rd) n).width = w :=
    fun n w x hn hw hx hxw => CoreMemDesign.appliedIn_width hd hn hw hx hxw
  have hrst' := hwidth "rst" 1 rst (by simp [hdi])
    (by subst hE0; simp [rz.mirror_def, Elab.toDesign2, Design2.declWidth]) (by simp [view, SvState.lookup]) hrst
  have hwe' := hwidth "we" 1 we (by simp [hdi])
    (by subst hE0; simp [rz.mirror_def, Elab.toDesign2, Design2.declWidth]) (by simp [view, SvState.lookup]) hwe
  have hwa' := hwidth "wa" 5 wa (by simp [hdi])
    (by subst hE0; simp [rz.mirror_def, Elab.toDesign2, Design2.declWidth]) (by simp [view, SvState.lookup]) hwa
  have hwd' := hwidth "wd" W wd (by simp [hdi])
    (by subst hE0; simp [rz.mirror_def, Elab.toDesign2, Design2.declWidth]) (by simp [view, SvState.lookup]) hwd
  have hra' := hwidth "ra" 5 ra (by simp [hdi])
    (by subst hE0; simp [rz.mirror_def, Elab.toDesign2, Design2.declWidth]) (by simp [view, SvState.lookup]) hra
  refine ⟨?_, rzF_inv hmw hrst' hwe' hwa' hwd' hra'⟩
  rw [CoreMemDesign.cycleMV_applied hP mv hshape dt, CoreMemDesign.appliedEntry, hdi]
  simp only [List.map_cons, List.map_nil]
  unfold rzF
  generalize appliedIn dt (view c rst we wa wd ra rd) "rst" = rst' at hrst' ⊢
  generalize appliedIn dt (view c rst we wa wd ra rd) "we" = we' at hwe' ⊢
  generalize appliedIn dt (view c rst we wa wd ra rd) "wa" = wa' at hwa' ⊢
  generalize appliedIn dt (view c rst we wa wd ra rd) "wd" = wd' at hwd' ⊢
  generalize appliedIn dt (view c rst we wa wd ra rd) "ra" = ra' at hra' ⊢
  sv_seq_cycle hcyc : E.cycleMV "clk" (view c rst we wa wd ra rd, mv)
      [("rst", rst'), ("we", we'), ("wa", wa'), ("wd", wd'), ("ra", ra')] using hE0
    [rz.mirror_def, view, hc, hrst, hwe, hwa, hwd, hra, hrd, hrst', hwe', hwa', hwd', hra', hmw]
  rw [hcyc]
  -- the loop's write equation in closed form, the address decisions
  simp only [rz_post h1 h2]
  simp only [rz_index h1, view]
  -- the post read is the read of the post memory (two decisions, `rst` and `we`)
  by_cases hr : rst'.condTrue = true <;> by_cases hw : we'.condTrue = true <;> simp [hr, hw, memRd_memWrite]

/-! ## 3. The claim, over every run -/

/-- **The claim** about the samples of a run (pre and post of each cycle, each a view and a memory view): the reset,
the write equation, the low slot writing nothing, the read equation before and after the edge. -/
def RzClaim (W N : Nat) (tr : List ((SvState × MemV) × (SvState × MemV))) : Prop :=
  ∀ (c : Nat) (pc : (SvState × MemV) × (SvState × MemV)), tr[c]? = some pc →
    -- known reset decisions expose the reset equation; unknown reset reads remain set-valued
    (DecisionKnown (lk pc.1.1 "rst") →
      ((lk pc.1.1 "rst").condTrue = true → ∀ k : Int, 0 ≤ k → k < (N : Int) →
        pc.2.2 "mem" k = LVec.ofBitVec 0#W)) ∧
    -- known reset and write-enable decisions expose the write equation
    (DecisionKnown (lk pc.1.1 "rst") → DecisionKnown (lk pc.1.1 "we") →
      ((lk pc.1.1 "rst").condTrue = false → pc.2.2 = (if (lk pc.1.1 "we").condTrue then
        memWrite pc.1.2 "mem" (rzIdx N (lk pc.1.1 "wa")) (lk pc.1.1 "wd") else pc.1.2))) ∧
    -- the low slot writes nothing: the cycle starts from the previous cycle's memory
    (∀ pp, tr[c - 1]? = some pp → 1 ≤ c → pc.1.2 = pp.2.2) ∧
    -- the read equation, before and after the edge
    lk pc.1.1 "rd" = memRd pc.1.2 "mem" (rzIdx N (lk pc.1.1 "ra")) W ∧
    lk pc.2.1 "rd" = memRd pc.2.2 "mem" (rzIdx N (lk pc.2.1 "ra")) W

/-- The state before cycle `c ≥ 1` of a run is the post sample of cycle `c - 1`. -/
theorem prev_cycle (W N : Nat) (σ : SvState × MemV) (ins : List SvState) (c : Nat)
    (pp : (SvState × MemV) × (SvState × MemV)) (hc : 1 ≤ c) (hpp : (runF (rzF W N) σ ins)[c - 1]? = some pp) :
    stF (rzF W N) σ ins c = pp.2 := by
  rw [runF_getElem?] at hpp
  cases hin : ins[c - 1]? with
  | none => simp [hin] at hpp
  | some d =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpp
      subst hpp
      obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
      exact stF_succ (rzF W N) σ ins k d (by simpa using hin)

/-- **The claim from the cycle function**, cycle by cycle. -/
theorem rzClaim_of_runF (W N : Nat) (σ : SvState × MemV) (ins : List SvState) :
    RzClaim W N (runF (rzF W N) σ ins) := by
  intro c pc hpc
  have hpc' := hpc
  rw [runF_getElem?] at hpc
  cases hin : ins[c]? with
  | none => simp [hin] at hpc
  | some dt =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpc
      subst hpc
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro _ hr k hk0 hkN
        simp only [rzF, lk, view, SvState.lookup] at hr ⊢
        simp at hr
        simp [hr, clearM, hk0, hkN]
      · intro _ _ hr
        simp only [rzF, lk, view, SvState.lookup] at hr ⊢
        simp at hr
        simp [hr]
      · intro pp hpp hc
        rw [show (rzF W N (stF (rzF W N) σ ins c) dt).1.2 = (stF (rzF W N) σ ins c).2 from rfl,
          prev_cycle W N σ ins c pp hc hpp]
      · simp [rzF, lk, view, SvState.lookup]
      · simp [rzF, lk, view, SvState.lookup]

theorem rzIdx_ofBitVec {N : Nat} (a : BitVec 5) (h : a.toNat < N) :
    rzIdx N (LVec.ofBitVec a) = some (a.toNat : Int) := by
  simp [rzIdx, h]

/-- **READ AFTER RESET**: after a cycle whose `rst` reads 1, a read of a known address `a < N` in the next cycle's pre
sample shows 0. -/
theorem rz_read_after_reset {W N : Nat} {tr : List ((SvState × MemV) × (SvState × MemV))} (h : RzClaim W N tr)
    {c : Nat} {pc pc' : (SvState × MemV) × (SvState × MemV)} (hc : tr[c]? = some pc) (hc' : tr[c + 1]? = some pc')
    (hrstKnown : DecisionKnown (lk pc.1.1 "rst"))
    (hrst : (lk pc.1.1 "rst").condTrue = true) {a : BitVec 5} (hN : a.toNat < N)
    (hra : lk pc'.1.1 "ra" = LVec.ofBitVec a) : lk pc'.1.1 "rd" = LVec.ofBitVec 0#W := by
  obtain ⟨hz, -, -, -, -⟩ := h c pc hc hrstKnown
  obtain ⟨-, -, hlow, hrd, -⟩ := h (c + 1) pc' hc' hrstKnown
  rw [hrd, hra, hlow pc (by simpa using hc) (by omega), rzIdx_ofBitVec a hN]
  exact hz hrst (a.toNat : Int) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state (memory contents arbitrary), on every typed
stimulus. -/
theorem rz_runs (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqRunsM (rz.e W N) "clk" (RzClaim W N) := by
  obtain ⟨E, hE, hP, hO⟩ := rz_structure W N hW1 hW2 h1 h2
  have hE0 : rz.mirror W N = E := Res.ok.inj ((rz.mirror_eq W N hW1 hW2 h1 h2).symm.trans hE)
  refine SeqRunsM.of_cycleFn hE hP hO (by subst hE0; simp [rz.mirror_def, Elab.toDesign2, Design2.declWidth])
    (RzInv W) ?_ (rzF W N) (fun σ dt hσ hd => rz_cycle W N hW1 hW2 h1 h2 hE σ dt hσ hd)
    (fun σ ins _ _ => rzClaim_of_runF W N σ ins)
  intro st hc hmc
  have hs := hc.shape
  have hms := CoreMemDesign.MemCoherent.shape hP.mems hmc
  obtain ⟨hk, hw⟩ := hs
  generalize E.scalar.view st.scalar = v at hk hw ⊢
  generalize E.memOf st.memory = mv at hms ⊢
  subst hE0
  simp [rz.mirror_def, CoreMemDesign.MemShapeV] at hms
  rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨⟨n5, x5⟩, _ | ⟨⟨n6, x6⟩,
    _ | ⟨⟨n7, x7⟩, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp [rz.mirror_def] at hk hw
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hk
  exact ⟨x1, x2, x3, x4, x5, x6, x7, rfl, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
    hw.2.2.2.2.2.2, fun k => hms k⟩

/-- **READ AFTER RESET, over every run**: in every run of the route, from every coherent state, on every typed
stimulus, after a cycle whose `rst` reads 1 a read of a known address `a < N` in the next cycle's pre sample shows 0. -/
theorem rz_runs_reset (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqRunsM (rz.e W N) "clk" fun tr => ∀ (c : Nat) (pc pc' : (SvState × MemV) × (SvState × MemV)) (a : BitVec 5),
      tr[c]? = some pc → tr[c + 1]? = some pc' → DecisionKnown (lk pc.1.1 "rst") →
      (lk pc.1.1 "rst").condTrue = true → a.toNat < N →
      lk pc'.1.1 "ra" = LVec.ofBitVec a → lk pc'.1.1 "rd" = LVec.ofBitVec 0#W :=
  (rz_runs W N hW1 hW2 h1 h2).mono fun _ h _ _ _ _ hc hc' hrstKnown hrst hN hra =>
    rz_read_after_reset h hc hc' hrstKnown hrst hN hra

#print axioms rz_structure
#print axioms rz_ports
#print axioms rz_post
#print axioms rz_cycle
#print axioms rz_read_after_reset
#print axioms rz_runs
#print axioms rz_runs_reset

end Examples.«system-verilog».seq_cycle.reset_for_proof
