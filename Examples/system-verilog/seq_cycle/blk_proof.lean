import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# A counter through a blocking temporary in `always_ff`, on the ordinary E route, over every run

The census design `seq_neg/blocking_self` (a negative fixture of the retired FF-only `run2` profile, which admitted
NBA-only bodies; on the ordinary E route the design is legal and exact):

```systemverilog
module blocking_self(input logic clk, output logic [3:0] q);
  logic [3:0] x;
  always_ff @(posedge clk) begin
    x = x + 4'd1;
    q <= x;
  end
endmodule
```

A blocking assignment completes before the next statement runs (IEEE 1800-2023 §10.4.1), so the nonblocking `q <= x`
samples the incremented `x`. With one edge process there is no order to choose (the obligation `oblEdgeOrder`).

1. **Structure, interface** (`sv_structure`, `sv_interface`).
2. **The cycle equations** (`blk_cycle`): the post sample's `x` and `q` are both `x + 1` (4-state `+`: an unknown `x`
   stays unknown); the pre sample holds them.
3. **The claim** (`blk_runs`): in every run, from every coherent state (the x start included): after each cycle `q`
   equals `x` (the blocking write is visible to the nonblocking one), `x` is the previous `x` plus one, and a known
   `x = k` before a cycle is `k + 1` after it.

Oracle: Icarus Verilog 12.0 (stable), a testbench outside the repository (200 rows from the x start and from a
forced known value; 0 mismatches).
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.blk_proof

load_design_sv2 blk from "Examples/system-verilog/seq_neg/blocking_self.sv.json"

/-! ## 1. Structure and interface -/

set_option maxHeartbeats 1000000 in
theorem blk_structure : SeqDesign blk.e "clk" := by
  sv_structure

set_option maxHeartbeats 1000000 in
theorem blk_ports : SeqPorts blk.e [("clk", 1)] [("q", 4)] := by
  sv_interface

/-! ## 2. The cycle equations -/

/-- The literal `4'd1`, bits least significant first. -/
def one4 : LVec := ⟨#[.l1, .l0, .l0, .l0]⟩

/-- The view of the design, in declaration order. -/
def view (c q x : LVec) : SvState := [("clk", c), ("q", q), ("x", x)]

/-- A signal of a view. -/
def lk (v : SvState) (n : String) : LVec := (SvState.lookup v n).getD ⟨#[]⟩

/-- **The cycle function**: the pre sample holds the registers; after the edge `x` is `x + 1` and `q` samples it. -/
def blkF (v _dt : SvState) : SvState × SvState :=
  (view ⟨#[.l0]⟩ (lk v "q") (lk v "x"), view ⟨#[.l1]⟩ ((lk v "x").add one4) ((lk v "x").add one4))

/-- The views the cycle keeps: the shape with its widths. -/
def BlkInv (v : SvState) : Prop := ∃ c q x, v = view c q x ∧ c.width = 1 ∧ q.width = 4 ∧ x.width = 4

theorem add_one4_width {x : LVec} (hx : x.width = 4) : (x.add one4).width = 4 := by
  rw [seqE_width_add, hx]; rfl

set_option maxHeartbeats 4000000 in
/-- **The cycle equations**: from every view of the shape, on every data entry, the route's cycle is `blkF`. -/
theorem blk_cycle {E : CoreMemDesign} (hE : blk.e = .ok E) (v dt : SvState) (hv : BlkInv v)
    (_hd : E.DataTyped "clk" dt) : E.cycleV "clk" v dt = .ok (blkF v dt) ∧ BlkInv (blkF v dt).2 := by
  obtain ⟨E', hE', hP, -⟩ := blk_structure
  rw [hE] at hE'
  cases hE'
  obtain ⟨c, q, x, rfl, hc, hq, hx⟩ := hv
  have hE0 := hE
  sv_seq_inst [blk.e, blk.pdesign] at hE0
  have hshape : E.ShapeV (view c q x) := by
    subst hE0; simp [CoreMemDesign.ShapeV, view, hc, hq, hx]
  have hdi : E.dataInputs "clk" = [] := by
    subst hE0; simp [CoreMemDesign.dataInputs, Elab.toDesign2, Design2.inputNames]
  refine ⟨?_, ⟨_, _, _, rfl, rfl, add_one4_width (by simp [lk, view, SvState.lookup, hx]),
    add_one4_width (by simp [lk, view, SvState.lookup, hx])⟩⟩
  rw [CoreMemDesign.cycleV_applied hP hshape dt, CoreMemDesign.appliedEntry, hdi]
  simp only [List.map_nil, blkF, view, lk, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte,
    beq_self_eq_true, Option.getD_some, one4]
  -- the cycle equations, computed by the clocked `sv_equations` and checked against the statement
  sv_equations

/-! ## 3. The claim, over every run -/

/-- **The counter's claim** about the samples of a run. -/
def BlkClaim (tr : List (SvState × SvState)) : Prop :=
  ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc →
    -- the blocking write is visible to the nonblocking one: after the edge `q` is `x`
    SvState.lookup pc.2 "q" = SvState.lookup pc.2 "x" ∧
    -- `x` counts: after the edge it is the value before the edge plus one (4-state `+`)
    (∀ x, SvState.lookup pc.1 "x" = some x → SvState.lookup pc.2 "x" = some (x.add one4)) ∧
    -- on a known value: `k` before the edge is `k + 1` after it
    (∀ k : BitVec 4, SvState.lookup pc.1 "x" = some (LVec.ofBitVec k) →
      SvState.lookup pc.2 "x" = some (LVec.ofBitVec (k + 1#4)))

theorem one4_known : one4 = LVec.ofBitVec 1#4 := by decide

theorem blkClaim_of_runF (v : SvState) (ins : List SvState) : BlkClaim (runF blkF v ins) := by
  intro c pc hpc
  rw [runF_getElem?] at hpc
  cases hin : ins[c]? with
  | none => simp [hin] at hpc
  | some dt =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpc
      subst hpc
      refine ⟨rfl, fun x hx => ?_, fun k hk => ?_⟩
      · simp only [blkF, view, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, Option.some.injEq] at hx ⊢
        rw [hx]
      · simp only [blkF, view, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, Option.some.injEq] at hk ⊢
        rw [hk, one4_known, LVec.add_ofBitVec]

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state, on every typed stimulus. -/
theorem blk_runs : SeqRuns blk.e "clk" BlkClaim := by
  obtain ⟨E, hE, hP, -⟩ := blk_structure
  have hE0 := hE
  sv_seq_inst [blk.e, blk.pdesign] at hE0
  refine SeqRuns.of_cycleFn hE hP (by subst hE0; rfl) (by subst hE0; simp [Elab.toDesign2, Design2.declWidth]) BlkInv ?_
    blkF (fun v dt hv hd => blk_cycle hE v dt hv hd) (fun v ins _ _ => blkClaim_of_runF v ins)
  intro v hsh
  subst hE0
  obtain ⟨hk, hw⟩ := hsh
  rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hk hw
  obtain ⟨rfl, rfl, rfl⟩ := hk
  exact ⟨x1, x2, x3, rfl, hw.1, hw.2.1, hw.2.2⟩

#print axioms blk_structure
#print axioms blk_ports
#print axioms blk_cycle
#print axioms blk_runs

end Examples.«system-verilog».seq_cycle.blk_proof
