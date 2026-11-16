import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# A memory with an asynchronous reset, at every width and depth, over every run, from per-signal equations

The census design `seq_mem/async_mem_fifo` (one memory, written at one cell under an active-low asynchronous reset):

```systemverilog
module async_mem_fifo #(parameter integer W = 8, N = 4) (input wire clk, rstn, input wire [W-1:0] d,
    output wire [W-1:0] q);
  logic [W-1:0] mem [N];
  always_ff @(posedge clk or negedge rstn)
    if (!rstn) mem[0] <= '0; else mem[0] <= d;
  assign q = mem[0];
endmodule
```

The memory is an indexed family: its contents are a function of the label, its next contents one write equation. The
process fires on the clock's rise and on the reset's fall (§9.4.2); under the clocking discipline the reset is a data
input, so a fall fires the process in the LOW slot and the write lands before the clock edge.

This example uses the per-signal form (`CoreMemDesign.CycleEqsM`, `SeqRunsM.of_cycleEqs`): the prover states only the
equations the claim reads (`AmStep`), never a cycle function; `sv_seq_cycle` computes the cycle and each equation is
closed on the computed views.

1. **Structure** (`am_structure`, `sv_structure`): at every `2 ≤ W, N < 2^30`.
2. **The per-signal equations** (`am_eqs`): cell 0 after the edge is `0` under reset, else `d`; `q` reads cell 0 before
   and after the edge; cell 0 before the edge is the reset's write when the reset fell, else the held contents; every
   other cell never changes.
3. **The claim over every run** (`am_runs`), from every coherent state (memory contents arbitrary), on every typed
   stimulus: `rstn = 0` gives `q = 0` after the edge; a fall `1 → 0` gives `q = 0` already BEFORE the edge; `rstn = 1`
   gives `q = d` after the edge; and every cell `k ≠ 0` keeps its contents in every cycle of every run.

Oracle: Icarus Verilog 12.0 (stable), a testbench outside the repository (1069 rows at (W, N) = (2, 2), (4, 4), (8, 3):
the per-signal equations on 4-state `rstn`, x data and the x start, the cells `k ≠ 0` read hierarchically, and the
claim's clauses; 0 mismatches; a testbench model that takes an x/z `rstn` for a reset is caught, 268 mismatches).
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.amem_proof

set_option maxRecDepth 100000 in
load_design_sv2 am from "Examples/system-verilog/seq_mem/async_mem_fifo.sv.json"

-- The instantiation at every width and depth, computed once.
set_option maxHeartbeats 1000000 in
seq_mirror (W : Nat) (hW1 : 2 ≤ W) (hW2 : W < 2 ^ 30) (N : Nat) (hN1 : 2 ≤ N) (hN2 : N < 2 ^ 30) : am.e W N

/-! ## 1. Structure -/

set_option maxHeartbeats 1000000 in
theorem am_structure (W : Nat) (hW1 : 2 ≤ W) (hW2 : W < 2 ^ 30) (N : Nat) (hN1 : 2 ≤ N) (hN2 : N < 2 ^ 30) :
    SeqDesign (am.e W N) "clk" := by
  sv_structure

/-! ## 2. The per-signal equations -/

/-- The view of the design, in declaration order. -/
def view (c r d q : LVec) : SvState := [("clk", c), ("rstn", r), ("d", d), ("q", q)]

/-- A signal of a view. -/
def lk (v : SvState) (n : String) : LVec := (SvState.lookup v n).getD ⟨#[]⟩

/-- The reset falls from `r0` to `r` (§9.4.2). -/
def fell (r0 r : LVec) : Bool := isNegedge (r0.bits[0]?.getD .lx) (r.bits[0]?.getD .lx)

/-- One activation of the body on cell 0: `!rstn` reads true → 0, else `d`. -/
def body (W : Nat) (r d : LVec) : LVec :=
  if (evalUnaryOp .lnot r).condTrue then LVec.ofBitVec 0#W else d

/-- **The equations the claim reads**, per signal, about the state before a cycle, its data and its samples. -/
def AmStep (W : Nat) (σ : SvState × MemV) (dt : SvState) (pp : (SvState × MemV) × (SvState × MemV)) : Prop :=
  let r := appliedIn dt σ.1 "rstn"
  let d := appliedIn dt σ.1 "d"
  lk pp.1.1 "rstn" = r ∧ lk pp.1.1 "d" = d ∧ lk pp.2.1 "rstn" = r ∧ lk pp.2.1 "d" = d ∧
  -- cell 0 after the edge, and `q` reading it
  pp.2.2 "mem" 0 = body W r d ∧ lk pp.2.1 "q" = pp.2.2 "mem" 0 ∧
  -- cell 0 before the edge: the reset's write when it fell (the low slot), else held; `q` reading it
  pp.1.2 "mem" 0 = (if fell (lk σ.1 "rstn") r then body W r d else σ.2 "mem" 0) ∧ lk pp.1.1 "q" = pp.1.2 "mem" 0 ∧
  -- every other cell never changes
  ∀ k, k ≠ 0 → pp.1.2 "mem" k = σ.2 "mem" k ∧ pp.2.2 "mem" k = σ.2 "mem" k

/-- The states the cycle keeps: the view's shape with its widths, every element `W` bits wide. -/
def AmInv (W : Nat) (σ : SvState × MemV) : Prop :=
  ∃ c r d q, σ.1 = view c r d q ∧ c.width = 1 ∧ r.width = 1 ∧ d.width = W ∧ q.width = W ∧
    ∀ k, (σ.2 "mem" k).width = W

/-- The route's index decision for the constant index 0 on `[0:N-1]` (`N ≥ 2`): label 0. -/
theorem am_index0 {N : Nat} (h : 2 ≤ N) {m : MemShape} (h0 : m.msb = 0) (h1 : m.lsb = (N : Int) - 1) :
    m.index? false (LVec.ofInt 32 0) = some 0 := by
  have hz : (LVec.ofInt 32 0).toNat? = some 0 := by rw [LVec.ofInt, LVec.toNat?_ofNat]; decide
  have hin : m.inRange 0 := by unfold MemShape.inRange; right; omega
  simp [MemShape.index?, hz, hin]

theorem body_width {W : Nat} {r d : LVec} (hd : d.width = W) : (body W r d).width = W := by
  unfold body; split
  · simp
  · exact hd

set_option maxHeartbeats 4000000 in
/-- **The per-signal equations**, over every state of the shape and every typed data entry: the route's cycle exists,
keeps the shape, and satisfies `AmStep`. -/
theorem am_eqs (W : Nat) (hW1 : 2 ≤ W) (hW2 : W < 2 ^ 30) (N : Nat) (hN1 : 2 ≤ N) (hN2 : N < 2 ^ 30)
    {E : CoreMemDesign} (hE : am.e W N = .ok E) : E.CycleEqsM "clk" (AmInv W) (AmStep W) := by
  obtain ⟨E', hE', hP, -⟩ := am_structure W hW1 hW2 N hN1 hN2
  rw [hE] at hE'
  cases hE'
  rintro ⟨v, mv⟩ dt ⟨c, r, d, q, hv, hc, hr, hd, hq, hmw⟩ hdt
  dsimp only at hv hmw
  subst hv
  have hE0 := hE
  sv_seq_use [am.mirror_eq W hW1 hW2 N hN1 hN2, am.mirror_def] at hE0
  have hshape : E.ShapeV (view c r d q) := by
    subst hE0; simp [CoreMemDesign.ShapeV, view, hc, hr, hd, hq]
  have hdi : E.dataInputs "clk" = ["rstn", "d"] := by
    subst hE0; simp [CoreMemDesign.dataInputs, Elab.toDesign2, Design2.inputNames]
  have hwidth : ∀ n w x, n ∈ E.dataInputs "clk" → E.scalar.toDesign2.declWidth n = some w →
      SvState.lookup (view c r d q) n = some x → x.width = w → (appliedIn dt (view c r d q) n).width = w :=
    fun n w x hn hw hx hxw => CoreMemDesign.appliedIn_width hdt hn hw hx hxw
  have hr' := hwidth "rstn" 1 r (by simp [hdi]) (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
    (by simp [view, SvState.lookup]) hr
  have hd' := hwidth "d" W d (by simp [hdi]) (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
    (by simp [view, SvState.lookup]) hd
  rw [CoreMemDesign.cycleMV_applied hP mv hshape dt, CoreMemDesign.appliedEntry, hdi]
  simp only [List.map_cons, List.map_nil, AmStep, AmInv]
  generalize appliedIn dt (view c r d q) "rstn" = r' at hr' ⊢
  generalize appliedIn dt (view c r d q) "d" = d' at hd' ⊢
  sv_seq_cycle hcyc : E.cycleMV "clk" (view c r d q, mv) [("rstn", r'), ("d", d')] using hE0
    [view, hc, hr, hd, hq, hr', hd', hmw]
  rw [hcyc]
  simp only [am_index0 hN1, view, lk, fell, body, SvState.lookup, Res.ok.injEq, exists_eq_left',
    String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Option.getD_some]
  -- the two decisions of the cycle: `!rstn`, and whether the reset fell in the low slot
  have hsz : r'.bits.size = 1 := hr'
  simp only [Array.getElem?_eq_getElem (show 0 < r'.bits.size by omega), Option.getD_some]
  by_cases hA : (evalUnaryOp UnaryOp.lnot r').condTrue = true <;>
    simp [hA, and_assoc, memWrite, memRd, hd', hr', hmw, seqE_width_ite, seqE_width_lit,
      eq_comm (a := (0 : Int))] <;>
    (try split) <;> simp_all [memWrite, seqE_width_ite, seqE_width_lit, eq_comm (a := (0 : Int))]

/-! ## 3. The claim, over every run -/

/-- **The memory's claim** about the samples of a run: the asynchronous reset clears cell 0 (after the edge; already
before it when the reset fell), `rstn = 1` loads `d` into cell 0, and every other cell keeps its contents. -/
def AmClaim (W : Nat) (tr : List ((SvState × MemV) × (SvState × MemV))) : Prop :=
  ∀ (c : Nat) (pc : (SvState × MemV) × (SvState × MemV)), tr[c]? = some pc →
    -- a cycle that sees `rstn = 0` shows `q = 0` after its edge
    (lk pc.1.1 "rstn" = LVec.ofBitVec 0#1 → lk pc.2.1 "q" = LVec.ofBitVec 0#W) ∧
    -- asynchronous: when `rstn` falls from 1 to 0, the pre sample (before the clock edge) already shows `q = 0`
    (∀ pp, tr[c - 1]? = some pp → 1 ≤ c → lk pp.1.1 "rstn" = LVec.ofBitVec 1#1 →
      lk pc.1.1 "rstn" = LVec.ofBitVec 0#1 → lk pc.1.1 "q" = LVec.ofBitVec 0#W) ∧
    -- `rstn = 1`: `q` after the edge is the `d` the cycle saw
    (lk pc.1.1 "rstn" = LVec.ofBitVec 1#1 → lk pc.2.1 "q" = lk pc.1.1 "d") ∧
    -- every other cell keeps its contents: through the cycle, and from the previous cycle
    (∀ k, k ≠ 0 → pc.2.2 "mem" k = pc.1.2 "mem" k) ∧
    (∀ pp, tr[c - 1]? = some pp → 1 ≤ c → ∀ k, k ≠ 0 → pc.1.2 "mem" k = pp.2.2 "mem" k)

theorem lnot_zero : (evalUnaryOp UnaryOp.lnot (LVec.ofBitVec 0#1)).condTrue = true := by
  simp [evalUnaryOp, LVec.lnot]
theorem lnot_one : (evalUnaryOp UnaryOp.lnot (LVec.ofBitVec 1#1)).condTrue = false := by
  simp [evalUnaryOp, LVec.lnot]
theorem fell_one_zero : fell (LVec.ofBitVec 1#1) (LVec.ofBitVec 0#1) = true := by decide

/-- **The claim from the per-signal equations**, cycle by cycle (`RunSat.get`). -/
theorem amClaim_of_runSat (W : Nat) (σ : SvState × MemV) (ins : List SvState)
    (tr : List ((SvState × MemV) × (SvState × MemV))) (h : RunSat (AmStep W) σ ins tr) : AmClaim W tr := by
  intro c pc hpc
  obtain ⟨σc, dt, -, hs, -, hprev⟩ := RunSat.get h hpc
  obtain ⟨hr1, hd1, hr2, hd2, hm0, hq2, hm0', hq1, hk⟩ := hs
  refine ⟨?_, ?_, ?_, fun k hk0 => by rw [(hk k hk0).2, (hk k hk0).1], ?_⟩
  · intro h0
    rw [hq2, hm0, ← hr1, h0]
    simp [body, lnot_zero]
  · intro pp hpp hc h1 h0
    have hσ := hprev pp hpp hc
    obtain ⟨σp, dp, -, hsp, -, -⟩ := RunSat.get h hpp
    obtain ⟨hpr1, -, hpr2, -⟩ := hsp
    rw [hq1, hm0', ← hr1, h0, hσ, hpr2, ← hpr1, h1, fell_one_zero]
    simp [body, lnot_zero]
  · intro h1
    rw [hq2, hm0, ← hr1, h1, hd1]
    simp [body, lnot_one]
  · intro pp hpp hc k hk0
    rw [(hk k hk0).1, hprev pp hpp hc]

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state (memory contents arbitrary), on every typed
stimulus. -/
theorem am_runs (W : Nat) (hW1 : 2 ≤ W) (hW2 : W < 2 ^ 30) (N : Nat) (hN1 : 2 ≤ N) (hN2 : N < 2 ^ 30) :
    SeqRunsM (am.e W N) "clk" (AmClaim W) := by
  obtain ⟨E, hE, hP, hO⟩ := am_structure W hW1 hW2 N hN1 hN2
  have hE0 := hE
  sv_seq_use [am.mirror_eq W hW1 hW2 N hN1 hN2, am.mirror_def] at hE0
  refine SeqRunsM.of_cycleEqs hE hP hO (by subst hE0; simp [Elab.toDesign2, Design2.declWidth]) (AmInv W) ?_
    (AmStep W) (am_eqs W hW1 hW2 N hN1 hN2 hE) (fun σ ins tr _ _ h => amClaim_of_runSat W σ ins tr h)
  intro st hc hmc
  have hs := hc.shape
  have hms := CoreMemDesign.MemCoherent.shape hP.mems hmc
  obtain ⟨hk, hw⟩ := hs
  generalize E.scalar.view st.scalar = v at hk hw ⊢
  generalize E.memOf st.memory = mv at hms ⊢
  subst hE0
  simp [CoreMemDesign.MemShapeV] at hms
  rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hk hw
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
  exact ⟨x1, x2, x3, x4, rfl, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, hms⟩

#print axioms am_structure
#print axioms am_eqs
#print axioms amClaim_of_runSat
#print axioms am_runs

end Examples.«system-verilog».seq_cycle.amem_proof
