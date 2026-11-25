import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# A register with an asynchronous active-low reset, on the ordinary E route, at every `N ≥ 1`, over every run

The census design `sem2/clk_arst`:

```systemverilog
module clk_arst #(parameter int N = 4) (input logic clk, rst_n, en, input logic [N-1:0] d,
    output logic [N-1:0] q);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= '0;
    else if (en) q <= d;
endmodule
```

The process fires on the clock's rise and on the reset's fall (IEEE 1800-2023 §9.4.2, the edge table with its x/z
rows: 1→0, 1→x, 1→z, x→0, z→0 are falls). Under the clocking discipline the reset is a data input: it changes in the
low slot, so a fall fires the process THERE, before the clock edge, and the pre sample already shows the reset.

1. **Structure** (`arst_structure`, `sv_structure`): the instantiation at every `1 ≤ N < 2^30`, in the clocked profile,
   with the obligations (the reset is an input port, not the clock).
2. **The cycle equations** (`arst_cycle`): one cycle is `arstF`: the pre sample's `q` is one activation of the body
   (`arstStep`) when the reset fell from the previous cycle's value, else the held `q`; the post sample's `q` is one
   activation on the pre sample. Exact on 4-state values (an x reset that "falls" reads `!x`, not true: the `else`
   branch, as the simulator does).
3. **The claim** (`arst_runs`): in every run, from every coherent state (the x start and every power-up included), on
   every typed stimulus keeping the input discipline (the reset's assertion never in a row with a data change, §4.7:
   the race the route resolves as "all inputs first", which the judgment no longer claims): a cycle that sees `rst_n = 0` shows `q = 0` after its edge; a cycle whose `rst_n` falls from
   1 to 0 shows `q = 0` already BEFORE its clock edge (the asynchronous reset); `rst_n = 1, en = 1` loads `d`;
   `rst_n = 1, en = 0` holds; and with `rst_n = 1` the pre sample shows the previous cycle's `q`.

Oracle: Icarus Verilog 12.0 (stable), a testbench outside the repository (457 rows at N = 1, 4, 8: the cycle
equations on 4-state `rst_n`/`en` and x data from the x start, and the claim's clauses; 0 mismatches).
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.arst_proof

load_design_sv2 arst from "Examples/system-verilog/sem2/clk_arst/clk_arst.sv.json"

-- A run on the route at `N = 4` (compiled), slot by slot: load 5; `rst_n` falls (the low slot already clears q);
-- `rst_n` rises (no event), hold; load 9.
#guard (match arst.e 4 with
  | .ok E => match runCoreMemRows E E.initial (cycleRows "clk"
      [[("rst_n", .ofNat 1 1), ("en", .ofNat 1 1), ("d", .ofNat 4 5)],
       [("rst_n", .ofNat 1 0), ("en", .ofNat 1 1), ("d", .ofNat 4 7)],
       [("rst_n", .ofNat 1 1), ("en", .ofNat 1 0), ("d", .ofNat 4 9)],
       [("rst_n", .ofNat 1 1), ("en", .ofNat 1 1), ("d", .ofNat 4 9)]]) with
    | .ok rows => rows.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxx", "0101", "0000", "0000", "0000", "0000", "0000", "1001"]
    | _ => false
  | _ => false)

/-! ## 1. Structure and interface -/

set_option maxHeartbeats 1000000 in
theorem arst_structure (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) : SeqDesign (arst.e N) "clk" := by
  sv_structure

set_option maxHeartbeats 1000000 in
theorem arst_ports (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) :
    SeqPorts (arst.e N) [("clk", 1), ("rst_n", 1), ("en", 1), ("d", N)] [("q", N)] := by
  sv_interface

/-! ## 2. The cycle equations -/

/-- One activation of the edge body: `!rst_n` reads true → 0; else `en` reads true → `d`; else hold (E's `if` reads
`condTrue`). -/
def arstStep (N : Nat) (r e d q : LVec) : LVec :=
  if (evalUnaryOp .lnot r).condTrue = true then LVec.ofBitVec 0#N else if e.condTrue = true then d else q

/-- The reset falls from `r0` to `r` (§9.4.2). -/
def fell (r0 r : LVec) : Bool := isNegedge (r0.bits[0]?.getD .lx) (r.bits[0]?.getD .lx)

/-- The view of the design, in declaration order. -/
def view (c r e d q : LVec) : SvState := [("clk", c), ("rst_n", r), ("en", e), ("d", d), ("q", q)]

/-- A signal of a view. -/
def lk (v : SvState) (n : String) : LVec := (SvState.lookup v n).getD ⟨#[]⟩

/-- **The cycle function**: the applied inputs; the pre sample's `q` (an activation when the reset fell from its
previous value, else held); the post sample's `q` (an activation on the pre sample). -/
def arstF (N : Nat) (v dt : SvState) : SvState × SvState :=
  let r := appliedIn dt v "rst_n"
  let e := appliedIn dt v "en"
  let d := appliedIn dt v "d"
  let p := if fell (lk v "rst_n") r = true then arstStep N r e d (lk v "q") else lk v "q"
  (view ⟨#[.l0]⟩ r e d p, view ⟨#[.l1]⟩ r e d (arstStep N r e d p))

/-- The views the cycle keeps: the shape with its widths. -/
def ArstInv (N : Nat) (v : SvState) : Prop :=
  ∃ c r e d q, v = view c r e d q ∧ c.width = 1 ∧ r.width = 1 ∧ e.width = 1 ∧ d.width = N ∧ q.width = N

theorem arstStep_width {N : Nat} {r e d q : LVec} (hd : d.width = N) (hq : q.width = N) :
    (arstStep N r e d q).width = N := by
  unfold arstStep
  split
  · simp
  · split
    · exact hd
    · exact hq

theorem arstF_inv {N : Nat} {v dt : SvState} (hc : (lk v "q").width = N)
    (hr : (appliedIn dt v "rst_n").width = 1) (he : (appliedIn dt v "en").width = 1)
    (hd : (appliedIn dt v "d").width = N) : ArstInv N (arstF N v dt).2 := by
  refine ⟨_, _, _, _, _, rfl, rfl, hr, he, hd, arstStep_width hd ?_⟩
  split
  · exact arstStep_width hd hc
  · exact hc

set_option maxHeartbeats 4000000 in
/-- **The cycle equations**: from every view of the shape, on every typed data entry, the route's cycle is `arstF`,
and the post view keeps the shape. -/
theorem arst_cycle (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : arst.e N = .ok E)
    (v dt : SvState) (hv : ArstInv N v) (hd : E.DataTyped "clk" dt) :
    E.cycleV "clk" v dt = .ok (arstF N v dt) ∧ ArstInv N (arstF N v dt).2 := by
  obtain ⟨E', hE', hP, -⟩ := arst_structure N h1 h2
  rw [hE] at hE'
  cases hE'
  obtain ⟨c, r, e, d, q, rfl, hc, hr, he, hdw, hq⟩ := hv
  have hE0 := hE
  sv_seq_inst [arst.e, arst.pdesign] at hE0
  -- the applied inputs and their widths
  have hshape : E.ShapeV (view c r e d q) := by
    subst hE0; simp [CoreMemDesign.ShapeV, view, hc, hr, he, hdw, hq]
  have hdi : E.dataInputs "clk" = ["rst_n", "en", "d"] := by
    subst hE0; simp [CoreMemDesign.dataInputs, Elab.toDesign2, Design2.inputNames]
  have hwidth : ∀ n w x, n ∈ E.dataInputs "clk" → E.scalar.toDesign2.declWidth n = some w →
      SvState.lookup (view c r e d q) n = some x → x.width = w →
      (appliedIn dt (view c r e d q) n).width = w :=
    fun n w x hn hw hx hxw => CoreMemDesign.appliedIn_width hd hn hw hx hxw
  have hr' := hwidth "rst_n" 1 r (by simp [hdi]) (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
    (by simp [view, SvState.lookup]) hr
  have he' := hwidth "en" 1 e (by simp [hdi]) (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
    (by simp [view, SvState.lookup]) he
  have hd' := hwidth "d" N d (by simp [hdi]) (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
    (by simp [view, SvState.lookup]) hdw
  refine ⟨?_, arstF_inv (by simp [lk, view, SvState.lookup, hq]) hr' he' hd'⟩
  rw [CoreMemDesign.cycleV_applied hP hshape dt, CoreMemDesign.appliedEntry, hdi]
  simp only [List.map_cons, List.map_nil]
  unfold arstF
  generalize appliedIn dt (view c r e d q) "rst_n" = r' at hr' ⊢
  generalize appliedIn dt (view c r e d q) "en" = e' at he' ⊢
  generalize appliedIn dt (view c r e d q) "d" = d' at hd' ⊢
  sv_seq_cycle hcyc : E.cycleV "clk" (view c r e d q) [("rst_n", r'), ("en", e'), ("d", d')] using hE0
    [view, hc, hr, he, hdw, hq, hr', he', hd']
  rw [hcyc]
  have hsz : r'.bits.size = 1 := hr'
  simp only [view, lk, SvState.lookup, arstStep, fell, String.reduceBEq, Bool.false_eq_true, ↓reduceIte,
    beq_self_eq_true, Option.getD_some]
  simp only [Res.ok.injEq, Prod.mk.injEq, List.cons.injEq, true_and, and_true]
  simp only [Array.getElem?_eq_getElem (show 0 < r'.bits.size by omega), Option.getD_some]
  repeat' split
  all_goals simp_all

/-! ## The cycle on known values: a `BitVec` equation (the knownness bridge) -/

/-- On known values one activation of the body is a `BitVec` function. -/
theorem arstStep_known (N : Nat) (r e : BitVec 1) (d q : BitVec N) :
    arstStep N (LVec.ofBitVec r) (LVec.ofBitVec e) (LVec.ofBitVec d) (LVec.ofBitVec q) =
      LVec.ofBitVec (if r = 0#1 then 0#N else if e = 0#1 then q else d) := by
  unfold arstStep
  rw [seqK_lnot_condTrue, LVec.condTrue_ofBitVec]
  by_cases hr : r = 0#1 <;> by_cases he : e = 0#1 <;> simp [hr, he]

/-- On known bits the reset falls exactly from 1 to 0. -/
theorem fell_known (r0 r : BitVec 1) :
    fell (LVec.ofBitVec r0) (LVec.ofBitVec r) = (r0.getLsbD 0 && !r.getLsbD 0) := by
  unfold fell
  rw [seqK_bit0 r0 (by decide), seqK_bit0 r (by decide), seqK_isNegedge]

/-- **The cycle on known state and inputs is a `BitVec` equation**: the pre sample's `q` is an activation when the
reset fell from 1 to 0, else the held `q`; the post sample's `q` an activation on it. -/
theorem arstF_known (N : Nat) (v dt : SvState) (r0 r e : BitVec 1) (d q : BitVec N)
    (hr0 : lk v "rst_n" = LVec.ofBitVec r0) (hq : lk v "q" = LVec.ofBitVec q)
    (hr : appliedIn dt v "rst_n" = LVec.ofBitVec r) (he : appliedIn dt v "en" = LVec.ofBitVec e)
    (hd : appliedIn dt v "d" = LVec.ofBitVec d) :
    let p : BitVec N :=
      if r0.getLsbD 0 && !r.getLsbD 0 then (if r = 0#1 then 0#N else if e = 0#1 then q else d) else q
    SvState.lookup (arstF N v dt).1 "q" = some (LVec.ofBitVec p) ∧
      SvState.lookup (arstF N v dt).2 "q" = some (LVec.ofBitVec (if r = 0#1 then 0#N else if e = 0#1 then p else d)) := by
  intro p
  simp only [arstF, view, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
    hr0, hq, hr, he, hd, fell_known]
  have hp : (if (r0.getLsbD 0 && !r.getLsbD 0) = true then
      arstStep N (LVec.ofBitVec r) (LVec.ofBitVec e) (LVec.ofBitVec d) (LVec.ofBitVec q) else LVec.ofBitVec q) =
      LVec.ofBitVec p := by
    simp only [p, arstStep_known, LVec.ite_ofBitVec]
  rw [hp, arstStep_known]
  exact ⟨rfl, rfl⟩

/-! ## 3. The claim, over every run -/

/-- **The register's claim** about the samples of a run (pre and post of each cycle). -/
def ArstClaim (N : Nat) (tr : List (SvState × SvState)) : Prop :=
  ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc →
    DecisionKnown ((SvState.lookup pc.1 "rst_n").getD (LVec.xVec 1)) →
    DecisionKnown ((SvState.lookup pc.1 "en").getD (LVec.xVec 1)) →
    -- a cycle that sees `rst_n = 0` shows `q = 0` after its edge
    (SvState.lookup pc.1 "rst_n" = some (LVec.ofNat 1 0) → SvState.lookup pc.2 "q" = some (LVec.ofNat N 0)) ∧
    -- asynchronous: when `rst_n` falls from 1 to 0, the pre sample (before the clock edge) already shows `q = 0`
    (∀ pp, tr[c - 1]? = some pp → 1 ≤ c → SvState.lookup pp.1 "rst_n" = some (LVec.ofNat 1 1) →
      SvState.lookup pc.1 "rst_n" = some (LVec.ofNat 1 0) → SvState.lookup pc.1 "q" = some (LVec.ofNat N 0)) ∧
    -- `rst_n = 1`, `en = 1`: `q` after the edge is the `d` the cycle saw
    (SvState.lookup pc.1 "rst_n" = some (LVec.ofNat 1 1) → SvState.lookup pc.1 "en" = some (LVec.ofNat 1 1) →
      SvState.lookup pc.2 "q" = SvState.lookup pc.1 "d") ∧
    -- `rst_n = 1`, `en = 0`: `q` holds the previous cycle's value
    (∀ pp, tr[c - 1]? = some pp → 1 ≤ c → SvState.lookup pc.1 "rst_n" = some (LVec.ofNat 1 1) →
      SvState.lookup pc.1 "en" = some (LVec.ofNat 1 0) → SvState.lookup pc.2 "q" = SvState.lookup pp.2 "q") ∧
    -- `rst_n = 1`: nothing fell, the pre sample shows the previous cycle's `q`
    (∀ pp, tr[c - 1]? = some pp → 1 ≤ c → SvState.lookup pc.1 "rst_n" = some (LVec.ofNat 1 1) →
      SvState.lookup pc.1 "q" = SvState.lookup pp.2 "q")

theorem lnot_zero : (evalUnaryOp UnaryOp.lnot (LVec.ofBitVec 0#1)).condTrue = true := by
  simp [evalUnaryOp, LVec.lnot]
theorem lnot_one : (evalUnaryOp UnaryOp.lnot (LVec.ofBitVec 1#1)).condTrue = false := by
  simp [evalUnaryOp, LVec.lnot]
theorem en_one : (LVec.ofBitVec 1#1).condTrue = true := by simp
theorem en_zero : (LVec.ofBitVec 0#1).condTrue = false := by simp
theorem bit_zero : (LVec.ofBitVec 0#1).bits[0]?.getD Logic.lx = .l0 := by decide
theorem bit_one : (LVec.ofBitVec 1#1).bits[0]?.getD Logic.lx = .l1 := by decide
theorem fell_into_one (r0 : LVec) : fell r0 (LVec.ofBitVec 1#1) = false := by
  unfold fell; rw [bit_one]; cases r0.bits[0]?.getD Logic.lx <;> rfl
theorem fell_one_zero : fell (LVec.ofBitVec 1#1) (LVec.ofBitVec 0#1) = true := by
  unfold fell; rw [bit_one, bit_zero]; rfl

/-- The cycle before cycle `c ≥ 1` of a run, and the view cycle `c` starts from (its post sample). -/
theorem prev_cycle (N : Nat) (v : SvState) (ins : List SvState) (c : Nat) (pp : SvState × SvState) (hc : 1 ≤ c)
    (hpp : (runF (arstF N) v ins)[c - 1]? = some pp) :
    ∃ u d', pp = arstF N u d' ∧ stF (arstF N) v ins c = (arstF N u d').2 := by
  rw [runF_getElem?] at hpp
  cases hin : ins[c - 1]? with
  | none => simp [hin] at hpp
  | some d =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpp
      subst hpp
      obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
      exact ⟨_, d, rfl, stF_succ (arstF N) v ins k d (by simpa using hin)⟩

/-- **The claim from the cycle function**, cycle by cycle. -/
theorem arstClaim_of_runF (N : Nat) (v : SvState) (ins : List SvState) : ArstClaim N (runF (arstF N) v ins) := by
  intro c pc hpc _ _
  rw [runF_getElem?] at hpc
  cases hin : ins[c]? with
  | none => simp [hin] at hpc
  | some dt =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpc
      subst hpc
      simp only [arstF]
      generalize appliedIn dt (stF (arstF N) v ins c) "rst_n" = R
      generalize appliedIn dt (stF (arstF N) v ins c) "en" = En
      generalize appliedIn dt (stF (arstF N) v ins c) "d" = D
      simp only [view, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
        Option.some.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rintro rfl
        simp [arstStep, lnot_zero]
      · intro pp hpp hc hr0 hR
        subst hR
        obtain ⟨u, d', rfl, hw⟩ := prev_cycle N v ins c pp hc hpp
        simp only [arstF, view, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, Option.some.injEq] at hr0
        rw [hw]
        simp [arstF, view, lk, SvState.lookup, hr0, fell_one_zero, arstStep, lnot_zero]
      · rintro rfl rfl
        simp [arstStep, lnot_one, en_one]
      · intro pp hpp hc hR hEn
        subst hR hEn
        obtain ⟨u, d', rfl, hw⟩ := prev_cycle N v ins c pp hc hpp
        rw [hw]
        simp [arstF, view, lk, SvState.lookup, arstStep, lnot_one, en_zero, fell_into_one]
      · intro pp hpp hc hR
        subst hR
        obtain ⟨u, d', rfl, hw⟩ := prev_cycle N v ins c pp hc hpp
        rw [hw]
        simp [arstF, view, lk, SvState.lookup, fell_into_one]

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state, on every typed stimulus keeping the input
discipline. -/
theorem arst_runs (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) : SeqRuns (arst.e N) "clk" (ArstClaim N) := by
  obtain ⟨E, hE, hP, hO⟩ := arst_structure N h1 h2
  have hE0 := hE
  sv_seq_inst [arst.e, arst.pdesign] at hE0
  refine SeqRuns.of_cycleFn hE hP hO (by subst hE0; rfl) (by subst hE0; simp [Elab.toDesign2, Design2.declWidth]) (ArstInv N) ?_
    (arstF N) (fun v dt hv hd => arst_cycle N h1 h2 hE v dt hv hd)
    (fun v ins _ _ => arstClaim_of_runF N v ins)
  intro v hs
  subst hE0
  obtain ⟨hk, hw⟩ := hs
  rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨⟨n5, x5⟩, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
    simp at hk hw
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk
  exact ⟨x1, x2, x3, x4, x5, rfl, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩

#print axioms arst_structure
#print axioms arst_ports
#print axioms arst_cycle
#print axioms arstF_known
#print axioms arst_runs

end Examples.«system-verilog».seq_cycle.arst_proof
