import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# Plain `case` with x/z items in an edge body, on the ordinary E route, over every run

The census design `sem2/case_always_ff_step11`:

```systemverilog
always_ff @(posedge clk) begin
  case (sel)
    2'b00: q <= d;   2'b01: q <= 4'hA;   2'b1x: q <= 4'hB;   2'bz1: q <= 4'hC;   default: q <= 4'hF;
  endcase
  case (sel)
    2'b00: q_default <= d;   default: q_default <= 4'hD;
  endcase
end
```

A plain `case` compares with case equality, `===` (IEEE 1800-2023 §12.5): the item `2'b1x` matches only a selector
whose bits are exactly 1 and x, `2'bz1` only z and 1; the first matching item wins, else the default.

1. **Structure, interface** (`sv_structure`, `sv_interface`).
2. **The cycle equations** (`case_cycle`): the post sample's `q` is `caseQ sel d`, its `q_default` is `caseD sel d`,
   exactly on 4-state values; the pre sample holds the registers.
3. **The claim** (`case_runs`): in every run, from every coherent state, on every typed stimulus: after each cycle `q`
   and `q_default` are the case functions of the `sel` and `d` the cycle saw (every 4-state `sel`); a KNOWN `sel`
   never matches the x/z items (`q` is `d`, `4'hA` or `4'hF`); before the edge the outputs show the previous cycle's.

Oracle: Icarus Verilog 12.0 (stable), a testbench outside the repository (256 rows: all 16 four-state selectors,
known and x/z data, the x start; 0 mismatches).
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.case_proof

load_design_sv2 cs from "Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_step11.sv.json"

-- A run on the route (compiled): sel = 00 (q = d = 5), 01 (A), 1x (B), 11 (F).
#guard (match cs.e with
  | .ok E => match runCoreMemRows E E.initial (cycleRows "clk"
      [[("sel", .ofNat 2 0), ("d", .ofNat 4 5)], [("sel", .ofNat 2 1), ("d", .ofNat 4 5)],
       [("sel", ⟨#[.lx, .l1]⟩), ("d", .ofNat 4 5)], [("sel", .ofNat 2 3), ("d", .ofNat 4 5)]]) with
    | .ok rows => (cyclePairs rows).map (fun pp => SvState.showSignal (CoreMemState.view E pp.2) "q") ==
        ["0101", "1010", "1011", "1111"]
    | _ => false
  | _ => false)

/-! ## 1. Structure and interface -/

set_option maxHeartbeats 1000000 in
theorem case_structure : SeqDesign cs.e "clk" := by
  sv_structure

set_option maxHeartbeats 1000000 in
theorem case_ports : SeqPorts cs.e [("clk", 1), ("sel", 2), ("d", 4)] [("q", 4), ("q_default", 4)] := by
  sv_interface

/-! ## 2. The cycle equations -/

/-- The items, bits least significant first: `2'b00`, `2'b01`, `2'b1x`, `2'bz1`. -/
def i00 : LVec := ⟨#[.l0, .l0]⟩
def i01 : LVec := ⟨#[.l1, .l0]⟩
def i1x : LVec := ⟨#[.lx, .l1]⟩
def iz1 : LVec := ⟨#[.l1, .lz]⟩

/-- The constants `4'hA`, `4'hB`, `4'hC`, `4'hF`, `4'hD`, bits least significant first. -/
def hA : LVec := ⟨#[.l0, .l1, .l0, .l1]⟩
def hB : LVec := ⟨#[.l1, .l1, .l0, .l1]⟩
def hC : LVec := ⟨#[.l0, .l0, .l1, .l1]⟩
def hF : LVec := ⟨#[.l1, .l1, .l1, .l1]⟩
def hD : LVec := ⟨#[.l1, .l0, .l1, .l1]⟩

/-- **The first case** (§12.5: case equality `===` on 4-state vectors, which is `LVec`'s `==`; the first matching item,
else the default). -/
def caseQ (s d : LVec) : LVec :=
  if s == i00 then d else if s == i01 then hA else if s == i1x then hB else if s == iz1 then hC else hF

/-- **The second case**. -/
def caseD (s d : LVec) : LVec := if s == i00 then d else hD

/-- The view of the design, in declaration order. -/
def view (c s d q qd : LVec) : SvState := [("clk", c), ("sel", s), ("d", d), ("q", q), ("q_default", qd)]

/-- A signal of a view. -/
def lk (v : SvState) (n : String) : LVec := (SvState.lookup v n).getD ⟨#[]⟩

/-- **The cycle function**: the applied inputs; the pre sample holds the registers; the post sample's registers are
the two case functions. -/
def caseF (v dt : SvState) : SvState × SvState :=
  let s := appliedIn dt v "sel"
  let d := appliedIn dt v "d"
  (view ⟨#[.l0]⟩ s d (lk v "q") (lk v "q_default"), view ⟨#[.l1]⟩ s d (caseQ s d) (caseD s d))

/-- The views the cycle keeps: the shape with its widths. -/
def CaseInv (v : SvState) : Prop :=
  ∃ c s d q qd, v = view c s d q qd ∧ c.width = 1 ∧ s.width = 2 ∧ d.width = 4 ∧ q.width = 4 ∧ qd.width = 4

theorem caseQ_width {s d : LVec} (hd : d.width = 4) : (caseQ s d).width = 4 := by
  unfold caseQ
  split
  · exact hd
  · repeat' split
    all_goals rfl

theorem caseD_width {s d : LVec} (hd : d.width = 4) : (caseD s d).width = 4 := by
  unfold caseD; split
  · exact hd
  · rfl

set_option maxHeartbeats 4000000 in
/-- **The cycle equations**: from every view of the shape, on every typed data entry, the route's cycle is `caseF`,
and the post view keeps the shape. -/
theorem case_cycle {E : CoreMemDesign} (hE : cs.e = .ok E) (v dt : SvState) (hv : CaseInv v)
    (hd : E.DataTyped "clk" dt) : E.cycleV "clk" v dt = .ok (caseF v dt) ∧ CaseInv (caseF v dt).2 := by
  obtain ⟨E', hE', hP, -⟩ := case_structure
  rw [hE] at hE'
  cases hE'
  obtain ⟨c, s, d, q, qd, rfl, hc, hs, hdw, hq, hqd⟩ := hv
  have hE0 := hE
  sv_seq_inst [cs.e, cs.pdesign] at hE0
  have hshape : E.ShapeV (view c s d q qd) := by
    subst hE0; simp [CoreMemDesign.ShapeV, view, hc, hs, hdw, hq, hqd]
  have hdi : E.dataInputs "clk" = ["sel", "d"] := by
    subst hE0; simp [CoreMemDesign.dataInputs, Elab.toDesign2, Design2.inputNames]
  have hs' : (appliedIn dt (view c s d q qd) "sel").width = 2 :=
    CoreMemDesign.appliedIn_width hd (by simp [hdi]) (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
      (by simp [view, SvState.lookup]) hs
  have hd' : (appliedIn dt (view c s d q qd) "d").width = 4 :=
    CoreMemDesign.appliedIn_width hd (by simp [hdi]) (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
      (by simp [view, SvState.lookup]) hdw
  refine ⟨?_, ⟨_, _, _, _, _, rfl, rfl, hs', hd', caseQ_width hd', caseD_width hd'⟩⟩
  rw [CoreMemDesign.cycleV_applied hP hshape dt, CoreMemDesign.appliedEntry, hdi]
  simp only [List.map_cons, List.map_nil]
  unfold caseF
  generalize appliedIn dt (view c s d q qd) "sel" = s' at hs' ⊢
  generalize appliedIn dt (view c s d q qd) "d" = d' at hd' ⊢
  sv_seq_cycle hcyc : E.cycleV "clk" (view c s d q qd) [("sel", s'), ("d", d')] using hE0
    [view, hc, hs, hdw, hq, hqd, hs', hd']
  rw [hcyc]
  simp only [view, lk, SvState.lookup, caseQ, caseD, i00, i01, i1x, iz1, hA, hB, hC, hD, hF, String.reduceBEq,
    Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Option.getD_some, beq_iff_eq]

/-! ## 3. The claim, over every run -/

theorem i00_known : i00 = LVec.ofBitVec 0#2 := by decide
theorem i01_known : i01 = LVec.ofBitVec 1#2 := by decide

theorem ofBool_ne_lx (c : Bool) : Logic.ofBool c ≠ Logic.lx := by cases c <;> decide
theorem ofBool_ne_lz (c : Bool) : Logic.ofBool c ≠ Logic.lz := by cases c <;> decide

/-- A known vector has no x bit. -/
theorem known_ne_i1x (b : BitVec 2) : LVec.ofBitVec b ≠ i1x := by
  intro h
  have := congrArg (fun v : LVec => v.bits[0]?) h
  simp [i1x, LVec.getElem?_ofBitVec, ofBool_ne_lx] at this

/-- A known vector has no z bit. -/
theorem known_ne_iz1 (b : BitVec 2) : LVec.ofBitVec b ≠ iz1 := by
  intro h
  have := congrArg (fun v : LVec => v.bits[1]?) h
  simp [iz1, LVec.getElem?_ofBitVec, ofBool_ne_lz] at this

/-- **The knownness bridge for the first case**: on a known selector the x/z items never match. -/
theorem caseQ_known (b : BitVec 2) (d : LVec) :
    caseQ (LVec.ofBitVec b) d = if b = 0#2 then d else if b = 1#2 then hA else hF := by
  simp only [caseQ, beq_iff_eq, i00_known, i01_known, LVec.ofBitVec_inj, known_ne_i1x, known_ne_iz1, ↓reduceIte]

/-- **The case claim** about the samples of a run. -/
def CaseClaim (tr : List (SvState × SvState)) : Prop :=
  ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc → ∀ s d,
    SvState.lookup pc.1 "sel" = some s → SvState.lookup pc.1 "d" = some d →
    -- after the edge: the case functions of the `sel` and `d` the cycle saw, every 4-state `sel`
    SvState.lookup pc.2 "q" = some (caseQ s d) ∧ SvState.lookup pc.2 "q_default" = some (caseD s d) ∧
    -- a known `sel` never matches the x/z items
    (∀ b : BitVec 2, s = LVec.ofBitVec b →
      SvState.lookup pc.2 "q" = some (if b = 0#2 then d else if b = 1#2 then hA else hF)) ∧
    -- before the edge: the previous cycle's outputs
    (∀ pp, tr[c - 1]? = some pp → 1 ≤ c →
      SvState.lookup pc.1 "q" = SvState.lookup pp.2 "q" ∧
        SvState.lookup pc.1 "q_default" = SvState.lookup pp.2 "q_default")

/-- The cycle before cycle `c ≥ 1` of a run, and the view cycle `c` starts from (its post sample). -/
theorem prev_cycle (v : SvState) (ins : List SvState) (c : Nat) (pp : SvState × SvState) (hc : 1 ≤ c)
    (hpp : (runF caseF v ins)[c - 1]? = some pp) :
    ∃ u d', pp = caseF u d' ∧ stF caseF v ins c = (caseF u d').2 := by
  rw [runF_getElem?] at hpp
  cases hin : ins[c - 1]? with
  | none => simp [hin] at hpp
  | some d =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpp
      subst hpp
      obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
      exact ⟨_, d, rfl, stF_succ caseF v ins k d (by simpa using hin)⟩

theorem caseClaim_of_runF (v : SvState) (ins : List SvState) : CaseClaim (runF caseF v ins) := by
  intro c pc hpc
  rw [runF_getElem?] at hpc
  cases hin : ins[c]? with
  | none => simp [hin] at hpc
  | some dt =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpc
      subst hpc
      intro s d hs hd
      simp only [caseF, view, SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
        Option.some.injEq] at hs hd ⊢
      subst hs hd
      refine ⟨rfl, rfl, fun b hb => by rw [hb, caseQ_known], fun pp hpp hc => ?_⟩
      obtain ⟨u, d', rfl, hw⟩ := prev_cycle v ins c pp hc hpp
      rw [hw]
      simp [caseF, view, lk, SvState.lookup]

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state, on every typed stimulus. -/
theorem case_runs : SeqRuns cs.e "clk" CaseClaim := by
  obtain ⟨E, hE, hP, hO⟩ := case_structure
  have hE0 := hE
  sv_seq_inst [cs.e, cs.pdesign] at hE0
  refine SeqRuns.of_cycleFn hE hP hO (by subst hE0; simp [Elab.toDesign2, Design2.declWidth]) CaseInv ?_
    caseF (fun v dt hv hd => case_cycle hE v dt hv hd) (fun v ins _ _ => caseClaim_of_runF v ins)
  intro v hsh
  subst hE0
  obtain ⟨hk, hw⟩ := hsh
  rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨⟨n5, x5⟩, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
    simp at hk hw
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk
  exact ⟨x1, x2, x3, x4, x5, rfl, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩

#print axioms case_structure
#print axioms case_ports
#print axioms case_cycle
#print axioms caseQ_known
#print axioms case_runs

end Examples.«system-verilog».seq_cycle.case_proof
