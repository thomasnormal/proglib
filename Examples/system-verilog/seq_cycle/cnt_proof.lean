import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleTactic

/-!
# The counter with synchronous reset and enable on the ordinary E route, at every `N ≥ 1`, over every run

The census design `sem2/clk_cnt`:

```systemverilog
module clk_cnt #(parameter int N = 4) (input logic clk, rst, en, output logic [N-1:0] q);
  always_ff @(posedge clk)
    if (rst) q <= '0;
    else if (en) q <= q + 1'b1;
endmodule
```

1. **Structure** (`cnt_structure`): the instantiation at every `1 ≤ N < 2^30`, in the clocked profile.
2. **Cycle equations** (`cnt_cycle`): the post sample's `q` is `cntNext` of the pre sample (reset to 0 when `rst`
   reads 1, `q + 1` when `en` reads 1, else held), computed by `sv_seq_cycle` for each outcome of the two decisions.
3. **The claim** (`cnt_runs`): in every run, from every coherent state (the x start and every power-up included), on
   every typed stimulus: if cycle `c` sees `rst = 1`, and each of the next `n` cycles sees `rst = 0` and `en = 1`, then
   `q` after cycle `c + n` is `n mod 2^N`. The decisions read known values (rule 4's cheap sufficient condition: the
   claim's hypotheses give `rst` and `en` as 0/1 values, so E's `if` takes the only branch every resolution would).

Oracle: Icarus Verilog 12.0 (stable), a testbench outside the repository.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.cnt_proof

load_design_sv2 cnt from "Examples/system-verilog/sem2/clk_cnt/clk_cnt.sv.json"

-- Runs on the route at `N = 4` (compiled): reset, then three enabled cycles, then one held.
#guard (match cnt.e 4 with
  | .ok E => match runCoreMemRows E E.initial (cycleRows "clk"
      [[("rst", .ofNat 1 1), ("en", .ofNat 1 0)], [("rst", .ofNat 1 0), ("en", .ofNat 1 1)],
       [("rst", .ofNat 1 0), ("en", .ofNat 1 1)], [("rst", .ofNat 1 0), ("en", .ofNat 1 1)],
       [("rst", .ofNat 1 0), ("en", .ofNat 1 0)]]) with
    | .ok rows => (cyclePairs rows).map (fun pp => SvState.showSignal (CoreMemState.view E pp.2) "q") ==
        ["0000", "0001", "0010", "0011", "0011"]
    | _ => false
  | _ => false)

/-! ## 1. Structure -/

set_option maxHeartbeats 1000000 in
theorem cnt_structure (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) :
    SeqDesign (cnt.e N) "clk" := by
  cases hE : cnt.e N with
  | ok E =>
      sv_seq_inst [cnt.e, cnt.pdesign] at hE
      subst hE
      exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
  | timeout => sv_seq_inst [cnt.e, cnt.pdesign] at hE
  | unsupported m => sv_seq_inst [cnt.e, cnt.pdesign] at hE

/-- **The interface**: the ports with their declared widths, in declaration order. -/
theorem cnt_ports (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) :
    SeqPorts (cnt.e N) [("clk", 1), ("rst", 1), ("en", 1)] [("q", N)] := by
  obtain ⟨E, hE, -, -⟩ := cnt_structure N h1 h2
  refine ⟨E, hE, ?_⟩
  sv_seq_inst [cnt.e, cnt.pdesign] at hE
  subst hE
  constructor <;> sv_seq_ports

/-! ## 2. The cycle equations -/

/-- The counter's next value: 0 on reset, `q + 1` when enabled, else `q` (the route's `if` reads `condTrue`). -/
def cntNext (N : Nat) (q r e : LVec) : LVec :=
  if r.condTrue then LVec.ofBitVec 0#N
  else if e.condTrue then q.add ((⟨#[.l1]⟩ : LVec).resizeU N) else q

/-- The input an entry applies: its own value, or the held one. -/
def applied (d : SvState) (n : String) (old : LVec) : LVec := (SvState.lookup d n).getD old

set_option maxHeartbeats 2000000 in
/-- **The cycle equations**: the pre sample holds the applied inputs and the old count, the post sample `cntNext`. -/
theorem cnt_cycle (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : cnt.e N = .ok E)
    (c r e qq : LVec) (hr : r.width = 1) (he : e.width = 1) (hq : qq.width = N)
    (d : SvState) (hd : E.DataTyped "clk" d) :
    (applied d "rst" r).width = 1 ∧ (applied d "en" e).width = 1 ∧
      E.cycleV "clk" [("clk", c), ("rst", r), ("en", e), ("q", qq)] d =
        .ok ([("clk", ⟨#[.l0]⟩), ("rst", applied d "rst" r), ("en", applied d "en" e), ("q", qq)],
          [("clk", ⟨#[.l1]⟩), ("rst", applied d "rst" r), ("en", applied d "en" e),
            ("q", cntNext N qq (applied d "rst" r) (applied d "en" e))]) := by
  sv_seq_inst [cnt.e, cnt.pdesign] at hE
  -- the widths of the applied inputs (the entry is typed)
  have hw : ∀ n old, n = "rst" ∨ n = "en" → old.width = 1 → (applied d n old).width = 1 := by
    intro n old hn hold
    unfold applied
    cases hl : SvState.lookup d n with
    | none => exact hold
    | some v =>
        have hin : n ∈ E.scalar.toDesign2.inputNames.toList := by
          subst hE; rcases hn with rfl | rfl <;> simp [Elab.toDesign2, Design2.inputNames]
        have hdw : E.scalar.toDesign2.declWidth n = some 1 := by
          subst hE; rcases hn with rfl | rfl <;> simp [Elab.toDesign2, Design2.declWidth]
        have := hd n v hin (by rcases hn with rfl | rfl <;> simp [lowEntry, SvState.lookup, hl])
        rw [hdw] at this
        simp only [Option.getD_some]
        exact (Option.some.inj this).symm
  have hrw := hw "rst" r (Or.inl rfl) hr
  have hew := hw "en" e (Or.inr rfl) he
  refine ⟨hrw, hew, ?_⟩
  -- the cycle reads the entry only through the inputs it applies
  rw [CoreMemDesign.cycleV_congr_data E "clk" _ d [("rst", applied d "rst" r), ("en", applied d "en" e)] (by
    subst hE
    unfold applied
    simp only [applyInputs2, Elab.toDesign2, lowEntry]
    cases h1 : SvState.lookup d "rst" <;> cases h2 : SvState.lookup d "en" <;>
      simp [h1, h2, SvState.lookup, SvState.set])]
  generalize applied d "rst" r = r' at hrw ⊢
  generalize applied d "en" e = e' at hew ⊢
  by_cases hr1 : r'.condTrue = true
  · sv_seq_cycle hcyc : E.cycleV "clk" [("clk", c), ("rst", r), ("en", e), ("q", qq)]
        [("rst", r'), ("en", e')] using hE [hr1, hrw, hew, hq, hr, he]
    rw [hcyc, seqE_insertAt_zero (by simp [hq])]
    simp [cntNext, hr1]
  · by_cases he1 : e'.condTrue = true
    · sv_seq_cycle hcyc : E.cycleV "clk" [("clk", c), ("rst", r), ("en", e), ("q", qq)]
          [("rst", r'), ("en", e')] using hE [hr1, he1, hrw, hew, hq, hr, he]
      rw [hcyc, seqE_insertAt_zero (by simp [seqE_width_add, hq])]
      simp [cntNext, hr1, he1]
    · sv_seq_cycle hcyc : E.cycleV "clk" [("clk", c), ("rst", r), ("en", e), ("q", qq)]
          [("rst", r'), ("en", e')] using hE [hr1, he1, hrw, hew, hq, hr, he]
      rw [hcyc]
      simp [cntNext, hr1, he1]


/-! ## 3. The claim, over every run -/

/-- **The counter's claim** about the samples of a run: if cycle `c` sees `rst = 1` and each of the next `n` cycles
sees `rst = 0` and `en = 1`, then `q` after cycle `c + n` is `n` modulo `2^N`. -/
def CntClaim (N : Nat) (tr : List (SvState × SvState)) : Prop :=
  ∀ (c n : Nat) (pp : SvState × SvState), tr[c + n]? = some pp →
    (∀ p0, tr[c]? = some p0 → SvState.lookup p0.1 "rst" = some (LVec.ofNat 1 1)) →
    (∀ j pj, c < j → j ≤ c + n → tr[j]? = some pj →
      SvState.lookup pj.1 "rst" = some (LVec.ofNat 1 0) ∧ SvState.lookup pj.1 "en" = some (LVec.ofNat 1 1)) →
    SvState.lookup pp.2 "q" = some (LVec.ofBitVec (BitVec.ofNat N n))

theorem cntNext_width {N : Nat} {q r e : LVec} (hq : q.width = N) : (cntNext N q r e).width = N := by
  unfold cntNext
  split
  · simp
  · split
    · simp [seqE_width_add, hq]
    · exact hq

theorem one_resize (N : Nat) (h : 1 ≤ N) : (⟨#[.l1]⟩ : LVec).resizeU N = LVec.ofBitVec (1#N) := by
  have h1 : (⟨#[.l1]⟩ : LVec) = LVec.ofBitVec (1#1) := by decide
  rw [h1, LVec.resizeU_ofBitVec]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have : 1 < 2 ^ N := Nat.one_lt_two_pow (by omega)
  simp [Nat.mod_eq_of_lt this]

theorem cntNext_reset (N : Nat) (q e : LVec) : cntNext N q (LVec.ofNat 1 1) e = LVec.ofBitVec (BitVec.ofNat N 0) := by
  simp [cntNext]

theorem cntNext_count (N : Nat) (h : 1 ≤ N) (n : Nat) :
    cntNext N (LVec.ofBitVec (BitVec.ofNat N n)) (LVec.ofNat 1 0) (LVec.ofNat 1 1) =
      LVec.ofBitVec (BitVec.ofNat N (n + 1)) := by
  simp only [cntNext, show (LVec.ofNat 1 0).condTrue = false by simp,
    show (LVec.ofNat 1 1).condTrue = true by simp, Bool.false_eq_true, ↓reduceIte, one_resize N h,
    LVec.add_ofBitVec]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

/-- One cycle of a run of the counter: the inputs `r`, `e` and the count `q` it starts from. -/
structure CCyc (N : Nat) (pp : SvState × SvState) (r e q : LVec) : Prop where
  pre : pp.1 = [("clk", ⟨#[.l0]⟩), ("rst", r), ("en", e), ("q", q)]
  post : pp.2 = [("clk", ⟨#[.l1]⟩), ("rst", r), ("en", e), ("q", cntNext N q r e)]
  wr : r.width = 1
  we : e.width = 1
  wq : q.width = N

theorem CCyc.unique {N : Nat} {pp : SvState × SvState} {r e q r' e' q' : LVec} (h : CCyc N pp r e q)
    (h' : CCyc N pp r' e' q') : r = r' ∧ e = e' ∧ q = q' := by
  have := h.pre.symm.trans h'.pre
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at this
  exact this

set_option maxHeartbeats 1000000 in
/-- **The trace of a run** of the counter: every cycle is a `CCyc`; the first starts from the start view's count,
every later one from the count its predecessor's post sample shows. -/
theorem cnt_trace (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : cnt.e N = .ok E) :
    ∀ (ins : List SvState) (c0 r0 e0 q0 : LVec), r0.width = 1 → e0.width = 1 → q0.width = N →
      (∀ d ∈ ins, E.DataTyped "clk" d) → ∀ tr,
      E.runV "clk" [("clk", c0), ("rst", r0), ("en", e0), ("q", q0)] ins = .ok tr →
      ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc → ∃ r e q, CCyc N pc r e q ∧ (c = 0 → q = q0) ∧
        ∀ (c' : Nat) (pc' : SvState × SvState) (r' e' q' : LVec), c = c' + 1 → tr[c']? = some pc' →
          CCyc N pc' r' e' q' → q = cntNext N q' r' e'
  | [], _, _, _, _, _, _, _, _, tr, htr => by
      simp only [CoreMemDesign.runV, Res.ok.injEq] at htr
      subst htr
      intro c pc hc
      simp at hc
  | d :: ds, c0, r0, e0, q0, hr0, he0, hq0, hd, tr, htr => by
      obtain ⟨hrw, hew, hcyc⟩ := cnt_cycle N h1 h2 hE c0 r0 e0 q0 hr0 he0 hq0 d (hd d (by simp))
      simp only [CoreMemDesign.runV, hcyc, Res.ok_bind, Res.bind_eq_ok, Res.ok.injEq] at htr
      obtain ⟨rest, hrest, rfl⟩ := htr
      have hcyc0 : CCyc N ([("clk", ⟨#[.l0]⟩), ("rst", applied d "rst" r0), ("en", applied d "en" e0),
          ("q", q0)], [("clk", ⟨#[.l1]⟩), ("rst", applied d "rst" r0), ("en", applied d "en" e0),
          ("q", cntNext N q0 (applied d "rst" r0) (applied d "en" e0))]) (applied d "rst" r0)
          (applied d "en" e0) q0 := ⟨rfl, rfl, hrw, hew, hq0⟩
      have ih := cnt_trace N h1 h2 hE ds _ _ _ (cntNext N q0 (applied d "rst" r0) (applied d "en" e0)) hrw hew
        (cntNext_width hq0) (fun d' hd' => hd d' (by simp [hd'])) rest hrest
      intro c pc hc
      cases c with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst hc
          exact ⟨_, _, q0, hcyc0, fun _ => rfl, fun c' _ _ _ _ h _ _ => absurd h (by omega)⟩
      | succ c =>
          simp only [List.getElem?_cons_succ] at hc
          obtain ⟨r, e, q, hpc, h0, hlink⟩ := ih c pc hc
          refine ⟨r, e, q, hpc, fun h => absurd h (by omega), fun c' pc' r'' e'' q'' hcc hpc' hcyc' => ?_⟩
          obtain rfl : c' = c := by omega
          cases c' with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hpc'
              subst hpc'
              obtain ⟨rfl, rfl, rfl⟩ := hcyc0.unique hcyc'
              exact h0 rfl
          | succ c'' =>
              simp only [List.getElem?_cons_succ] at hpc'
              exact hlink c'' pc' r'' e'' q'' rfl hpc' hcyc'

/-- **The claim from the trace**, by induction on `n`. -/
theorem cntClaim_of_trace (N : Nat) (h1 : 1 ≤ N) (tr : List (SvState × SvState)) (q0 : LVec)
    (htr : ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc → ∃ r e q, CCyc N pc r e q ∧ (c = 0 → q = q0) ∧
      ∀ (c' : Nat) (pc' : SvState × SvState) (r' e' q' : LVec), c = c' + 1 → tr[c']? = some pc' →
        CCyc N pc' r' e' q' → q = cntNext N q' r' e') :
    CntClaim N tr := by
  intro c n
  induction n with
  | zero =>
      intro pp hpp hrst _
      simp only [Nat.add_zero] at hpp
      obtain ⟨r, e, q, hcyc, -, -⟩ := htr c pp hpp
      have hr := hrst pp hpp
      rw [hcyc.pre] at hr
      simp only [SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
        Option.some.injEq] at hr
      rw [hcyc.post, hr, cntNext_reset]
      simp [SvState.lookup]
  | succ n ih =>
      intro pp hpp hrst hrun
      have hlt : c + n < tr.length := by
        have := (List.getElem?_eq_some_iff.mp hpp).1
        omega
      have hprev := ih tr[c + n] (List.getElem?_eq_getElem hlt) hrst
        (fun j pj hj hjn hpj => hrun j pj hj (by omega) hpj)
      obtain ⟨r', e', q', hcyc', -, -⟩ := htr (c + n) tr[c + n] (List.getElem?_eq_getElem hlt)
      obtain ⟨r, e, q, hcyc, -, hlink⟩ := htr (c + (n + 1)) pp hpp
      have hq : q = cntNext N q' r' e' :=
        hlink (c + n) tr[c + n] r' e' q' (by omega) (List.getElem?_eq_getElem hlt) hcyc'
      rw [hcyc'.post] at hprev
      simp only [SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
        Option.some.injEq] at hprev
      obtain ⟨hr, he⟩ := hrun (c + (n + 1)) pp (by omega) (by omega) hpp
      rw [hcyc.pre] at hr he
      simp only [SvState.lookup, String.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
        Option.some.injEq] at hr he
      rw [hcyc.post, hr, he, hq, hprev, cntNext_count N h1 n]
      simp [SvState.lookup]

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state, on every typed stimulus, `n` enabled cycles
after a reset cycle the count is `n mod 2^N`. -/
theorem cnt_runs (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) : SeqRuns (cnt.e N) "clk" (CntClaim N) := by
  obtain ⟨E, hE, hP, -⟩ := cnt_structure N h1 h2
  have hE0 := hE
  sv_seq_inst [cnt.e, cnt.pdesign] at hE0
  refine SeqRuns.intro hE hP (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
    (fun v => ∃ c r e q, v = [("clk", c), ("rst", r), ("en", e), ("q", q)] ∧ r.width = 1 ∧ e.width = 1 ∧
      q.width = N) ?_ ?_ ?_
  · intro v hs
    subst hE0
    obtain ⟨hk, hw⟩ := hs
    rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
      simp at hk hw
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
    exact ⟨x1, x2, x3, x4, rfl, hw.2.1, hw.2.2.1, hw.2.2.2⟩
  · rintro v d ⟨c, r, e, q, rfl, hr, he, hq⟩ hd
    obtain ⟨hrw, hew, hcyc⟩ := cnt_cycle N h1 h2 hE c r e q hr he hq d hd
    exact ⟨_, _, hcyc, ⟨_, _, _, _, rfl, hrw, hew, cntNext_width hq⟩⟩
  · rintro v ins tr ⟨c, r, e, q, rfl, hr, he, hq⟩ hd htr
    exact cntClaim_of_trace N h1 tr q (cnt_trace N h1 h2 hE ins c r e q hr he hq hd tr htr)

#print axioms cnt_structure
#print axioms cnt_ports
#print axioms cnt_cycle
#print axioms cnt_runs

end Examples.«system-verilog».seq_cycle.cnt_proof
