import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleTactic

/-!
# The packed shift register on the ordinary E route, at every `N ≥ 2`, over every run

The census design `sem2/packed_shift_canonical_e` (the clean-room fixture `packed_shift_register.sv`, verbatim but for
the module name):

```systemverilog
module packed_shift_canonical_e #(parameter integer N=4) (input logic clk, input logic v, output logic [N-1:0] q);
  logic [N-1:0] t;
  always_ff @(posedge clk) t <= {t[N-2:0], v};
  assign q = t;
endmodule
```

Its meaning is the loader's ordinary E entry `shreg.e N : Res CoreMemDesign` and the route's slot function
`CoreMemDesign.step`; a clock cycle is two slots under the rising-edge clocking discipline (`SeqCycle.lean`).

1. **Structure** (`shreg_structure`): the instantiation succeeds at every `2 ≤ N < 2^30` and is in the clocked profile
   (`sv_seq_inst`, `sv_seq_profile`).
2. **Cycle equations** (`shreg_cycle`): from any view of the declarations' shape and any typed data entry, the cycle's
   pre sample holds the applied input and the old register, the post sample holds `t` shifted by one with the input at
   bit 0, and `q = t` (computed by `sv_seq_cycle`, restated with the named shift `sh`).
3. **The claim** (`shreg_runs`): in EVERY run of the route, from EVERY coherent state (the x start and every power-up
   included), on every typed stimulus: in every cycle `c`, bit `k < N` of `q` in the post sample is the bit the input
   `v` had in the pre sample of cycle `c - k`, for every `k ≤ c`. Exact on 4-state values: an x input travels as an x.

Oracle: Icarus Verilog 12.0 (stable), a testbench outside the repository: the x start, x and z inputs,
`N = 2, 4, 8`.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.shreg_proof

load_design_sv2 shreg from "Examples/system-verilog/sem2/packed_shift_canonical_e/packed_shift_canonical_e.sv.json"

-- Runs on the route at `N = 4` (compiled): the x start, then a 1 shifted in, then a 0.
#guard (match shreg.e 4 with
  | .ok E => match runCoreMemRows E E.initial (cycleRows "clk" [[("v", .ofNat 1 1)], [("v", .ofNat 1 0)]]) with
    | .ok rows => rows.map (fun s => SvState.showSignal (CoreMemState.view E s) "q") ==
        ["xxxx", "xxx1", "xxx1", "xx10"]
    | _ => false
  | _ => false)

/-! ## 1. Structure -/

set_option maxHeartbeats 1000000 in
theorem shreg_structure (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) :
    SeqDesign (shreg.e N) "clk" := by
  cases hE : shreg.e N with
  | ok E =>
      sv_seq_inst [shreg.e, shreg.pdesign] at hE
      subst hE
      exact ⟨_, rfl, by sv_seq_profile, by sv_seq_obligations⟩
  | timeout => sv_seq_inst [shreg.e, shreg.pdesign] at hE
  | unsupported m => sv_seq_inst [shreg.e, shreg.pdesign] at hE

/-- **The interface**: the ports with their declared widths, in declaration order. -/
theorem shreg_ports (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) :
    SeqPorts (shreg.e N) [("clk", 1), ("v", 1)] [("q", N)] := by
  obtain ⟨E, hE, -, -⟩ := shreg_structure N h1 h2
  refine ⟨E, hE, ?_⟩
  sv_seq_inst [shreg.e, shreg.pdesign] at hE
  subst hE
  constructor <;> sv_seq_ports

/-! ## 2. The cycle equations -/

/-- One shift: bits `N-2 … 0` of `t` move up by one, the input enters at bit 0. -/
def sh (N : Nat) (t a : LVec) : LVec := t.insertAt 0 ((t.extract 0 (N - 1)).concat a)

theorem toNat_sub_two_add_one (N : Nat) (h : 2 ≤ N) : ((N : Int) - 2 + 1).toNat = N - 1 := by omega

set_option maxHeartbeats 2000000 in
/-- **The cycle equations**: from a view of the declarations' shape and a typed data entry, the pre sample holds the
input the entry applies (or the old input, if the entry has none) and the old register; the post sample the shifted
register in both `t` and `q`. -/
theorem shreg_cycle (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : shreg.e N = .ok E)
    (c a qq tt : LVec) (ha : a.width = 1) (hq : qq.width = N) (ht : tt.width = N)
    (d : SvState) (hd : E.DataTyped "clk" d) :
    ∃ a', a'.width = 1 ∧ (SvState.lookup d "v" = some a' ∨ (SvState.lookup d "v" = none ∧ a' = a)) ∧
      E.cycleV "clk" [("clk", c), ("v", a), ("q", qq), ("t", tt)] d =
        .ok ([("clk", ⟨#[.l0]⟩), ("v", a'), ("q", tt), ("t", tt)],
          [("clk", ⟨#[.l1]⟩), ("v", a'), ("q", sh N tt a'), ("t", sh N tt a')]) := by
  sv_seq_inst [shreg.e, shreg.pdesign] at hE
  cases hv : SvState.lookup d "v" with
  | some vin =>
      have hvin : vin.width = 1 := by
        have := hd "v" vin (by subst hE; simp [Elab.toDesign2, Design2.inputNames])
          (by simp [lowEntry, SvState.lookup, hv])
        subst hE
        simp [Elab.toDesign2, Design2.declWidth] at this
        omega
      refine ⟨vin, hvin, Or.inl rfl, ?_⟩
      sv_seq_cycle hcyc : E.cycleV "clk" [("clk", c), ("v", a), ("q", qq), ("t", tt)] d using hE
        [hv, hvin, ha, hq, ht]
      rw [hcyc, toNat_sub_two_add_one N h1]
      rfl
  | none =>
      refine ⟨a, ha, Or.inr ⟨rfl, rfl⟩, ?_⟩
      sv_seq_cycle hcyc : E.cycleV "clk" [("clk", c), ("v", a), ("q", qq), ("t", tt)] d using hE
        [hv, ha, hq, ht]
      rw [hcyc, toNat_sub_two_add_one N h1]
      rfl


/-! ## 3. The claim, over every run -/

/-- **The shift register's claim** about the samples of a run (one pair per cycle): in cycle `c`, bit `k < N` of `q`
in the post sample is the bit the input `v` had in the pre sample of cycle `c - k`, for every `k ≤ c`. -/
def ShiftClaim (N : Nat) (tr : List (SvState × SvState)) : Prop :=
  ∀ (c k : Nat) (pc pk : SvState × SvState), tr[c]? = some pc → tr[c - k]? = some pk → k < N → k ≤ c →
    ∃ q v, SvState.lookup pc.2 "q" = some q ∧ SvState.lookup pk.1 "v" = some v ∧ q.bits[k]? = v.bits[0]?

theorem sh_width (N : Nat) (t a : LVec) : (sh N t a).width = t.width := by
  simp [sh, LVec.insertAt, LVec.width]

theorem sh_bit0 {N : Nat} (h : 2 ≤ N) {t a : LVec} (ht : t.width = N) (ha : a.width = 1) :
    (sh N t a).bits[0]? = a.bits[0]? := by
  have ha' : a.bits.size = 1 := ha
  have ht' : t.bits.size = N := ht
  simp [sh, LVec.insertAt, LVec.concat, LVec.extract, LVec.width, ht', ha', Array.getElem?_append_left,
    show 0 < N by omega]

theorem sh_bit_succ {N : Nat} (h : 2 ≤ N) {t a : LVec} (ht : t.width = N) (ha : a.width = 1) {k : Nat}
    (hk : k + 1 < N) : (sh N t a).bits[k + 1]? = t.bits[k]? := by
  have ha' : a.bits.size = 1 := ha
  have ht' : t.bits.size = N := ht
  have hk' : k < t.bits.size := by omega
  simp [sh, LVec.insertAt, LVec.concat, LVec.extract, LVec.width, ht', ha', hk, Array.getElem?_append_right,
    show k < N - 1 by omega, Array.getElem?_eq_getElem hk']
  intro h'
  exfalso
  omega

/-- One cycle of a run, as the cycle equations give it: the input `a` and the register `t` it starts from. -/
structure Cyc (N : Nat) (pp : SvState × SvState) (a t : LVec) : Prop where
  pre : pp.1 = [("clk", ⟨#[.l0]⟩), ("v", a), ("q", t), ("t", t)]
  post : pp.2 = [("clk", ⟨#[.l1]⟩), ("v", a), ("q", sh N t a), ("t", sh N t a)]
  wa : a.width = 1
  wt : t.width = N

theorem Cyc.unique {N : Nat} {pp : SvState × SvState} {a t a' t' : LVec} (h : Cyc N pp a t) (h' : Cyc N pp a' t') :
    a = a' ∧ t = t' := by
  have := h.pre.symm.trans h'.pre
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at this
  exact ⟨this.1, this.2.1⟩

set_option maxHeartbeats 1000000 in
/-- **The trace of a run**: every cycle is a `Cyc`; the first starts from the start view's register, every later one
from the register its predecessor's post sample shows. -/
theorem shreg_trace (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : shreg.e N = .ok E) :
    ∀ (ins : List SvState) (c0 a0 q0 t0 : LVec), a0.width = 1 → q0.width = N → t0.width = N →
      (∀ d ∈ ins, E.DataTyped "clk" d) → ∀ tr,
      E.runV "clk" [("clk", c0), ("v", a0), ("q", q0), ("t", t0)] ins = .ok tr →
      ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc → ∃ a t, Cyc N pc a t ∧ (c = 0 → t = t0) ∧
        ∀ (c' : Nat) (pc' : SvState × SvState) (a' t' : LVec), c = c' + 1 → tr[c']? = some pc' →
          Cyc N pc' a' t' → t = sh N t' a'
  | [], _, _, _, _, _, _, _, _, tr, htr => by
      simp only [CoreMemDesign.runV, Res.ok.injEq] at htr
      subst htr
      intro c pc hc
      simp at hc
  | d :: ds, c0, a0, q0, t0, ha0, hq0, ht0, hd, tr, htr => by
      obtain ⟨a', ha', -, hcyc⟩ := shreg_cycle N h1 h2 hE c0 a0 q0 t0 ha0 hq0 ht0 d (hd d (by simp))
      simp only [CoreMemDesign.runV, hcyc, Res.ok_bind, Res.bind_eq_ok, Res.ok.injEq] at htr
      obtain ⟨rest, hrest, rfl⟩ := htr
      have hcyc0 : Cyc N ([("clk", ⟨#[.l0]⟩), ("v", a'), ("q", t0), ("t", t0)],
          [("clk", ⟨#[.l1]⟩), ("v", a'), ("q", sh N t0 a'), ("t", sh N t0 a')]) a' t0 :=
        ⟨rfl, rfl, ha', ht0⟩
      have ih := shreg_trace N h1 h2 hE ds _ _ _ (sh N t0 a') ha' (by rw [sh_width, ht0]) (by rw [sh_width, ht0])
        (fun d' hd' => hd d' (by simp [hd'])) rest hrest
      intro c pc hc
      cases c with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst hc
          exact ⟨a', t0, hcyc0, fun _ => rfl, fun c' _ _ _ h _ _ => absurd h (by omega)⟩
      | succ c =>
          simp only [List.getElem?_cons_succ] at hc
          obtain ⟨a, t, hpc, h0, hlink⟩ := ih c pc hc
          refine ⟨a, t, hpc, fun h => absurd h (by omega), fun c' pc' a'' t'' hcc hpc' hcyc' => ?_⟩
          obtain rfl : c' = c := by omega
          cases c' with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hpc'
              subst hpc'
              obtain ⟨rfl, rfl⟩ := hcyc0.unique hcyc'
              exact h0 rfl
          | succ c'' =>
              simp only [List.getElem?_cons_succ] at hpc'
              exact hlink c'' pc' a'' t'' rfl hpc' hcyc'

/-- **The claim from the trace**, by induction on `k`. -/
theorem shiftClaim_of_trace (N : Nat) (h1 : 2 ≤ N) (tr : List (SvState × SvState)) (t0 : LVec)
    (htr : ∀ (c : Nat) (pc : SvState × SvState), tr[c]? = some pc → ∃ a t, Cyc N pc a t ∧ (c = 0 → t = t0) ∧
      ∀ (c' : Nat) (pc' : SvState × SvState) (a' t' : LVec), c = c' + 1 → tr[c']? = some pc' →
        Cyc N pc' a' t' → t = sh N t' a') :
    ShiftClaim N tr := by
  have key : ∀ (k c : Nat) (pc : SvState × SvState) (a t : LVec), tr[c]? = some pc → Cyc N pc a t → k < N →
      k ≤ c → ∃ pk ak tk, tr[c - k]? = some pk ∧ Cyc N pk ak tk ∧ (sh N t a).bits[k]? = ak.bits[0]? := by
    intro k
    induction k with
    | zero =>
        intro c pc a t hc hcyc _ _
        exact ⟨pc, a, t, by simpa using hc, hcyc, sh_bit0 h1 hcyc.wt hcyc.wa⟩
    | succ k ih =>
        intro c pc a t hc hcyc hk hkc
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        have hlt : c' < tr.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1
          omega
        obtain ⟨a', t', hcyc', -, -⟩ := htr c' tr[c'] (List.getElem?_eq_getElem hlt)
        obtain ⟨a2, t2, hcyc2, -, hlink⟩ := htr (c' + 1) pc hc
        obtain ⟨rfl, rfl⟩ := hcyc.unique hcyc2
        have ht : t = sh N t' a' := hlink c' tr[c'] a' t' rfl (List.getElem?_eq_getElem hlt) hcyc'
        obtain ⟨pk, ak, tk, hpk, hcyck, hbit⟩ :=
          ih c' tr[c'] a' t' (List.getElem?_eq_getElem hlt) hcyc' (by omega) (by omega)
        refine ⟨pk, ak, tk, by rwa [show c' + 1 - (k + 1) = c' - k by omega], hcyck, ?_⟩
        rw [sh_bit_succ h1 hcyc.wt hcyc.wa (by omega), ht, hbit]
  intro c k pc pk hc hk hkN hkc
  obtain ⟨a, t, hcyc, -, -⟩ := htr c pc hc
  obtain ⟨pk', ak, tk, hpk', hcyck, hbit⟩ := key k c pc a t hc hcyc hkN hkc
  rw [hk] at hpk'
  cases hpk'
  refine ⟨sh N t a, ak, ?_, ?_, hbit⟩
  · rw [hcyc.post]; rfl
  · rw [hcyck.pre]; rfl

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state, on every typed stimulus, `q` holds the last
`N` inputs: bit `k` of `q` after cycle `c` is the input of cycle `c - k`. -/
theorem shreg_runs (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) : SeqRuns (shreg.e N) "clk" (ShiftClaim N) := by
  obtain ⟨E, hE, hP, hO⟩ := shreg_structure N h1 h2
  have hE0 := hE
  sv_seq_inst [shreg.e, shreg.pdesign] at hE0
  refine SeqRuns.intro hE hP hO (by subst hE0; simp [Elab.toDesign2, Design2.declWidth])
    (fun v => ∃ c a q t, v = [("clk", c), ("v", a), ("q", q), ("t", t)] ∧ a.width = 1 ∧ q.width = N ∧
      t.width = N) ?_ ?_ ?_
  · intro v hs
    subst hE0
    obtain ⟨hk, hw⟩ := hs
    rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
      simp at hk hw
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
    exact ⟨x1, x2, x3, x4, rfl, hw.2.1, hw.2.2.1, hw.2.2.2⟩
  · rintro v d ⟨c, a, q, t, rfl, ha, hq, ht⟩ hd
    obtain ⟨a', ha', -, hcyc⟩ := shreg_cycle N h1 h2 hE c a q t ha hq ht d hd
    exact ⟨_, _, hcyc, ⟨_, a', _, _, rfl, ha', by rw [sh_width, ht], by rw [sh_width, ht]⟩⟩
  · rintro v ins tr ⟨c, a, q, t, rfl, ha, hq, ht⟩ hd htr
    exact shiftClaim_of_trace N h1 tr t (shreg_trace N h1 h2 hE ins c a q t ha hq ht hd tr htr)

#print axioms shreg_structure
#print axioms shreg_ports
#print axioms shreg_cycle
#print axioms shreg_runs

end Examples.«system-verilog».seq_cycle.shreg_proof
