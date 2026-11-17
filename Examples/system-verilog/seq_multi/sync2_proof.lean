import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# A two-flop synchronizer over every sequence of instants (LANGUAGE LEVEL)

The design `Examples/system-verilog/seq_multi/sync2/sync2.sv`:

```systemverilog
module sync2 (input logic clka, clkb, d, output logic q);
  logic src, s1, s2;
  always_ff @(posedge clka) src <= d;
  always_ff @(posedge clkb) begin s1 <= src; s2 <= s1; end
  assign q = s2;
endmodule
```

Its events are `posedge clka` and `posedge clkb`; its domains `clka: [src]` and `clkb: [s1, s2]`; ONE crossing,
computed: the `clkb` process reads `src`, a register of `clka`'s domain.

**LANGUAGE LEVEL.** Every statement here is about the SystemVerilog semantics (IEEE 1800-2023 §9.4.2, §10.4.2): at a
rising edge of `clkb` the process reads the committed value of `src`, its value before the slot, even when `clka`
rises in the same slot (the nonblocking update of `src` commits after every woken process has read). In hardware a
flop sampling `src` while it changes can go metastable and resolve either way; nothing here models that, and no
statement here is a hardware claim (a hardware layer would attach at exactly this read).

**What connects these theorems to the envelope.** The ordinary loader refuses this two-clock envelope today
(`load_design_sv2` … `REFUSED … Clock:multiple`, protecting the run2 design `X.sem`), so `X.e` is not defined for it,
although the canonical E route instantiates it. The claims are therefore stated for every canonical-E design `E` with
the design's computed facts (`SyFacts`: the instant profile and obligations, the shape of its view, its inputs and
event sources, and the row equations of the mirror). On the master before the loader's refusal returned, every field
was computed from the envelope by the clocked stages (`sv_structure`; `sv_domains`, which reported the domains
`clka: [src]`, `clkb: [s1, s2]` and the ONE crossing: `clkb`'s process reads `src`; `sv_seq_cycle`), and the route
agreed with Icarus Verilog 12.0 on 530 rows; the request that would make `SyFacts sy.e` a theorem again is upstream.

1. **The step claim** (`sy_runs`), over every sequence of instants and data rows keeping the input discipline (any
   interleaving, any ratio, stopped clocks, coincident edges, x and z on a clock): at a rise of `clkb`, `s1` takes
   `src`'s value before the step and `s2` takes `s1`'s; at a rise of `clka`, `src` takes `d`'s; `q` is `s2`.
2. **The synchronizer's invariant** (`sy_sync`): after every step `k`, if the last two rises of `clkb` up to `k` came
   from the samples `t₁ < t₂`, the output `q` is the value `src` had at `t₁` and `s1` the value it had at `t₂`: the
   output is an earlier value of the source register as `clkb`'s edges saw it, two edges late.
3. **A relation between the clocks as a hypothesis** (`sy_lag`): if `clkb` rises in every window of `n` steps
   (`FairWithin`, a fairness hypothesis; the semantics lets `clkb` stop), the output lags `src` by at most `2n` steps.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_multi.sync2_proof

/-- The edge test of §9.4.2 on bit 0: a rise from `a` to `b`. -/
def rise (a b : LVec) : Bool := isPosedge (a.bits[0]?.getD .lx) (b.bits[0]?.getD .lx)

/-- A rise of a signal from one view to the next. -/
def riseAt (s s' : SvState) (n : String) : Bool := isPosedge (s.bit0 n) (s'.bit0 n)

theorem riseAt_eq {s s' : SvState} {n : String} {x y : LVec} (hx : SvState.lookup s n = some x)
    (hy : SvState.lookup s' n = some y) : riseAt s s' n = rise x y := by
  simp only [riseAt, SvState.bit0, hx, hy, rise]

/-- The view of the design, in declaration order. -/
def syView (a b c q s t u : LVec) : SvState :=
  [("clka", a), ("clkb", b), ("d", c), ("q", q), ("src", s), ("s1", t), ("s2", u)]

theorem syView_lookup (a b c q s t u : LVec) : SvState.lookup (syView a b c q s t u) "clka" = some a ∧
    SvState.lookup (syView a b c q s t u) "clkb" = some b ∧ SvState.lookup (syView a b c q s t u) "d" = some c ∧
    SvState.lookup (syView a b c q s t u) "q" = some q ∧ SvState.lookup (syView a b c q s t u) "src" = some s ∧
    SvState.lookup (syView a b c q s t u) "s1" = some t ∧ SvState.lookup (syView a b c q s t u) "s2" = some u := by
  simp [syView, SvState.lookup]

/-- **The design's computed facts** (what the clocked stages compute from the envelope): the instant profile and
obligations, the shape of its view, the inputs a row binds, the event sources, and the row equations of the mirror (at
a rise of `clkb`, `s1` takes `src`'s value before the slot and `s2` takes `s1`'s; at a rise of `clka`, `src` takes
`d`'s applied value; `q` is `s2`). -/
structure SyFacts (E : CoreMemDesign) : Prop where
  prof : E.SeqProfileI
  obl : E.seqOblI = true
  shape : ∀ v, E.ShapeV v ↔ ∃ a b c q s t u : LVec, v = syView a b c q s t u ∧ a.width = 1 ∧ b.width = 1 ∧
    c.width = 1 ∧ q.width = 1 ∧ s.width = 1 ∧ t.width = 1 ∧ u.width = 1
  applied : ∀ r v, E.appliedRow r v = [("clka", appliedIn r v "clka"), ("clkb", appliedIn r v "clkb"),
    ("d", appliedIn r v "d")]
  inputs : E.scalar.toDesign2.inputNames.toList = ["clka", "clkb", "d"]
  wa : E.scalar.toDesign2.declWidth "clka" = some 1
  wb : E.scalar.toDesign2.declWidth "clkb" = some 1
  wd : E.scalar.toDesign2.declWidth "d" = some 1
  sources : E.sources = ["clka", "clkb"]
  events : E.events = [⟨"clka", .posedge⟩, ⟨"clkb", .posedge⟩]
  row : ∀ (a b c q s t u a' b' c' : LVec), a.width = 1 → b.width = 1 → c.width = 1 → q.width = 1 → s.width = 1 →
    t.width = 1 → u.width = 1 → a'.width = 1 → b'.width = 1 → c'.width = 1 → ∀ mv : MemV,
    E.slotV (syView a b c q s t u) mv [("clka", a'), ("clkb", b'), ("d", c')] =
      .ok (syView a' b' c' (if rise b b' then t else u) (if rise a a' then c' else s) (if rise b b' then s else t)
        (if rise b b' then t else u), mv)

/-! ## 1. The step claim, over every sequence of instants -/

/-- **One step of a run** (language level): `s1` and `s2` shift at a rise of `clkb` (reading the values before the
step: `src`'s even when `clka` rises with it), `src` takes `d`'s value before the step at a rise of `clka`, `q` is
`s2`. -/
def SyClaim (tr : List (SvState × MemV)) : Prop :=
  ∀ (k : Nat) (s s' : SvState × MemV), tr[k]? = some s → tr[k + 1]? = some s' →
    SvState.lookup s'.1 "s1" =
        (if riseAt s.1 s'.1 "clkb" then SvState.lookup s.1 "src" else SvState.lookup s.1 "s1") ∧
      SvState.lookup s'.1 "s2" =
        (if riseAt s.1 s'.1 "clkb" then SvState.lookup s.1 "s1" else SvState.lookup s.1 "s2") ∧
      SvState.lookup s'.1 "src" =
        (if riseAt s.1 s'.1 "clka" then SvState.lookup s.1 "d" else SvState.lookup s.1 "src") ∧
      SvState.lookup s'.1 "q" = SvState.lookup s'.1 "s2"

def SyInv (σ : SvState × MemV) : Prop :=
  ∃ a b c q s t u : LVec, σ.1 = syView a b c q s t u ∧ a.width = 1 ∧ b.width = 1 ∧ c.width = 1 ∧ q.width = 1 ∧
    s.width = 1 ∧ t.width = 1 ∧ u.width = 1

def SyStep (σ : SvState × MemV) (r : SvState) (σ' : SvState × MemV) : Prop :=
  SyInv σ ∧ ∃ a b c q s t u : LVec, σ.1 = syView a b c q s t u ∧
    σ'.1 = syView (appliedIn r σ.1 "clka") (appliedIn r σ.1 "clkb") (appliedIn r σ.1 "d")
      (if rise b (appliedIn r σ.1 "clkb") then t else u)
      (if rise a (appliedIn r σ.1 "clka") then appliedIn r σ.1 "d" else s)
      (if rise b (appliedIn r σ.1 "clkb") then s else t)
      (if rise b (appliedIn r σ.1 "clkb") then t else u)

set_option maxHeartbeats 4000000 in
/-- **THE STEP CLAIM, over every sequence of instants** (language level). -/
theorem sy_runs {E : CoreMemDesign} (hF : SyFacts E) : SeqRunsI (.ok E) fun _ tr => SyClaim tr := by
  have hP := hF.prof
  have hO := hF.obl
  have hsh := hF.shape
  have happ := hF.applied
  have hin := hF.inputs
  have hwa := hF.wa
  have hwb := hF.wb
  have hwd := hF.wd
  have hsrc := hF.sources
  have hev := hF.events
  refine SeqRunsI.of_rowEqs rfl hP hO SyInv (fun st hc _ => (hsh _).mp hc.shape) SyStep ?_ ?_
  · rintro ⟨v, mv⟩ r ⟨a, b, c, q, s, t, u, hv, ha, hb, hc, hq, hs, ht, hu⟩ _ hty
    simp only at hv
    subst hv
    have hsv : E.ShapeV (syView a b c q s t u) := (hsh _).mpr ⟨a, b, c, q, s, t, u, rfl, ha, hb, hc, hq, hs, ht, hu⟩
    have look := syView_lookup a b c q s t u
    have w1 := CoreMemDesign.appliedIn_width_row hty (n := "clka") (x := a) (v := syView a b c q s t u)
      (by simp [hin]) hwa look.1 ha
    have w2 := CoreMemDesign.appliedIn_width_row hty (n := "clkb") (x := b) (v := syView a b c q s t u)
      (by simp [hin]) hwb look.2.1 hb
    have w3 := CoreMemDesign.appliedIn_width_row hty (n := "d") (x := c) (v := syView a b c q s t u)
      (by simp [hin]) hwd look.2.2.1 hc
    rw [CoreMemDesign.slotV_applied hP hsv mv r, happ, hF.row a b c q s t u _ _ _ ha hb hc hq hs ht hu w1 w2 w3 mv]
    refine ⟨_, rfl, ⟨_, _, _, _, _, _, _, rfl, w1, w2, w3, ?_, ?_, ?_, ?_⟩,
      ⟨⟨a, b, c, q, s, t, u, rfl, ha, hb, hc, hq, hs, ht, hu⟩, a, b, c, q, s, t, u, rfl, rfl⟩⟩
    all_goals split <;> assumption
  · intro σ rows trs _ _ hsat k s0 s' hk hk1
    obtain ⟨σc, row, -, ⟨⟨hinv, a, b, c, q, s, t, u, hv, hv'⟩, hrow⟩, -, hprev⟩ := RunSatS.get hsat hk1
    have hσc : σc = s0 := hprev s0 (by simpa using hk) (by omega)
    subst hσc
    obtain ⟨v, mv⟩ := σc
    simp only at hv hv' hrow hinv
    subst hv
    obtain ⟨v', mv'⟩ := s'
    simp only at hv'
    subst hv'
    have hsv : E.ShapeV (syView a b c q s t u) := (hsh _).mpr hinv
    have look := syView_lookup a b c q s t u
    have look' := syView_lookup (appliedIn row (syView a b c q s t u) "clka")
      (appliedIn row (syView a b c q s t u) "clkb") (appliedIn row (syView a b c q s t u) "d")
      (if rise b (appliedIn row (syView a b c q s t u) "clkb") then t else u)
      (if rise a (appliedIn row (syView a b c q s t u) "clka") then appliedIn row (syView a b c q s t u) "d" else s)
      (if rise b (appliedIn row (syView a b c q s t u) "clkb") then s else t)
      (if rise b (appliedIn row (syView a b c q s t u) "clkb") then t else u)
    show SvState.lookup (syView _ _ _ _ _ _ _) "s1" = _ ∧ _
    rw [riseAt_eq look.2.1 look'.2.1, riseAt_eq look.1 look'.1, look'.2.2.2.2.2.1, look'.2.2.2.2.2.2,
      look'.2.2.2.2.1, look'.2.2.2.1, look.2.2.2.2.1, look.2.2.2.2.2.1, look.2.2.2.2.2.2, look.2.2.1]
    refine ⟨?_, ?_, ?_, rfl⟩
    · by_cases hr : rise b (appliedIn row (syView a b c q s t u) "clkb") = true
      · rw [if_pos hr, if_pos hr]
      · rw [if_neg hr, if_neg hr]
    · by_cases hr : rise b (appliedIn row (syView a b c q s t u) "clkb") = true
      · rw [if_pos hr, if_pos hr]
      · rw [if_neg hr, if_neg hr]
    · by_cases hr : rise a (appliedIn row (syView a b c q s t u) "clka") = true
      · rw [if_pos hr, if_pos hr]
        have := CoreMemDesign.applied_still hP hsv hrow (e := ⟨"clka", .posedge⟩) (by rw [hev]; simp)
          (by simp [hin]) (by simpa [edgeOf, SvState.bit0, look.1, rise] using hr) (x := "d") (by simp [hin])
          (by rw [hsrc]; simp)
        rw [this, look.2.2.1]
        rfl
      · rw [if_neg hr, if_neg hr]

/-! ## 2. The synchronizer's invariant -/

/-- A signal's value after step `j` of a run (none past its end). -/
def valAt (tr : List (SvState × MemV)) (j : Nat) (n : String) : Option LVec :=
  tr[j]?.bind fun s => SvState.lookup s.1 n

/-- Whether `clkb` rose in step `j + 1` of a run (from the sample after step `j` to the sample after step `j + 1`). -/
def riseB (tr : List (SvState × MemV)) (j : Nat) : Bool :=
  match tr[j]?, tr[j + 1]? with
  | some s, some s' => riseAt s.1 s'.1 "clkb"
  | _, _ => false

/-- The step claim, indexed. -/
theorem SyClaim.step {tr : List (SvState × MemV)} (h : SyClaim tr) {j : Nat} (hj : j + 1 < tr.length) :
    valAt tr (j + 1) "s1" = (if riseB tr j then valAt tr j "src" else valAt tr j "s1") ∧
      valAt tr (j + 1) "s2" = (if riseB tr j then valAt tr j "s1" else valAt tr j "s2") ∧
      valAt tr (j + 1) "q" = valAt tr (j + 1) "s2" := by
  have h0 : tr[j]? = some tr[j] := List.getElem?_eq_getElem (by omega)
  have h1 : tr[j + 1]? = some tr[j + 1] := List.getElem?_eq_getElem hj
  obtain ⟨e1, e2, -, e4⟩ := h j _ _ h0 h1
  simp only [valAt, riseB, h0, h1, Option.bind_some]
  refine ⟨e1, e2, e4⟩

/-- Between two rises of `clkb`, `s1` and `s2` hold. -/
theorem SyClaim.hold {tr : List (SvState × MemV)} (h : SyClaim tr) (n : String) (hn : n = "s1" ∨ n = "s2") :
    ∀ (a m : Nat), a + m < tr.length → (∀ j, a ≤ j → j < a + m → riseB tr j = false) →
      valAt tr (a + m) n = valAt tr a n
  | a, 0, _, _ => rfl
  | a, m + 1, hl, hno => by
      have ih := SyClaim.hold h n hn a m (by omega) (fun j h1 h2 => hno j h1 (by omega))
      have hs := SyClaim.step h (j := a + m) (by omega)
      have hf := hno (a + m) (by omega) (by omega)
      rw [show a + (m + 1) = a + m + 1 by omega]
      rcases hn with rfl | rfl
      · rw [hs.1, hf]; exact ih
      · rw [hs.2.1, hf]; exact ih

/-- **THE SYNCHRONIZER'S INVARIANT** (language level), over every run: if `clkb` last rose in steps `t₁ + 1 < t₂ + 1`
up to step `k` (no rise between them, none after `t₂ + 1` up to `k`), the output `q` after step `k` is the value `src`
had before step `t₁ + 1`, and `s1` the value `src` had before step `t₂ + 1`. -/
def SySync (tr : List (SvState × MemV)) : Prop :=
  ∀ (t₁ t₂ k : Nat), t₁ < t₂ → t₂ < k → k < tr.length → riseB tr t₁ = true → riseB tr t₂ = true →
    (∀ j, t₁ < j → j < t₂ → riseB tr j = false) → (∀ j, t₂ < j → j < k → riseB tr j = false) →
    valAt tr k "q" = valAt tr t₁ "src" ∧ valAt tr k "s1" = valAt tr t₂ "src"

theorem SyClaim.sync {tr : List (SvState × MemV)} (h : SyClaim tr) : SySync tr := by
  intro t₁ t₂ k h12 h2k hk hr1 hr2 hno12 hno2k
  -- s1 after the rise at t₂ is src before it; it holds to k
  have s1t2 : valAt tr (t₂ + 1) "s1" = valAt tr t₂ "src" := by
    have := (SyClaim.step h (j := t₂) (by omega)).1; rw [hr2] at this; exact this
  have s1k : valAt tr k "s1" = valAt tr (t₂ + 1) "s1" := by
    have := SyClaim.hold h "s1" (Or.inl rfl) (t₂ + 1) (k - (t₂ + 1)) (by omega)
      (fun j h1 h2 => hno2k j (by omega) (by omega))
    rwa [show t₂ + 1 + (k - (t₂ + 1)) = k by omega] at this
  -- s1 before the rise at t₂ is src before the rise at t₁
  have s1t1 : valAt tr (t₁ + 1) "s1" = valAt tr t₁ "src" := by
    have := (SyClaim.step h (j := t₁) (by omega)).1; rw [hr1] at this; exact this
  have s1t2' : valAt tr t₂ "s1" = valAt tr (t₁ + 1) "s1" := by
    have := SyClaim.hold h "s1" (Or.inl rfl) (t₁ + 1) (t₂ - (t₁ + 1)) (by omega)
      (fun j h1 h2 => hno12 j (by omega) (by omega))
    rwa [show t₁ + 1 + (t₂ - (t₁ + 1)) = t₂ by omega] at this
  -- s2 after the rise at t₂ is s1 before it; it holds to k; q is s2
  have s2t2 : valAt tr (t₂ + 1) "s2" = valAt tr t₂ "s1" := by
    have := (SyClaim.step h (j := t₂) (by omega)).2.1; rw [hr2] at this; exact this
  have s2k : valAt tr k "s2" = valAt tr (t₂ + 1) "s2" := by
    have := SyClaim.hold h "s2" (Or.inr rfl) (t₂ + 1) (k - (t₂ + 1)) (by omega)
      (fun j h1 h2 => hno2k j (by omega) (by omega))
    rwa [show t₂ + 1 + (k - (t₂ + 1)) = k by omega] at this
  have qk : valAt tr k "q" = valAt tr k "s2" := by
    have := (SyClaim.step h (j := k - 1) (by omega)).2.2
    rwa [show k - 1 + 1 = k by omega] at this
  exact ⟨by rw [qk, s2k, s2t2, s1t2', s1t1], by rw [s1k, s1t2]⟩

/-- **THE SYNCHRONIZER, over every sequence of instants** (LANGUAGE LEVEL: a statement about the SystemVerilog
semantics, not about metastable hardware): in every run of the route, from every coherent state, on every sequence of
instants and data rows keeping the input discipline, the output is the value the source register had two `clkb` edges
ago, as those edges saw it. -/
theorem sy_sync {E : CoreMemDesign} (hF : SyFacts E) : SeqRunsI (.ok E) fun _ tr => SySync tr :=
  SeqRunsI.mono (sy_runs hF) fun _ _ h => SyClaim.sync h

/-! ## 3. A relation between the clocks, as a hypothesis: bounded latency under fairness -/

/-- The last index below `b` (and at least `a`) where `p` holds, when there is one. -/
theorem exists_last {p : Nat → Bool} {a : Nat} : ∀ {b : Nat}, (∃ j, a ≤ j ∧ j < b ∧ p j = true) →
    ∃ j, a ≤ j ∧ j < b ∧ p j = true ∧ ∀ i, j < i → i < b → p i = false
  | 0, ⟨j, _, hj, _⟩ => absurd hj (by omega)
  | b + 1, ⟨j, haj, hjb, hpj⟩ => by
      by_cases hb : p b = true
      · exact ⟨b, by omega, by omega, hb, fun i hi hib => absurd hib (by omega)⟩
      · have hjb' : j < b := by
          rcases Nat.lt_or_ge j b with h | h
          · exact h
          · exact absurd (show j = b by omega ▸ hpj) hb
        obtain ⟨j', ha', hb', hp', hlast⟩ := exists_last ⟨j, haj, hjb', hpj⟩
        refine ⟨j', ha', by omega, hp', fun i hi hib => ?_⟩
        rcases Nat.lt_or_ge i b with h | h
        · exact hlast i hi h
        · rw [show i = b by omega]; simpa using hb

/-- `clkb`'s rise in a step, read on the samples, is the event `posedge clkb` of the step. -/
theorem riseB_iff {E : CoreMemDesign} (hF : SyFacts E) (tr : List (SvState × MemV)) (j : Nat) :
    (⟨"clkb", .posedge⟩ : SeqEvent) ∈ E.stepEvents tr j ↔ riseB tr j = true := by
  unfold CoreMemDesign.stepEvents riseB
  cases tr[j]? <;> cases tr[j + 1]? <;> simp [CoreMemDesign.occurs, hF.events, SeqEvent.occursIn, edgeOf, riseAt]

/-- **THE SYNCHRONIZER'S LATENCY UNDER FAIRNESS** (language level): if `clkb` rises in every window of `n` steps of a
run (a relation between the clocks, a hypothesis: the semantics allows `clkb` to stop), the output after every step
`k > 2n` is the value `src` had at most `2n` steps before. -/
def SyLag (E : CoreMemDesign) (n : Nat) (tr : List (SvState × MemV)) : Prop :=
  E.FairWithin tr ⟨"clkb", .posedge⟩ n → ∀ k, 2 * n < k → k < tr.length →
    ∃ j, k - 2 * n ≤ j ∧ j < k ∧ valAt tr k "q" = valAt tr j "src"

theorem SyClaim.lag {E : CoreMemDesign} (hF : SyFacts E) {tr : List (SvState × MemV)} (h : SyClaim tr) (n : Nat) :
    SyLag E n tr := by
  intro hfair k hk hlen
  -- the last rise below k, in the window [k - n, k)
  obtain ⟨j2, hj2a, hj2b, hj2⟩ := hfair (k - n) (by omega)
  obtain ⟨t₂, h2a, h2b, hr2, hlast2⟩ := exists_last (p := riseB tr) (a := k - n) (b := k)
    ⟨j2, by omega, by omega, (riseB_iff hF tr j2).mp hj2⟩
  -- the last rise below t₂, in the window [t₂ - n, t₂)
  obtain ⟨j1, hj1a, hj1b, hj1⟩ := hfair (t₂ - n) (by omega)
  obtain ⟨t₁, h1a, h1b, hr1, hlast1⟩ := exists_last (p := riseB tr) (a := t₂ - n) (b := t₂)
    ⟨j1, by omega, by omega, (riseB_iff hF tr j1).mp hj1⟩
  obtain ⟨hq, -⟩ := SyClaim.sync h t₁ t₂ k h1b h2b hlen hr1 hr2 (fun j a b => hlast1 j a b)
    (fun j a b => hlast2 j a b)
  exact ⟨t₁, by omega, by omega, hq⟩

/-- **THE SYNCHRONIZER'S LATENCY, over every sequence of instants** (LANGUAGE LEVEL): in every run, IF `clkb` rises in
every window of `n` steps, the output lags the source register by at most `2n` steps. -/
theorem sy_lag {E : CoreMemDesign} (hF : SyFacts E) (n : Nat) : SeqRunsI (.ok E) fun _ tr => SyLag E n tr :=
  SeqRunsI.mono (sy_runs hF) fun _ _ h => SyClaim.lag hF h n

#print axioms sy_runs
#print axioms SyClaim.sync
#print axioms sy_sync
#print axioms sy_lag

end Examples.«system-verilog».seq_multi.sync2_proof
