import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages
import LeanModels.Sv.SeqCycleProduct

/-!
# Two registers on two clocks, over every sequence of instants (the instant view's product case)

The design `Examples/system-verilog/seq_multi/two_reg/two_reg.sv`:

```systemverilog
module two_reg #(parameter int W = 4) (input logic clka, clkb, input logic [W-1:0] da, db,
    output logic [W-1:0] qa, qb);
  always_ff @(posedge clka) qa <= da;
  always_ff @(posedge clkb) qb <= db;
endmodule
```

Its events are `posedge clka` and `posedge clkb`; its two domains read nothing of each other (no crossing). The claims
are over EVERY sequence of instants and data rows under the input discipline: any interleaving, any ratio, stopped
clocks, coincident edges, x and z on a clock.

**What connects these theorems to the envelope.** The ordinary loader refuses this two-clock envelope today
(`load_design_sv2` … `REFUSED … Clock:multiple`: the refusal protects the run2 design `X.sem`, whose cycle cannot
express two clocks), so `X.e` is not defined for it, although the canonical E route instantiates it. The claims are
therefore stated for every canonical-E design `E` with the design's computed facts (`TrFacts`: the instant profile and
obligations, the shape of its view, its inputs and event sources, its two domains, and the row equations of the
mirror). On the master before the loader's refusal returned, every field was computed from the envelope by the
clocked stages (`sv_structure`, `sv_domains`, `sv_seq_cycle`) and the route agreed with Icarus Verilog 12.0 on 530
rows; the request that would make `TrFacts (tr.e W)` a theorem again is upstream (keep `X.e` for designs the run2
design refuses).

1. **The claim** (`tr_runs`): in every run, from every coherent state, on every typed stimulus keeping the input
   discipline, each register is the single-clock register of its own clock: at a rising edge of its clock it takes the
   value its data input had before the edge, otherwise it holds, whatever the other clock does (coincident edges
   included). The discipline is what makes "before the edge" the standard's only answer: in an instant row the data
   does not move.
2. **The product theorem applied** (`tr_comm`, `tr_project`): the two domains own disjoint names and read nothing of
   each other (`CoreMemDesign.Domain`), so a coincident instant of both clocks is the two single-clock instants in
   either order, and on `clka`'s domain every run is the run with `clkb` stopped: `qa`'s single-clock behaviour
   transfers unchanged to every interleaving.
3. **A relation between the clocks as a hypothesis** (`tr_derived`): if `clkb` ticks only together with `clka`
   (`TicksOnlyWith`, a derived clock by assumption; the semantics lets the two clocks move independently), `qb` changes
   only in steps in which `clka` rises.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_multi.two_reg_proof

/-- The edge test of §9.4.2 on bit 0: a rise from `a` to `b`. -/
def rise (a b : LVec) : Bool := isPosedge (a.bits[0]?.getD .lx) (b.bits[0]?.getD .lx)

/-- The view of the design, in declaration order. -/
def trView (ca cb da db qa qb : LVec) : SvState :=
  [("clka", ca), ("clkb", cb), ("da", da), ("db", db), ("qa", qa), ("qb", qb)]

/-- **The design's computed facts** (what the clocked stages compute from the envelope at `W`, `1 ≤ W < 2^30`): the
instant profile and obligations, the shape of its view, the inputs a row binds, the event sources, the two domains
without a crossing, and the row equations of the mirror (one slot on a row binding every input: each register takes
its data input's applied value when its own clock rose, else holds). -/
structure TrFacts (W : Nat) (E : CoreMemDesign) : Prop where
  prof : E.SeqProfileI
  obl : E.seqOblI = true
  shape : ∀ v, E.ShapeV v ↔ ∃ ca cb da db qa qb : LVec, v = trView ca cb da db qa qb ∧ ca.width = 1 ∧
    cb.width = 1 ∧ da.width = W ∧ db.width = W ∧ qa.width = W ∧ qb.width = W
  applied : ∀ r v, E.appliedRow r v = [("clka", appliedIn r v "clka"), ("clkb", appliedIn r v "clkb"),
    ("da", appliedIn r v "da"), ("db", appliedIn r v "db")]
  inputs : E.scalar.toDesign2.inputNames.toList = ["clka", "clkb", "da", "db"]
  wa : E.scalar.toDesign2.declWidth "clka" = some 1
  wb : E.scalar.toDesign2.declWidth "clkb" = some 1
  wda : E.scalar.toDesign2.declWidth "da" = some W
  wdb : E.scalar.toDesign2.declWidth "db" = some W
  sources : E.sources = ["clka", "clkb"]
  events : E.events = [⟨"clka", .posedge⟩, ⟨"clkb", .posedge⟩]
  names : E.scalar.decls.toList.map Decl.name = ["clka", "clkb", "da", "db", "qa", "qb"]
  domA : E.Domain [⟨"clka", .posedge⟩] ["clka", "da", "qa"]
  domB : E.Domain [⟨"clkb", .posedge⟩] ["clkb", "db", "qb"]
  row : ∀ (ca cb da db qa qb ca' cb' da' db' : LVec), ca.width = 1 → cb.width = 1 → da.width = W → db.width = W →
    qa.width = W → qb.width = W → ca'.width = 1 → cb'.width = 1 → da'.width = W → db'.width = W → ∀ mv : MemV,
    E.slotV (trView ca cb da db qa qb) mv [("clka", ca'), ("clkb", cb'), ("da", da'), ("db", db')] =
      .ok (trView ca' cb' da' db' (if rise ca ca' then da' else qa) (if rise cb cb' then db' else qb), mv)

/-! ## 1. The claim, over every sequence of instants -/

/-- A rise of a signal from one view to the next (the edge table of §9.4.2 on bit 0). -/
def riseAt (s s' : SvState) (n : String) : Bool := isPosedge (s.bit0 n) (s'.bit0 n)

/-- **Each register is its own clock's register**: in every step of a run, `qa` takes the value `da` had before the
step when `clka` rose in it, else holds, whatever `clkb` did; `qb` likewise. -/
def TrClaim (tr : List (SvState × MemV)) : Prop :=
  ∀ (k : Nat) (s s' : SvState × MemV), tr[k]? = some s → tr[k + 1]? = some s' →
    SvState.lookup s'.1 "qa" =
        (if riseAt s.1 s'.1 "clka" then SvState.lookup s.1 "da" else SvState.lookup s.1 "qa") ∧
      SvState.lookup s'.1 "qb" =
        (if riseAt s.1 s'.1 "clkb" then SvState.lookup s.1 "db" else SvState.lookup s.1 "qb")

/-- The invariant: the view has the design's shape. -/
def TrInv (W : Nat) (σ : SvState × MemV) : Prop :=
  ∃ ca cb da db qa qb : LVec, σ.1 = trView ca cb da db qa qb ∧ ca.width = 1 ∧ cb.width = 1 ∧ da.width = W ∧
    db.width = W ∧ qa.width = W ∧ qb.width = W

/-- One step of a run: the row equations, from a view of the design's shape, on the values the row applies. -/
def TrStep (W : Nat) (σ : SvState × MemV) (r : SvState) (σ' : SvState × MemV) : Prop :=
  TrInv W σ ∧ ∃ ca cb da db qa qb : LVec, σ.1 = trView ca cb da db qa qb ∧
    σ'.1 = trView (appliedIn r σ.1 "clka") (appliedIn r σ.1 "clkb") (appliedIn r σ.1 "da") (appliedIn r σ.1 "db")
      (if rise ca (appliedIn r σ.1 "clka") then appliedIn r σ.1 "da" else qa)
      (if rise cb (appliedIn r σ.1 "clkb") then appliedIn r σ.1 "db" else qb)

set_option maxHeartbeats 4000000 in
/-- **The row equations, on every row**: from a view of the design's shape, every typed row's slot is `TrStep`. -/
theorem tr_eqs (W : Nat) {E : CoreMemDesign} (hF : TrFacts W E) :
    ∀ (σ : SvState × MemV) (r : SvState), TrInv W σ → r ≠ [] → EntryTyped E.scalar.toDesign2 r →
      ∃ σ', E.slotV σ.1 σ.2 r = .ok σ' ∧ TrInv W σ' ∧ TrStep W σ r σ' := by
  have hP := hF.prof
  have hsh := hF.shape
  have happ := hF.applied
  have hin := hF.inputs
  have hwa := hF.wa
  have hwb := hF.wb
  have hwda := hF.wda
  have hwdb := hF.wdb
  rintro ⟨v, mv⟩ r hinv _ hty
  obtain ⟨ca, cb, da, db, qa, qb, hv, hca, hcb, hda, hdb, hqa, hqb⟩ := hinv
  simp only at hv
  subst hv
  have hs : E.ShapeV (trView ca cb da db qa qb) := (hsh _).mpr ⟨ca, cb, da, db, qa, qb, rfl, hca, hcb, hda, hdb, hqa, hqb⟩
  have hw : ∀ n w x, n ∈ E.scalar.toDesign2.inputNames.toList → E.scalar.toDesign2.declWidth n = some w →
      SvState.lookup (trView ca cb da db qa qb) n = some x → x.width = w →
      (appliedIn r (trView ca cb da db qa qb) n).width = w :=
    fun n w x hn hdw hx hxw => CoreMemDesign.appliedIn_width_row hty hn hdw hx hxw
  have w1 := hw "clka" 1 ca (by simp [hin]) hwa (by simp [trView, SvState.lookup]) hca
  have w2 := hw "clkb" 1 cb (by simp [hin]) hwb (by simp [trView, SvState.lookup]) hcb
  have w3 := hw "da" W da (by simp [hin]) hwda (by simp [trView, SvState.lookup]) hda
  have w4 := hw "db" W db (by simp [hin]) hwdb (by simp [trView, SvState.lookup]) hdb
  rw [CoreMemDesign.slotV_applied hP hs mv r, happ, hF.row ca cb da db qa qb _ _ _ _ hca hcb hda hdb
    hqa hqb w1 w2 w3 w4 mv]
  refine ⟨_, rfl, ⟨_, _, _, _, _, _, rfl, w1, w2, w3, w4, ?_, ?_⟩,
    ⟨⟨ca, cb, da, db, qa, qb, rfl, hca, hcb, hda, hdb, hqa, hqb⟩, ca, cb, da, db, qa, qb, rfl, rfl⟩⟩
  · split <;> assumption
  · split <;> assumption

set_option maxHeartbeats 4000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state, on every sequence of instants and data rows
keeping the input discipline (any interleaving of the two clocks, any ratio, a stopped clock, coincident edges, x and z
on a clock), each register is its own clock's register. -/
theorem tr_runs (W : Nat) {E : CoreMemDesign} (hF : TrFacts W E) : SeqRunsI (.ok E) fun _ tr => TrClaim tr := by
  have hP := hF.prof
  have hO := hF.obl
  have hsh := hF.shape
  have hin := hF.inputs
  have hsrc := hF.sources
  have hev := hF.events
  refine SeqRunsI.of_rowEqs rfl hP hO (TrInv W) (fun st hc _ => ?_) (TrStep W)
    (fun σ r hi hne hty => tr_eqs W hF σ r hi hne hty) ?_
  · obtain ⟨ca, cb, da, db, qa, qb, hv, hw⟩ := (hsh _).mp hc.shape
    exact ⟨ca, cb, da, db, qa, qb, hv, hw⟩
  · intro σ rows trs _ _ hsat k s s' hk hk1
    obtain ⟨σc, d, -, ⟨⟨hinv, ca, cb, da, db, qa, qb, hv, hv'⟩, hrow⟩, -, hprev⟩ := RunSatS.get hsat hk1
    have hσc : σc = s := hprev s (by simpa using hk) (by omega)
    subst hσc
    obtain ⟨v, mv⟩ := σc
    simp only at hv hv' hrow hinv
    subst hv
    obtain ⟨v', mv'⟩ := s'
    simp only at hv'
    subst hv'
    have hs : E.ShapeV (trView ca cb da db qa qb) := (hsh _).mpr (by
      obtain ⟨ca', cb', da', db', qa', qb', hv2, hw⟩ := hinv
      exact ⟨ca', cb', da', db', qa', qb', hv2, hw⟩)
    -- what the row applies, read back from the inputs it applies
    have hap : ∀ n, n ∈ E.scalar.toDesign2.inputNames.toList →
        SvState.lookup (E.applyRow (trView ca cb da db qa qb) d) n =
          some (appliedIn d (trView ca cb da db qa qb) n) :=
      fun n hn => CoreMemDesign.applyRow_appliedRow_lookup hP hs d hn
    have look : ∀ (a b c e f g : LVec), SvState.lookup (trView a b c e f g) "clka" = some a ∧
        SvState.lookup (trView a b c e f g) "clkb" = some b ∧ SvState.lookup (trView a b c e f g) "da" = some c ∧
        SvState.lookup (trView a b c e f g) "db" = some e ∧ SvState.lookup (trView a b c e f g) "qa" = some f ∧
        SvState.lookup (trView a b c e f g) "qb" = some g := by
      intro a b c e f g; simp [trView, SvState.lookup]
    -- in a row where a clock rises, the data did not move (the input discipline)
    have hstill : ∀ (c x : String) (cv xv : LVec), (⟨c, .posedge⟩ : SeqEvent) ∈ E.events → x ∉ E.sources →
        c ∈ E.scalar.toDesign2.inputNames.toList → x ∈ E.scalar.toDesign2.inputNames.toList →
        SvState.lookup (trView ca cb da db qa qb) c = some cv → SvState.lookup (trView ca cb da db qa qb) x = some xv →
        rise cv (appliedIn d (trView ca cb da db qa qb) c) = true → appliedIn d (trView ca cb da db qa qb) x = xv := by
      intro c x cv xv he hn hc hx hcv hxv hr
      have ho : SeqEvent.occursIn ⟨c, .posedge⟩ (trView ca cb da db qa qb)
          (E.applyRow (trView ca cb da db qa qb) d) = true := by
        simp only [SeqEvent.occursIn, edgeOf, SvState.bit0, hap c hc, hcv]
        exact hr
      have h := CoreMemDesign.rowOk_still hrow he ho hn
      rw [hap x hx, hxv] at h
      exact Option.some.inj h
    have riseEq : ∀ (a b c e f g a' b' c' e' f' g' : LVec) (n : String) (x y : LVec),
        SvState.lookup (trView a b c e f g) n = some x → SvState.lookup (trView a' b' c' e' f' g') n = some y →
          riseAt (trView a b c e f g) (trView a' b' c' e' f' g') n = rise x y := by
      intro a b c e f g a' b' c' e' f' g' n x y hx hy
      simp only [riseAt, SvState.bit0, hx, hy, rise]
    show SvState.lookup (trView _ _ _ _ _ _) "qa" = _ ∧ SvState.lookup (trView _ _ _ _ _ _) "qb" = _
    rw [riseEq _ _ _ _ _ _ _ _ _ _ _ _ "clka" _ _ (look ..).1 (look ..).1,
      riseEq _ _ _ _ _ _ _ _ _ _ _ _ "clkb" _ _ (look ..).2.1 (look ..).2.1]
    rw [(look ..).2.2.2.2.1, (look ..).2.2.2.2.2, (look ..).2.2.1, (look ..).2.2.2.1, (look ..).2.2.2.2.1,
      (look ..).2.2.2.2.2]
    have inA : "clka" ∈ E.scalar.toDesign2.inputNames.toList := by rw [hin]; simp
    have inB : "clkb" ∈ E.scalar.toDesign2.inputNames.toList := by rw [hin]; simp
    have inDA : "da" ∈ E.scalar.toDesign2.inputNames.toList := by rw [hin]; simp
    have inDB : "db" ∈ E.scalar.toDesign2.inputNames.toList := by rw [hin]; simp
    refine ⟨?_, ?_⟩
    · by_cases hr : rise ca (appliedIn d (trView ca cb da db qa qb) "clka") = true
      · rw [if_pos hr, if_pos hr, hstill "clka" "da" ca da (by rw [hev]; simp) (by rw [hsrc]; simp) inA inDA
          (look ..).1 (look ..).2.2.1 hr]
      · rw [if_neg hr, if_neg hr]
    · by_cases hr : rise cb (appliedIn d (trView ca cb da db qa qb) "clkb") = true
      · rw [if_pos hr, if_pos hr, hstill "clkb" "db" cb db (by rw [hev]; simp) (by rw [hsrc]; simp) inB inDB
          (look ..).2.1 (look ..).2.2.2.1 hr]
      · rw [if_neg hr, if_neg hr]

/-! ## 2. The product theorem applied: each domain on its own -/

set_option maxHeartbeats 4000000 in
/-- **The product theorem applied: coincident rises commute.** From a settled view, the instant raising both clocks at
once is `clka`'s instant followed by `clkb`'s: the same view and memory view (`CoreMemDesign.tick_comm`). -/
theorem tr_comm (W : Nat) {E : CoreMemDesign} (hF : TrFacts W E) {σ σ1 σA σ2 : SvState × MemV} (hs : E.settleV σ.2 σ.1 = .ok σ.1)
    (h : E.tick (Instant.rise "clka" ++ Instant.rise "clkb") σ = .ok σ1) (ha : E.tick (Instant.rise "clka") σ = .ok σA)
    (hb : E.tick (Instant.rise "clkb") σA = .ok σ2) :
    (∀ x, SvState.lookup σ1.1 x = SvState.lookup σ2.1 x) ∧ σ1.2 = σ2.2 := by
  have hnames := hF.names
  refine CoreMemDesign.tick_comm hF.prof hF.obl hF.domA hF.domB (fun x hx => ?_) hs (by simp [Instant.rise]) (by simp [Instant.rise])
    h ha hb
  rw [hnames] at hx
  simp at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxHeartbeats 4000000 in
/-- **The product theorem applied: a run projects to its domain's run.** On `clka`'s domain, every view-level run is
the run on the same rows with everything but `clka` and `da` dropped (`clkb` stopped, `db` held): `qa` does not see
the other clock at all (`CoreMemDesign.runRV_project`). -/
theorem tr_project (W : Nat) {E : CoreMemDesign} (hF : TrFacts W E) {rows : List SvState} {σ : SvState × MemV} {tr tr' : List (SvState × MemV)}
    (hrun : E.runRV σ rows = .ok tr) (hproj : E.runRV σ (rows.map (projRow ["clka", "da", "qa"])) = .ok tr') :
    tr.length = tr'.length ∧ ∀ (k : Nat) (s s' : SvState × MemV), tr[k]? = some s → tr'[k]? = some s' →
      SvState.lookup s.1 "qa" = SvState.lookup s'.1 "qa" := by
  obtain ⟨hlen, hall⟩ := CoreMemDesign.runRV_project hF.prof hF.domA hrun hproj
  exact ⟨hlen, fun k s s' hk hk' => hall k s s' hk hk' "qa" (by simp)⟩

/-! ## 3. A relation between the clocks, as a hypothesis: a derived clock -/

/-- The event `posedge c` of a step of a run, read on its samples, is a rise of `c` (for the design's two clocks). -/
theorem rise_iff {W : Nat} {E : CoreMemDesign} (hF : TrFacts W E) (tr : List (SvState × MemV)) {k : Nat}
    {s s' : SvState × MemV} (hk : tr[k]? = some s) (hk1 : tr[k + 1]? = some s') (c : String)
    (hc : c = "clka" ∨ c = "clkb") :
    (⟨c, .posedge⟩ : SeqEvent) ∈ E.stepEvents tr k ↔ riseAt s.1 s'.1 c = true := by
  unfold CoreMemDesign.stepEvents
  rw [hk, hk1]
  rcases hc with rfl | rfl <;> simp [CoreMemDesign.occurs, hF.events, SeqEvent.occursIn, edgeOf, riseAt]

/-- **A derived clock, by assumption**: if `clkb` ticks only together with `clka` in a run (`TicksOnlyWith`, a
hypothesis of the claim: the semantics lets the two clocks move independently), `qb` changes only in steps in which
`clka` rises. -/
def TrDerived (E : CoreMemDesign) (tr : List (SvState × MemV)) : Prop :=
  E.TicksOnlyWith tr ⟨"clkb", .posedge⟩ ⟨"clka", .posedge⟩ → ∀ (k : Nat) (s s' : SvState × MemV), tr[k]? = some s →
    tr[k + 1]? = some s' → SvState.lookup s'.1 "qb" ≠ SvState.lookup s.1 "qb" → riseAt s.1 s'.1 "clka" = true

theorem TrClaim.derived {W : Nat} {E : CoreMemDesign} (hF : TrFacts W E) {tr : List (SvState × MemV)}
    (h : TrClaim tr) : TrDerived E tr := by
  intro hrel k s s' hk hk1 hne
  have hb : riseAt s.1 s'.1 "clkb" = true := by
    cases hb : riseAt s.1 s'.1 "clkb" with
    | true => rfl
    | false => exact absurd (by simp [(h k s s' hk hk1).2, hb]) hne
  exact (rise_iff hF tr hk hk1 "clka" (.inl rfl)).mp (hrel k ((rise_iff hF tr hk hk1 "clkb" (.inr rfl)).mpr hb))

/-- **A derived clock, over every sequence of instants**: in every run, IF `clkb` ticks only together with `clka`,
`qb` changes only in steps in which `clka` rises. -/
theorem tr_derived (W : Nat) {E : CoreMemDesign} (hF : TrFacts W E) : SeqRunsI (.ok E) fun _ tr => TrDerived E tr :=
  SeqRunsI.mono (tr_runs W hF) fun _ _ h => TrClaim.derived hF h

#print axioms tr_eqs
#print axioms tr_runs
#print axioms tr_comm
#print axioms tr_project
#print axioms tr_derived

end Examples.«system-verilog».seq_multi.two_reg_proof
