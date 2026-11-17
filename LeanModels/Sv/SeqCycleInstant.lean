import LeanModels.Sv.SeqCycleRuns

/-!
# The instant view of the ordinary E route (`LeanModels.Sv.Kernel`, the clocked tactics' theory)

**Status: derived from the ordinary E route.** One definition: the route's run (`runCoreMemRows`, the event-based slot
semantics). One derived view on it, indexed by the design's events: the instant function `tick` (`SeqCycle.lean`), the
mirror's slot on an instant's row. Single clock is that view at the one event `posedge clk` (`cycleMV` is a data row
then `tick (Instant.rise clk)` by definition); nothing here is special to one clock.

* `runRows_slots`: the route's run of EVERY list of typed rows (any clocks, either edge, any interleaving) lands on the
  fold of the mirror's slot (`runRV`), under the obligations. The input discipline is not needed for the refinement.
* `runRows_instants`, **THE REFINEMENT, any number of events**: under the input discipline (`Separated`) the route's run
  is the fold of `tick` over the instants, interleaved with the data rows (`runI`): each instant row IS its instant
  (`slotV_instOf`), read from the view before it.
* `SeqRunsI.intro`, `SeqRunsI.of_rowEqs`: how a claim over every sequence of instants is proved (an invariant, the
  slot's per-row equations, the claim from a run whose rows each carry their discipline fact).
* `SeqProfile.separated_cycleRows`, `SeqRunsM_iff`: on a design whose only event is `posedge clk` every cycle stimulus
  keeps the discipline, so the single-clock judgment means what it meant (over every typed data list).
* `eventTrace`, `TicksOnlyWith`, `FairWithin`: relations between clocks, as hypotheses of a claim (a derived or
  divided clock by assumption; a bounded fairness), never part of the semantics.

Why the discipline (IEEE 1800-2023 §4.7, §9.4.2): the route applies a row's inputs first, then runs the processes whose
events occurred. That is the standard's only resolution exactly when no process woken in the slot reads a signal the
row moves, other than the reset that woke it. The discipline gives that: no process wakes in a data row; an instant row
moves only event sources, no process reads an event source as data except its own reset (`oblNoSourceRead`), and no
process sees its clock event while its reset moves (`ResetStill`). Outside the discipline a design still has a meaning
(the route's run, `runRows_slots`); a claim about it is then about the route's resolution, not the standard's.

Theorems about a design with a read across domains are LANGUAGE-LEVEL: they describe the SystemVerilog semantics (a
crossing read sees the source's committed value, old or new by §10.4.2), not hardware (metastability is not modelled).
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## A slot changes only what the processes drive -/

/-- A settle pass changes only the continuous assigns' targets (on the materialized view). -/
theorem CoreMemDesign.settleV_frame {E : CoreMemDesign} {mv : MemV} {w w' : SvState} (h : E.settleV mv w = .ok w')
    {x : String} (hx : x ∉ assignTargets E.processes.toList) : SvState.lookup w' x = SvState.lookup (E.matV w) x := by
  simp only [CoreMemDesign.settleV, Res.bind_eq_ok, Res.ok.injEq] at h
  obtain ⟨raw, hr, rfl⟩ := h
  exact CoreMemDesign.lookup_matV_congr (CoreMemDesign.settleRaw_frame _ _ _ _ hr x hx)

/-- The inputs a typed row applies to a coherent state's view are a materialized view. -/
theorem CoreMemDesign.matV_applyRow {E : CoreMemDesign} (hP : E.SeqProfileI) {st : CoreMemState}
    (hc : E.Coherent st) {r : SvState} (hty : EntryTyped E.scalar.toDesign2 r) :
    E.matV (applyInputs2 E.scalar.toDesign2 r (E.scalar.view st.scalar)) =
      applyInputs2 E.scalar.toDesign2 r (E.scalar.view st.scalar) := by
  rw [← Elab.view_applyInputs hP.names hP.four hc.typed hty]
  exact CoreMemDesign.matV_view hP.names hP.four (hc.typed.applyInputs r)

/-- **A slot keeps every name no process drives at the value the row applied**: the inputs (clocks, resets, data) of the
view after a slot are the row's. -/
theorem CoreMemDesign.slotV_undriven {E : CoreMemDesign} (hP : E.SeqProfileI) {st : CoreMemState}
    (hc : E.Coherent st) {r : SvState} (hty : EntryTyped E.scalar.toDesign2 r) {mv mv' : MemV} {v' : SvState}
    (hs : E.slotV (E.scalar.view st.scalar) mv r = .ok (v', mv')) :
    ∀ n, n ∉ E.driven → SvState.lookup v' n = SvState.lookup (E.applyRow (E.scalar.view st.scalar) r) n := by
  intro n hn
  have hna : n ∉ assignTargets E.processes.toList := fun h' => hn (CoreMemDesign.assignTargets_driven n h')
  simp only [CoreMemDesign.slotV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hs
  obtain ⟨p0, h0, p, h1, rr, hq, s1, h2, s2, h3, rfl, -⟩ := hs
  have hp := CoreMemDesign.matV_settleV hP.names hP.four h1
  rw [CoreMemDesign.round_frame hP hp hq h2 h3 n hn, CoreMemDesign.settleV_frame h1 hna,
    CoreMemDesign.matV_settleV hP.names hP.four h0, CoreMemDesign.settleV_frame h0 hna,
    CoreMemDesign.matV_applyRow hP hc hty]
  rfl

/-! ## The discipline reads only what no process drives -/

/-- What `applyRow` does to one name, on 4-state inputs: an input takes the row's value if the row binds it. -/
theorem CoreMemDesign.lookup_applyRow {E : CoreMemDesign} (h4 : AllFour E.scalar) (v r : SvState) (n : String) :
    SvState.lookup (E.applyRow v r) n =
      if n ∈ E.scalar.toDesign2.inputNames.toList then (SvState.lookup r n).or (SvState.lookup v n)
      else SvState.lookup v n :=
  lookup_applyInputs2 _ r v n fun dc hdc _ => h4 dc (by simpa [Elab.toDesign2] using hdc)

/-- A driven name is not an input port (the obligations). -/
theorem CoreMemDesign.driven_not_input {E : CoreMemDesign} (hO : E.seqOblI = true) {n : String}
    (hn : n ∈ E.driven) : n ∉ E.scalar.toDesign2.inputNames.toList := by
  intro hin
  have h := (CoreMemDesign.seqOblI_spec hO).2.2.1
  simp only [CoreMemDesign.oblInputsUndriven, List.all_eq_true, Bool.not_eq_true', List.contains_eq_any_beq,
    List.any_eq_false, beq_iff_eq] at h
  refine h n hn n ?_ rfl
  simpa [CoreMemDesign.inputNamesL, Design2.inputNames, Elab.toDesign2] using hin

/-- Two views that agree off the driven names apply a row to views that agree off the driven names. -/
theorem CoreMemDesign.applyRow_agree {E : CoreMemDesign} (h4 : AllFour E.scalar) {v v' : SvState}
    (h : ∀ n, n ∉ E.driven → SvState.lookup v n = SvState.lookup v' n) (r : SvState) :
    ∀ n, n ∉ E.driven → SvState.lookup (E.applyRow v r) n = SvState.lookup (E.applyRow v' r) n := by
  intro n hn
  rw [CoreMemDesign.lookup_applyRow h4, CoreMemDesign.lookup_applyRow h4, h n hn]

/-- Bit 0 of a name, from its lookup. -/
theorem SvState.bit0_congr {a b : SvState} {n : String} (h : SvState.lookup a n = SvState.lookup b n) :
    a.bit0 n = b.bit0 n := by
  simp only [SvState.bit0, h]

/-- The events that occur depend only on the event sources. -/
theorem CoreMemDesign.occurs_congr {E : CoreMemDesign} (hO : E.seqOblI = true) {a a' b b' : SvState}
    (ha : ∀ n, n ∉ E.driven → SvState.lookup a n = SvState.lookup a' n)
    (hb : ∀ n, n ∉ E.driven → SvState.lookup b n = SvState.lookup b' n) : E.occurs a b = E.occurs a' b' := by
  unfold CoreMemDesign.occurs
  apply List.filter_congr
  intro e he
  have hs : e.src ∈ E.sources := List.mem_map_of_mem he
  have hu := CoreMemDesign.source_undriven hO hs
  simp only [SeqEvent.occursIn, SvState.bit0_congr (ha _ hu), SvState.bit0_congr (hb _ hu)]

/-- **The row discipline depends only on what no process drives** (inputs: clocks, resets, data). -/
theorem CoreMemDesign.rowOk_congr {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true) {v v' : SvState}
    (h : ∀ n, n ∉ E.driven → SvState.lookup v n = SvState.lookup v' n) {r : SvState}
    (hr : E.DataRow v r ∨ E.InstantRow v r) : E.DataRow v' r ∨ E.InstantRow v' r := by
  have hap := CoreMemDesign.applyRow_agree hP.four h r
  have hocc := CoreMemDesign.occurs_congr hO h hap
  rcases hr with hd | ⟨hne, hmove, hrst⟩
  · left; unfold CoreMemDesign.DataRow at hd ⊢; rw [← hocc]; exact hd
  · right
    refine ⟨by rw [← hocc]; exact hne, fun n hn => ?_, fun f hf hck rr hrr => ?_⟩
    · by_cases hd : n ∈ E.driven
      · have hni := CoreMemDesign.driven_not_input hO hd
        rw [CoreMemDesign.lookup_applyRow hP.four, if_neg hni]
      · rw [← hap n hd, ← h n hd]; exact hmove n hn
    · have hs := CoreMemDesign.reset_mem_sources hf hrr
      have hu := CoreMemDesign.source_undriven hO hs
      have hc := CoreMemDesign.clock_mem_sources hf
      have hcu := CoreMemDesign.source_undriven hO hc
      have hck' : f.clockEvent.occursIn v (E.applyRow v r) = true := by
        simpa only [SeqEvent.occursIn, CoreMemEdge.clockEvent, SvState.bit0_congr (h _ hcu),
          SvState.bit0_congr (hap _ hcu)] using hck
      rw [← hap rr hu, ← h rr hu]
      exact hrst f hf hck' rr hrr

/-- **The discipline of a run depends only on what no process drives.** -/
theorem CoreMemDesign.separated_congr {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true) :
    ∀ (rows : List SvState) {v v' : SvState}, (∀ n, n ∉ E.driven → SvState.lookup v n = SvState.lookup v' n) →
      E.Separated v rows → E.Separated v' rows
  | [], _, _, _, _ => trivial
  | r :: rs, v, v', h, ⟨hr, hrs⟩ =>
      ⟨CoreMemDesign.rowOk_congr hP hO h hr,
        CoreMemDesign.separated_congr hP hO rs (CoreMemDesign.applyRow_agree hP.four h r) hrs⟩

/-! ## An instant row IS its instant -/

/-- The moves of an instant, looked up: a source in the list with a move has the move's one-bit value. -/
theorem lookup_movesRow (g : String → Option Logic) :
    ∀ (ss : List String) (n : String),
      SvState.lookup (Instant.row (ss.filterMap fun s => (g s).map fun l => (s, l))) n =
        if n ∈ ss then (g n).map fun l => (⟨#[l]⟩ : LVec) else none
  | [], n => by simp [Instant.row, SvState.lookup]
  | s :: ss, n => by
      cases hg : g s with
      | none =>
          rw [List.filterMap_cons, hg]
          simp only [Option.map_none]
          rw [lookup_movesRow g ss n]
          by_cases hsn : s = n
          · subst hsn; simp [hg]
          · simp [List.mem_cons, Ne.symm hsn]
      | some l =>
          rw [List.filterMap_cons, hg]
          simp only [Option.map_some, Instant.row, List.map_cons, SvState.lookup]
          by_cases hsn : s = n
          · subst hsn; simp [hg]
          · have : (s == n) = false := by simpa using hsn
            simp only [this, Bool.false_eq_true, ↓reduceIte]
            have ih := lookup_movesRow g ss n
            simp only [Instant.row] at ih
            rw [ih]
            simp [List.mem_cons, Ne.symm hsn]

/-- `instOf` as a list of moves. -/
theorem CoreMemDesign.instOf_eq (E : CoreMemDesign) (v r : SvState) :
    E.instOf v r = E.sources.eraseDups.filterMap fun s =>
      (if SvState.lookup (E.applyRow v r) s = SvState.lookup v s then none else some ((E.applyRow v r).bit0 s)).map
        fun l => (s, l) := by
  unfold CoreMemDesign.instOf
  congr 1
  funext s
  split <;> rfl

/-- A one-bit value is its bit 0. -/
theorem LVec.eq_bit0 {x : LVec} (h : x.width = 1) : (⟨#[x.bits[0]?.getD .lx]⟩ : LVec) = x := by
  rcases x with ⟨⟨_ | ⟨a, _ | ⟨b, l⟩⟩⟩⟩ <;> simp_all [LVec.width]

private theorem find_name_of_nodup : ∀ {l : List Decl}, (l.map Decl.name).Nodup → ∀ {dc : Decl}, dc ∈ l →
    l.find? (fun d => d.name == dc.name) = some dc
  | [], _, _, h => by simp at h
  | d :: l, hnd, dc, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have hne : (d.name == dc.name) = false := by
          simpa using fun he => hnd.1 dc h he.symm
        simp [List.find?_cons, hne, find_name_of_nodup hnd.2 h]

/-- An input port's declared width. -/
theorem CoreMemDesign.declWidth_of_port {E : CoreMemDesign} (hP : E.SeqProfileI) {s : String} {w : Nat}
    (h : (s, w) ∈ E.inputPorts) : E.scalar.toDesign2.declWidth s = some w := by
  simp only [CoreMemDesign.inputPorts, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨dc, hdc, -, rfl, rfl⟩ := h
  simp only [Design2.declWidth, Elab.toDesign2]
  rw [find_name_of_nodup hP.names hdc]
  rfl

/-- **An instant row applies the inputs of its instant**: on a view with every declaration, a typed instant row and the
row of the instant it makes apply the same inputs. -/
theorem CoreMemDesign.applyRow_instOf {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    {v r : SvState} (hv : E.ShapeV v) (hty : EntryTyped E.scalar.toDesign2 r)
    (hmove : ∀ n, n ∉ E.sources → SvState.lookup (E.applyRow v r) n = SvState.lookup v n) :
    E.applyRow v (E.instOf v r).row = E.applyRow v r := by
  have h4' : ∀ dc ∈ E.scalar.toDesign2.decls.toList, dc.isInput = true → dc.twoState = false :=
    fun dc hdc _ => hP.four dc (by simpa [Elab.toDesign2] using hdc)
  have hkeys : ∀ n ∈ E.scalar.toDesign2.inputNames.toList, n ∈ v.map Prod.fst := by
    intro n hn
    rw [hv.1]
    obtain ⟨dc, hdc, -, rfl⟩ : ∃ dc ∈ E.scalar.decls.toList, dc.isInput = true ∧ dc.name = n := by
      simpa [Design2.inputNames, Elab.toDesign2] using hn
    exact List.mem_map_of_mem (f := Decl.name) hdc
  apply SvState.ext
  · unfold CoreMemDesign.applyRow
    rw [keys_applyInputs2 _ _ h4' hkeys, keys_applyInputs2 _ _ h4' hkeys]
  · unfold CoreMemDesign.applyRow
    rw [keys_applyInputs2 _ _ h4' hkeys, hv.1]; exact hP.names
  · intro n
    rw [CoreMemDesign.instOf_eq, CoreMemDesign.lookup_applyRow hP.four v _ n,
      CoreMemDesign.lookup_applyRow hP.four v r n, lookup_movesRow]
    by_cases hin : n ∈ E.scalar.toDesign2.inputNames.toList
    · simp only [hin, ↓reduceIte]
      by_cases hs : n ∈ E.sources
      · have hse : n ∈ E.sources.eraseDups := List.mem_eraseDups.mpr hs
        simp only [hse, ↓reduceIte]
        by_cases hm : SvState.lookup (E.applyRow v r) n = SvState.lookup v n
        · simp only [hm, ↓reduceIte, Option.map_none, Option.none_or]
          rw [CoreMemDesign.lookup_applyRow hP.four, if_pos hin] at hm
          exact hm.symm
        · simp only [hm, ↓reduceIte, Option.map_some, Option.some_or]
          have hm' := hm
          rw [CoreMemDesign.lookup_applyRow hP.four, if_pos hin] at hm'
          cases hr : SvState.lookup r n with
          | none => simp [hr] at hm'
          | some x =>
              have hw : x.width = 1 := by
                have := hty n x hin hr
                rw [CoreMemDesign.declWidth_of_port hP (CoreMemDesign.source_port hO hs)] at this
                exact (Option.some.inj this).symm
              have hap : SvState.lookup (E.applyRow v r) n = some x := by
                rw [CoreMemDesign.lookup_applyRow hP.four, if_pos hin, hr]; rfl
              simp only [Option.some_or, SvState.bit0, hap]
              exact congrArg some (LVec.eq_bit0 hw)
      · have hse : n ∉ E.sources.eraseDups := fun h' => hs (List.mem_eraseDups.mp h')
        simp only [hse, ↓reduceIte, Option.none_or]
        have := hmove n hs
        rw [CoreMemDesign.lookup_applyRow hP.four, if_pos hin] at this
        exact this.symm
    · simp only [hin, ↓reduceIte]

/-- **AN INSTANT ROW IS ITS INSTANT**: on a view with every declaration, the slot on a typed instant row is the instant
function at the instant the row makes. -/
theorem CoreMemDesign.slotV_instOf {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    {σ : SvState × MemV} {r : SvState} (hv : E.ShapeV σ.1) (hty : EntryTyped E.scalar.toDesign2 r)
    (hi : E.InstantRow σ.1 r) : E.tick (E.instOf σ.1 r) σ = E.slotV σ.1 σ.2 r := by
  have h := CoreMemDesign.applyRow_instOf hP hO hv hty hi.2.1
  unfold CoreMemDesign.applyRow at h
  simp only [CoreMemDesign.tick, CoreMemDesign.slotV, h]

/-! ## The runs: the route's run is the fold of the slot, and of the instant function -/

/-- The view-level run of a row list: one sample per row, the mirror's slot. -/
def CoreMemDesign.runRV (E : CoreMemDesign) : SvState × MemV → List SvState → Res (List (SvState × MemV))
  | _, [] => .ok []
  | σ, r :: rs => do
      let σ' ← E.slotV σ.1 σ.2 r
      let rest ← E.runRV σ' rs
      .ok (σ' :: rest)

/-- The step of the instant view on one row, from the state before it: the data row's slot when no event occurs, else
the instant function at the row's instant. -/
def CoreMemDesign.stepI (E : CoreMemDesign) (σ : SvState × MemV) (r : SvState) : Res (SvState × MemV) :=
  if (E.occurs σ.1 (E.applyRow σ.1 r)).isEmpty then E.dataV σ r else E.tick (E.instOf σ.1 r) σ

/-- **The run of the instant view**: `tick` folded over the instants, interleaved with the data rows. -/
def CoreMemDesign.runI (E : CoreMemDesign) : SvState × MemV → List SvState → Res (List (SvState × MemV))
  | _, [] => .ok []
  | σ, r :: rs => do
      let σ' ← E.stepI σ r
      let rest ← E.runI σ' rs
      .ok (σ' :: rest)

/-- A nonempty row, as the route's run reads it. -/
theorem SvState.isEmpty_of_ne {r : SvState} (h : r ≠ []) : r.isEmpty = false := by
  cases r with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- **THE RUN REFINEMENT, every row list**: under the obligations, from every coherent state with a coherent memory, for
every list of nonempty typed rows (any clocks, either edge, any interleaving: the input discipline is not needed),
when the view-level run succeeds the route's run succeeds and its samples are exactly the view-level run's. -/
theorem CoreMemDesign.runRows_slots {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true) :
    ∀ (rows : List SvState) (st : CoreMemState) (tr : List (SvState × MemV)), E.Coherent st →
      E.MemCoherent st.memory → (∀ r ∈ rows, r ≠ [] ∧ EntryTyped E.scalar.toDesign2 r) →
      E.runRV (E.scalar.view st.scalar, E.memOf st.memory) rows = .ok tr →
      ∃ outs, runCoreMemRows E st rows = .ok outs ∧
        outs.map (fun s => (E.scalar.view s.scalar, E.memOf s.memory)) = tr
  | [], st, tr, _, _, _, hv => by
      simp only [CoreMemDesign.runRV, Res.ok.injEq] at hv
      subst hv
      exact ⟨[], rfl, rfl⟩
  | r :: rs, st, tr, hc, hmc, hty, hv => by
      simp only [CoreMemDesign.runRV, Res.bind_eq_ok, Res.ok.injEq] at hv
      obtain ⟨⟨v1, m1⟩, h1, rest, hrest, rfl⟩ := hv
      have hr := hty r (by simp)
      obtain ⟨st1, hs1, hv1, hm1, hc1, hmc1⟩ := CoreMemDesign.step_seqI hP hO hc hmc hr.2 h1
      obtain ⟨outs, ho, hmap⟩ := CoreMemDesign.runRows_slots hP hO rs st1 rest hc1 hmc1
        (fun r' h' => hty r' (by simp [h'])) (by rw [hv1, hm1]; exact hrest)
      refine ⟨st1 :: outs, ?_, by simp [hv1, hm1, hmap]⟩
      rw [runCoreMemRows_cons (SvState.isEmpty_of_ne hr.1), hs1]
      simp [ho]

#print axioms CoreMemDesign.runRows_slots

/-- The instant view's step is the slot, on a row of the discipline, from a coherent state's view. -/
theorem CoreMemDesign.stepI_eq {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    {σ : SvState × MemV} {r : SvState} (hv : E.ShapeV σ.1) (hty : EntryTyped E.scalar.toDesign2 r)
    (hr : E.DataRow σ.1 r ∨ E.InstantRow σ.1 r) : E.stepI σ r = E.slotV σ.1 σ.2 r := by
  unfold CoreMemDesign.stepI
  rcases hr with hd | hi
  · unfold CoreMemDesign.DataRow at hd
    simp [hd, CoreMemDesign.dataV]
  · have hne : (E.occurs σ.1 (E.applyRow σ.1 r)).isEmpty = false := by
      cases h : E.occurs σ.1 (E.applyRow σ.1 r) with
      | nil => exact absurd h hi.1
      | cons _ _ => rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact CoreMemDesign.slotV_instOf hP hO hv hty hi

/-- **THE REFINEMENT, any number of events**: under the input discipline and the obligations, from every coherent state
with a coherent memory, for every list of nonempty typed rows, when the instant view's run (`tick` folded over the
instants, interleaved with the data rows) succeeds the route's run succeeds and its samples are exactly the instant
view's. -/
theorem CoreMemDesign.runRows_instants {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true) :
    ∀ (rows : List SvState) (st : CoreMemState) (tr : List (SvState × MemV)), E.Coherent st →
      E.MemCoherent st.memory → (∀ r ∈ rows, r ≠ [] ∧ EntryTyped E.scalar.toDesign2 r) →
      E.Separated (E.scalar.view st.scalar) rows →
      E.runI (E.scalar.view st.scalar, E.memOf st.memory) rows = .ok tr →
      ∃ outs, runCoreMemRows E st rows = .ok outs ∧
        outs.map (fun s => (E.scalar.view s.scalar, E.memOf s.memory)) = tr
  | [], st, tr, _, _, _, _, hv => by
      simp only [CoreMemDesign.runI, Res.ok.injEq] at hv
      subst hv
      exact ⟨[], rfl, rfl⟩
  | r :: rs, st, tr, hc, hmc, hty, ⟨hrow, hsep⟩, hv => by
      simp only [CoreMemDesign.runI, Res.bind_eq_ok, Res.ok.injEq] at hv
      obtain ⟨⟨v1, m1⟩, h1, rest, hrest, rfl⟩ := hv
      have hr := hty r (by simp)
      rw [CoreMemDesign.stepI_eq hP hO hc.shape hr.2 hrow] at h1
      obtain ⟨st1, hs1, hv1, hm1, hc1, hmc1⟩ := CoreMemDesign.step_seqI hP hO hc hmc hr.2 h1
      have hag : ∀ n, n ∉ E.driven →
          SvState.lookup (E.applyRow (E.scalar.view st.scalar) r) n = SvState.lookup (E.scalar.view st1.scalar) n :=
        fun n hn => by rw [hv1, CoreMemDesign.slotV_undriven hP hc hr.2 h1 n hn]
      obtain ⟨outs, ho, hmap⟩ := CoreMemDesign.runRows_instants hP hO rs st1 rest hc1 hmc1
        (fun r' h' => hty r' (by simp [h'])) (CoreMemDesign.separated_congr hP hO rs hag hsep)
        (by rw [hv1, hm1]; exact hrest)
      refine ⟨st1 :: outs, ?_, by simp [hv1, hm1, hmap]⟩
      rw [runCoreMemRows_cons (SvState.isEmpty_of_ne hr.1), hs1]
      simp [ho]

#print axioms CoreMemDesign.runRows_instants

/-! ## The judgment over every sequence of instants: how a claim is proved -/

/-- **How a `SeqRunsI` claim is proved from per-row equations**: the instant profile and obligations, an invariant every
coherent state's views have, the slot's per-row equations as a relation `Step σ row σ'` (the slot exists from the
invariant, keeps it, satisfies `Step`), and the claim about every run whose samples satisfy `Step` row by row, each row
carrying its discipline fact (a data row or an instant row, from the view before it). -/
theorem SeqRunsI.of_rowEqs {r : Res CoreMemDesign} {E : CoreMemDesign}
    {P : List SvState → List (SvState × MemV) → Prop} (hr : r = .ok E) (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    (Inv : SvState × MemV → Prop)
    (hinv : ∀ st, E.Coherent st → E.MemCoherent st.memory → Inv (E.scalar.view st.scalar, E.memOf st.memory))
    (Step : SvState × MemV → SvState → SvState × MemV → Prop)
    (heqs : ∀ σ row, Inv σ → row ≠ [] → EntryTyped E.scalar.toDesign2 row →
      ∃ σ', E.slotV σ.1 σ.2 row = .ok σ' ∧ Inv σ' ∧ Step σ row σ')
    (hrun : ∀ σ rows tr, Inv σ → (∀ row ∈ rows, row ≠ [] ∧ EntryTyped E.scalar.toDesign2 row) →
      RunSatS (fun σ row σ' => Step σ row σ' ∧ (E.DataRow σ.1 row ∨ E.InstantRow σ.1 row)) id σ rows tr → P rows tr) :
    SeqRunsI r P := by
  refine ⟨E, hr, fun st rows hc hmc hty hsep => ?_⟩
  -- the run from a coherent state: the slots, their equations and the discipline, row by row
  have key : ∀ (rows : List SvState) (st : CoreMemState), E.Coherent st → E.MemCoherent st.memory →
      Inv (E.scalar.view st.scalar, E.memOf st.memory) → (∀ row ∈ rows, row ≠ [] ∧ EntryTyped E.scalar.toDesign2 row) →
      E.Separated (E.scalar.view st.scalar) rows →
      ∃ outs, runCoreMemRows E st rows = .ok outs ∧
        RunSatS (fun σ row σ' => Step σ row σ' ∧ (E.DataRow σ.1 row ∨ E.InstantRow σ.1 row)) id
          (E.scalar.view st.scalar, E.memOf st.memory) rows
          (outs.map fun s => (E.scalar.view s.scalar, E.memOf s.memory)) := by
    intro rows
    induction rows with
    | nil => intro st _ _ _ _ _; exact ⟨[], rfl, rfl⟩
    | cons row rs ih =>
        intro st hc hmc hi hty ⟨hrow, hsep⟩
        have hr := hty row (by simp)
        obtain ⟨⟨v1, m1⟩, h1, hi1, hs⟩ := heqs _ row hi hr.1 hr.2
        obtain ⟨st1, hs1, hv1, hm1, hc1, hmc1⟩ := CoreMemDesign.step_seqI hP hO hc hmc hr.2 h1
        have hag : ∀ n, n ∉ E.driven →
            SvState.lookup (E.applyRow (E.scalar.view st.scalar) row) n =
              SvState.lookup (E.scalar.view st1.scalar) n :=
          fun n hn => by rw [hv1, CoreMemDesign.slotV_undriven hP hc hr.2 h1 n hn]
        obtain ⟨outs, ho, hsat⟩ := ih st1 hc1 hmc1 (by rw [hv1, hm1]; exact hi1)
          (fun r' h' => hty r' (by simp [h'])) (CoreMemDesign.separated_congr hP hO rs hag hsep)
        refine ⟨st1 :: outs, ?_, ⟨(v1, m1), outs.map fun s => (E.scalar.view s.scalar, E.memOf s.memory),
          by simp [hv1, hm1], ⟨hs, hrow⟩, ?_⟩⟩
        · rw [runCoreMemRows_cons (SvState.isEmpty_of_ne hr.1), hs1]
          simp [ho]
        · show RunSatS _ id (v1, m1) rs _
          rw [← hv1, ← hm1]
          exact hsat
  obtain ⟨outs, ho, hsat⟩ := key rows st hc hmc (hinv st hc hmc) hty hsep
  exact ⟨outs, ho, hrun _ rows _ (hinv st hc hmc) hty hsat⟩

#print axioms SeqRunsI.of_rowEqs

/-- **How a `SeqRunsI` claim is proved**: an invariant the slot keeps on every row, and the claim about every view-level
run from it (each row carrying its discipline fact). -/
theorem SeqRunsI.intro {r : Res CoreMemDesign} {E : CoreMemDesign}
    {P : List SvState → List (SvState × MemV) → Prop} (hr : r = .ok E) (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    (Inv : SvState × MemV → Prop)
    (hinv : ∀ st, E.Coherent st → E.MemCoherent st.memory → Inv (E.scalar.view st.scalar, E.memOf st.memory))
    (hstep : ∀ σ row, Inv σ → row ≠ [] → EntryTyped E.scalar.toDesign2 row →
      ∃ σ', E.slotV σ.1 σ.2 row = .ok σ' ∧ Inv σ')
    (hrun : ∀ σ rows tr, Inv σ → (∀ row ∈ rows, row ≠ [] ∧ EntryTyped E.scalar.toDesign2 row) →
      RunSatS (fun σ row σ' => E.slotV σ.1 σ.2 row = .ok σ' ∧ (E.DataRow σ.1 row ∨ E.InstantRow σ.1 row)) id σ rows tr →
      P rows tr) :
    SeqRunsI r P :=
  SeqRunsI.of_rowEqs hr hP hO Inv hinv (fun σ row σ' => E.slotV σ.1 σ.2 row = .ok σ')
    (fun σ row hi hne hty => by obtain ⟨σ', h1, h2⟩ := hstep σ row hi hne hty; exact ⟨σ', h1, h2, h1⟩) hrun

/-- A claim over every sequence of instants implies every weaker claim. -/
theorem SeqRunsI.mono {r : Res CoreMemDesign} {P Q : List SvState → List (SvState × MemV) → Prop}
    (h : SeqRunsI r P) (hPQ : ∀ rows tr, P rows tr → Q rows tr) : SeqRunsI r Q := by
  obtain ⟨E, hr, hall⟩ := h
  exact ⟨E, hr, fun st rows hc hmc hty hs => by
    obtain ⟨outs, ho, hp⟩ := hall st rows hc hmc hty hs
    exact ⟨outs, ho, hPQ _ _ hp⟩⟩

/-! ## Single clock is the one-event instance -/

/-- **On a design whose only event is `posedge clk`, every cycle stimulus keeps the input discipline**, from every view:
the low slot is a data row (the clock goes to 0: no rise), the high slot a data row or the instant `{posedge clk}`. -/
theorem CoreMemDesign.SeqProfile.separated_cycleRows {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (hnr : ∀ f, CoreMemProc.edge f ∈ E.processes.toList → f.reset = none) :
    ∀ (v : SvState) (ins : List SvState), E.Separated v (cycleRows clk ins) := by
  -- every event is `posedge clk`
  have hev : ∀ e ∈ E.events, e = ⟨clk, .posedge⟩ := by
    intro e he
    obtain ⟨f, hf, he⟩ := CoreMemDesign.mem_events.mp he
    have hr := hP.rise _ hf
    simp only [CoreMemProc.OnRise] at hr
    simp only [CoreMemEdge.events, CoreMemEdge.resetEvent?, hnr f hf, Option.map_none, Option.toList_none,
      List.mem_singleton, CoreMemEdge.clockEvent, hr.1, hr.2] at he
    exact he
  have hrow : ∀ (v r : SvState), (∀ n, n ≠ clk → SvState.lookup r n = none) →
      (SvState.lookup r clk = some ⟨#[.l0]⟩ ∨ SvState.lookup r clk = some ⟨#[.l1]⟩) →
      E.DataRow v r ∨ E.InstantRow v r := by
    intro v r hr hclk
    by_cases ho : E.occurs v (E.applyRow v r) = []
    · exact Or.inl ho
    · right
      refine ⟨ho, fun n hn => ?_, fun f hf _ rr hrr => absurd hrr (by rw [hnr f hf]; simp)⟩
      have hnc : n ≠ clk := by
        intro h
        subst h
        apply hn
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ ho
        have he' := (List.mem_filter.mp he).1
        have := hev e he'
        subst this
        exact List.mem_map_of_mem (f := SeqEvent.src) he'
      rw [CoreMemDesign.lookup_applyRow hP.four, hr n hnc]
      split <;> simp
  have hlow : ∀ (v d : SvState), E.DataRow v (lowEntry clk d) := by
    intro v d
    unfold CoreMemDesign.DataRow CoreMemDesign.occurs
    rw [List.filter_eq_nil_iff]
    intro e he
    rw [hev e he]
    simp only [SeqEvent.occursIn, edgeOf, Bool.not_eq_true]
    have hl : SvState.lookup (E.applyRow v (lowEntry clk d)) clk =
        if clk ∈ E.scalar.toDesign2.inputNames.toList then some ⟨#[.l0]⟩ else SvState.lookup v clk := by
      rw [CoreMemDesign.lookup_applyRow hP.four]
      simp [lowEntry, SvState.lookup]
    split at hl
    · rw [show (E.applyRow v (lowEntry clk d)).bit0 clk = .l0 by simp [SvState.bit0, hl]]
      cases v.bit0 clk <;> rfl
    · rw [SvState.bit0_congr hl]
      cases v.bit0 clk <;> rfl
  intro v ins
  induction ins generalizing v with
  | nil => trivial
  | cons d ds ih =>
      refine ⟨Or.inl (hlow v d), hrow _ _ (fun n hn => ?_) (Or.inr ?_), ih _⟩
      · have : (clk == n) = false := by simpa using fun h => hn h.symm
        simp [highEntry, SvState.lookup, this]
      · simp [highEntry, SvState.lookup]

#print axioms CoreMemDesign.SeqProfile.separated_cycleRows

/-- **The single-clock judgment means what it meant**: on a design whose only event is `posedge clk` it is the claim
over every typed data list, from every coherent state with a coherent memory. -/
theorem SeqRunsM_iff {r : Res CoreMemDesign} {E : CoreMemDesign} {clk : String}
    {P : List ((SvState × MemV) × (SvState × MemV)) → Prop} (hr : r = .ok E) (hP : E.SeqProfile clk)
    (hnr : ∀ f, CoreMemProc.edge f ∈ E.processes.toList → f.reset = none) :
    SeqRunsM r clk P ↔ ∀ (st : CoreMemState) (ins : List SvState), E.Coherent st → E.MemCoherent st.memory →
      (∀ d ∈ ins, E.DataTyped clk d) → ∃ rows, runCoreMemRows E st (cycleRows clk ins) = .ok rows ∧
        P (cyclePairs (rows.map fun s => (E.scalar.view s.scalar, E.memOf s.memory))) := by
  subst hr
  constructor
  · rintro ⟨E', hE', hall⟩ st ins hc hmc hd
    cases hE'
    exact hall st ins hc hmc hd (CoreMemDesign.SeqProfile.separated_cycleRows hP hnr _ ins)
  · intro hall
    exact ⟨E, rfl, fun st ins hc hmc hd _ => hall st ins hc hmc hd⟩

#print axioms SeqRunsM_iff

/-! ## Relations between clocks: hypotheses of a claim, never the semantics

"Every run" means every sequence of instants: any interleaving, any ratio, stopped clocks, coincident edges. A relation
between clocks is a hypothesis of a claim, stated on the stimulus (the events each row makes from the inputs applied
before it). Two examples: a clock that ticks only together with another (a derived or divided clock, by assumption),
and a bounded fairness (an event occurs in every window of `n` rows). -/

/-- The events of each row of a stimulus, from the inputs applied before it. -/
def CoreMemDesign.eventTrace (E : CoreMemDesign) : SvState → List SvState → List (List SeqEvent)
  | _, [] => []
  | v, r :: rs => E.occurs v (E.applyRow v r) :: E.eventTrace (E.applyRow v r) rs

/-- **`b` ticks only together with `a`**: every row in which `b` occurs is one in which `a` occurs (a clock derived
from or divided from another, by assumption; the semantics does not know it). -/
def CoreMemDesign.TicksOnlyWith (E : CoreMemDesign) (v : SvState) (rows : List SvState) (b a : SeqEvent) : Prop :=
  ∀ evs ∈ E.eventTrace v rows, b ∈ evs → a ∈ evs

/-- **Fairness, bounded**: the event `a` occurs in every window of `n` consecutive rows (the finite form of "`a` occurs
infinitely often", with a bound on the gap). -/
def CoreMemDesign.FairWithin (E : CoreMemDesign) (v : SvState) (rows : List SvState) (a : SeqEvent) (n : Nat) :
    Prop :=
  ∀ k, k + n ≤ rows.length → ∃ j evs, k ≤ j ∧ j < k + n ∧ (E.eventTrace v rows)[j]? = some evs ∧ a ∈ evs

/-- The event trace has one entry per row. -/
theorem CoreMemDesign.eventTrace_length (E : CoreMemDesign) :
    ∀ (v : SvState) (rows : List SvState), (E.eventTrace v rows).length = rows.length
  | _, [] => rfl
  | v, _ :: rs => by simp [CoreMemDesign.eventTrace, CoreMemDesign.eventTrace_length E _ rs]

/-- **In a row of the discipline in which an event occurs, nothing but event sources moves** (a data row has no event;
an instant row moves only event sources). -/
theorem CoreMemDesign.rowOk_still {E : CoreMemDesign} {v r : SvState} (hr : E.DataRow v r ∨ E.InstantRow v r)
    {e : SeqEvent} (he : e ∈ E.events) (ho : e.occursIn v (E.applyRow v r) = true) {n : String}
    (hn : n ∉ E.sources) : SvState.lookup (E.applyRow v r) n = SvState.lookup v n := by
  rcases hr with hd | hi
  · unfold CoreMemDesign.DataRow CoreMemDesign.occurs at hd
    exact absurd (List.mem_filter.mpr ⟨he, ho⟩) (by rw [hd]; simp)
  · exact hi.2.1 n hn

/-! ## A slot reads its row only through the values it applies (for the per-row equations) -/

/-- The row binding every input port (clocks, resets, data) to the value the row `r` applies to the view `v`. -/
def CoreMemDesign.appliedRow (E : CoreMemDesign) (r v : SvState) : SvState :=
  E.scalar.toDesign2.inputNames.toList.map fun n => (n, appliedIn r v n)

private theorem lookup_map_pair' (f : String → LVec) : ∀ (ns : List String) (n : String), n ∈ ns →
    SvState.lookup (ns.map fun m => (m, f m)) n = some (f n)
  | [], _, h => by simp at h
  | m :: ms, n, h => by
      by_cases hmn : m = n
      · subst hmn; simp [SvState.lookup]
      · have hmn' : (m == n) = false := by simpa using hmn
        simp only [List.map_cons, SvState.lookup, hmn', Bool.false_eq_true, ↓reduceIte]
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hmn
        · exact lookup_map_pair' f ms n h

private theorem lookup_some_of_key' : ∀ (v : SvState) (n : String), n ∈ v.map Prod.fst →
    ∃ y, SvState.lookup v n = some y
  | [], _, h => by simp at h
  | (k, w) :: rest, n, h => by
      by_cases hk : k = n
      · exact ⟨w, by simp [SvState.lookup, hk]⟩
      · have hk' : (k == n) = false := by simpa using hk
        simp only [SvState.lookup, hk', Bool.false_eq_true, ↓reduceIte]
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hk
        · exact lookup_some_of_key' rest n h

/-- **A slot reads its row only through the values it applies**: on a view with every declaration, a row applies the
same inputs as the row binding every input port to its applied value. -/
theorem CoreMemDesign.applyRow_applied {E : CoreMemDesign} (hP : E.SeqProfileI) {v : SvState} (hv : E.ShapeV v)
    (r : SvState) : E.applyRow v r = E.applyRow v (E.appliedRow r v) := by
  have h4' : ∀ dc ∈ E.scalar.toDesign2.decls.toList, dc.isInput = true → dc.twoState = false :=
    fun dc hdc _ => hP.four dc (by simpa [Elab.toDesign2] using hdc)
  have hkeys : ∀ n ∈ E.scalar.toDesign2.inputNames.toList, n ∈ v.map Prod.fst := by
    intro n hn
    rw [hv.1]
    obtain ⟨dc, hdc, -, rfl⟩ : ∃ dc ∈ E.scalar.decls.toList, dc.isInput = true ∧ dc.name = n := by
      simpa [Design2.inputNames, Elab.toDesign2] using hn
    exact List.mem_map_of_mem (f := Decl.name) hdc
  apply SvState.ext
  · unfold CoreMemDesign.applyRow; rw [keys_applyInputs2 _ _ h4' hkeys, keys_applyInputs2 _ _ h4' hkeys]
  · unfold CoreMemDesign.applyRow; rw [keys_applyInputs2 _ _ h4' hkeys, hv.1]; exact hP.names
  · intro n
    rw [CoreMemDesign.lookup_applyRow hP.four, CoreMemDesign.lookup_applyRow hP.four]
    split
    · rename_i hn
      obtain ⟨y, hy⟩ := lookup_some_of_key' v n (hkeys n hn)
      rw [CoreMemDesign.appliedRow, lookup_map_pair' _ _ n hn]
      cases hr : SvState.lookup r n <;> simp [appliedIn, hr, hy]
    · rfl

/-- The slot on a row is the slot on the row binding every input port to its applied value. -/
theorem CoreMemDesign.slotV_applied {E : CoreMemDesign} (hP : E.SeqProfileI) {v : SvState} (hv : E.ShapeV v)
    (mv : MemV) (r : SvState) : E.slotV v mv r = E.slotV v mv (E.appliedRow r v) := by
  have h := CoreMemDesign.applyRow_applied hP hv r
  unfold CoreMemDesign.applyRow at h
  simp only [CoreMemDesign.slotV, h]

/-- An applied input has its declared width (the row is typed, the held value has the width). -/
theorem CoreMemDesign.appliedIn_width_row {E : CoreMemDesign} {r : SvState} (hty : EntryTyped E.scalar.toDesign2 r)
    {n : String} (hn : n ∈ E.scalar.toDesign2.inputNames.toList) {w : Nat}
    (hw : E.scalar.toDesign2.declWidth n = some w) {v : SvState} {x : LVec} (hx : SvState.lookup v n = some x)
    (hxw : x.width = w) : (appliedIn r v n).width = w := by
  unfold appliedIn
  cases hrn : SvState.lookup r n with
  | none => simp [hx, hxw]
  | some y =>
      have := hty n y hn hrn
      rw [hw] at this
      simp only [Option.getD_some]
      exact (Option.some.inj this).symm

/-- The row an applied row applies, name by name: the applied value of every input port. -/
theorem CoreMemDesign.applyRow_appliedRow_lookup {E : CoreMemDesign} (hP : E.SeqProfileI) {v : SvState}
    (hv : E.ShapeV v) (r : SvState) {n : String} (hn : n ∈ E.scalar.toDesign2.inputNames.toList) :
    SvState.lookup (E.applyRow v r) n = some (appliedIn r v n) := by
  rw [CoreMemDesign.applyRow_applied hP hv r, CoreMemDesign.lookup_applyRow hP.four, if_pos hn,
    CoreMemDesign.appliedRow, lookup_map_pair' _ _ n hn]
  rfl

/-- Bit 0 of a name, from its value. -/
theorem SvState.bit0_of_lookup {st : SvState} {n : String} {x : LVec} (h : SvState.lookup st n = some x) :
    st.bit0 n = x.bits[0]?.getD .lx := by
  simp only [SvState.bit0, h]

/-- **The discipline at an edge, on applied values**: in a row of the discipline from a view of the design's shape in
which the event `e` occurs (read on the value the row applies to its source), every input that is no event source
keeps its value: the row applies the value it had. -/
theorem CoreMemDesign.applied_still {E : CoreMemDesign} (hP : E.SeqProfileI) {v r : SvState} (hv : E.ShapeV v)
    (hr : E.DataRow v r ∨ E.InstantRow v r) {e : SeqEvent} (he : e ∈ E.events)
    (hes : e.src ∈ E.scalar.toDesign2.inputNames.toList)
    (ho : edgeOf e.kind (v.bit0 e.src) ((appliedIn r v e.src).bits[0]?.getD .lx) = true) {x : String}
    (hx : x ∈ E.scalar.toDesign2.inputNames.toList) (hxs : x ∉ E.sources) :
    appliedIn r v x = (SvState.lookup v x).getD ⟨#[]⟩ := by
  have ho' : e.occursIn v (E.applyRow v r) = true := by
    rw [SeqEvent.occursIn, SvState.bit0_of_lookup (CoreMemDesign.applyRow_appliedRow_lookup hP hv r hes)]
    exact ho
  have h := CoreMemDesign.rowOk_still hr he ho' hxs
  rw [CoreMemDesign.applyRow_appliedRow_lookup hP hv r hx] at h
  rw [← h]
  rfl

/-! ## Domains and crossings, computed

A DOMAIN is a clock event with the registers its processes write (an asynchronous reset belongs to its clock's
domain; one driver per signal makes the domains a partition of the registers). A CROSSING is a read, by an edge
process of one domain, of a register of another (directly, or through continuous assigns). Crossings are where the
interleaving of instants matters; with none, a design is the product of its single-domain parts. A claim about a
crossing is LANGUAGE-LEVEL (the read sees the source's committed value, §10.4.2; metastability is not modelled). -/

/-- A list without repeats, first occurrences kept (computed by `simp` on a literal list). -/
def dedupL {α : Type} [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun acc a => if a ∈ acc then acc else acc ++ [a]) []

/-- The domain of an edge process: its clock event. -/
def CoreMemProc.domain? : CoreMemProc → Option SeqEvent
  | .edge f => some f.clockEvent
  | .assign _ _ => none
  | .initial _ => none
  | .comb _ => none
  | .implicit _ => none
  | .latch _ => none
  | .unsupported _ _ => none

/-- **The domains of a design**: each clock event with the registers its processes write. -/
def CoreMemDesign.domains (E : CoreMemDesign) : List (SeqEvent × List String) :=
  (dedupL (E.processes.toList.filterMap CoreMemProc.domain?)).map fun e =>
    (e, E.processes.toList.flatMap fun p => if p.domain? = some e then p.targets else [])

/-- The domain whose processes write a name (none for an input or a continuous assign's target). -/
def CoreMemDesign.domainOf (E : CoreMemDesign) (x : String) : Option SeqEvent :=
  (E.processes.toList.find? fun p => p.isEdge && p.targets.contains x).bind CoreMemProc.domain?

/-- The registers a name reads through the continuous assigns: a register itself, an assign's target the registers
its expression reads (`fuel` bounds the chain; the assigns are acyclic under `topoC`). -/
def CoreMemDesign.stateReads (E : CoreMemDesign) : Nat → String → List String
  | 0, _ => []
  | fuel + 1, x =>
      if (E.domainOf x).isSome then [x]
      else (E.processes.toList.flatMap fun p => match p with
        | .assign (.ident n) v => if n = x then PExpr.sigNames v else []
        | _ => []).flatMap (E.stateReads fuel)

/-- **The crossings of a design**: (the reader's domain, the register, its domain) for every read of another domain's
register by an edge process. -/
def CoreMemDesign.crossings (E : CoreMemDesign) : List (SeqEvent × String × SeqEvent) :=
  E.processes.toList.flatMap fun p => match p with
    | .edge f => (dedupL (f.body.readNames.flatMap (E.stateReads (E.processes.size + 1)))).filterMap fun x =>
        match E.domainOf x with
        | some B => if B = f.clockEvent then none else some (f.clockEvent, x, B)
        | none => none
    | _ => []

end LeanModels.Sv.Kernel
