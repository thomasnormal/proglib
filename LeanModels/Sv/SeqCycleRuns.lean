import LeanModels.Sv.SeqCycle

/-!
# Runs of the clocked route and the run judgment (`LeanModels.Sv.Kernel`)

**Status: derived from the ordinary E route** (part of the clocked tactics' theory, `SeqCycle.lean`).

* `runMV`, `runV`: the view-level runs (cycle after cycle, the next cycle from the post sample), with and without a
  memory view; `runRowsM_seq`, `runRows_seq`: they are the route's own runs (`runCoreMemRows` on `cycleRows`).
* **`SeqRunsM r clk P`**, the prover's judgment: the instantiation succeeds and, from every coherent state with a
  coherent memory (the x start and every power-up, memory contents arbitrary), on every typed data list, the route's
  run exists and its samples (view and memory view, pre and post of each cycle) satisfy `P`. `SeqRuns` is the same
  judgment for claims about the views only.
* `SeqRunsM.intro`, `SeqRunsM.of_cycleFn` (and the `SeqRuns` forms): how a claim is proved from an invariant and the
  cycle equations, with no trace induction of the prover's own (`runF`, `stF`, `runF_getElem?`, `stF_succ`).
* `cycleV_applied`, `cycleMV_applied`, `appliedIn_width`: a cycle reads its data entry only through the values it
  applies.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Runs: every run of the route, from every coherent state -/

/-- The view-level run with a memory view: each cycle's pre and post sample, the next cycle from the post sample. -/
def CoreMemDesign.runMV (E : CoreMemDesign) (clk : String) :
    SvState × MemV → List SvState → Res (List ((SvState × MemV) × (SvState × MemV)))
  | _, [] => .ok []
  | σ, d :: ds => do
      let pp ← E.cycleMV clk σ d
      let rest ← E.runMV clk pp.2 ds
      .ok (pp :: rest)

/-- The view-level run of a design without memories. -/
def CoreMemDesign.runV (E : CoreMemDesign) (clk : String) : SvState → List SvState → Res (List (SvState × SvState))
  | _, [] => .ok []
  | v, d :: ds => do
      let pp ← E.cycleV clk v d
      let rest ← E.runV clk pp.2 ds
      .ok (pp :: rest)

/-- The pre and post samples of a run of cycles: the slot states two by two. -/
def cyclePairs {α : Type} : List α → List (α × α)
  | a :: b :: rest => (a, b) :: cyclePairs rest
  | _ => []

theorem cyclePairs_map {α β : Type} (f : α → β) :
    ∀ (l : List α), cyclePairs (l.map f) = (cyclePairs l).map fun pp => (f pp.1, f pp.2)
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by simp [cyclePairs, cyclePairs_map f rest]

/-- **THE RUN REFINEMENT**: from every coherent state with a coherent memory and every typed data list, when the
view-level run succeeds the route's own run of the cycles (`runCoreMemRows` on `cycleRows`) succeeds and its samples,
two per cycle, are exactly the view-level run's. -/
theorem CoreMemDesign.runRowsM_seq {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) :
    ∀ (ins : List SvState) (st : CoreMemState) (tr : List ((SvState × MemV) × (SvState × MemV))), E.Coherent st →
      E.MemCoherent st.memory → (∀ d ∈ ins, E.DataTyped clk d) →
      E.runMV clk (E.scalar.view st.scalar, E.memOf st.memory) ins = .ok tr →
      ∃ rows, runCoreMemRows E st (cycleRows clk ins) = .ok rows ∧
        cyclePairs (rows.map fun s => (E.scalar.view s.scalar, E.memOf s.memory)) = tr
  | [], st, tr, _, _, _, hv => by
      simp only [CoreMemDesign.runMV, Res.ok.injEq] at hv
      subst hv
      exact ⟨[], rfl, rfl⟩
  | d :: ds, st, tr, hc, hmc, hd, hv => by
      simp only [CoreMemDesign.runMV, Res.bind_eq_ok, Res.ok.injEq] at hv
      obtain ⟨⟨pre, post⟩, hcyc, rest, hrest, rfl⟩ := hv
      obtain ⟨s1, s2, hs1, hs2, hv1, hv2, hc1, hc2, hmc1, hmc2⟩ :=
        CoreMemDesign.cycleMV_refines hP hc hmc (hd d (by simp)) (CoreMemDesign.highEntry_typed hclk) hcyc
      obtain ⟨rows, hrows, hpairs⟩ := CoreMemDesign.runRowsM_seq hP hclk ds s2 rest hc2 hmc2
        (fun d' hd' => hd d' (by simp [hd'])) (by rw [hv2]; exact hrest)
      refine ⟨s1 :: s2 :: rows, ?_, ?_⟩
      · simp only [cycleRows, runCoreMemRows, hs1, hs2, Res.ok_bind,
          show (lowEntry clk d).isEmpty = false from rfl, show (highEntry clk).isEmpty = false from rfl,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, hrows]
      · simp [cyclePairs, hv1, hv2, hpairs]

#print axioms CoreMemDesign.runRowsM_seq

/-- **THE RUN REFINEMENT, without memories**: from every coherent state and every typed data list, when the view-level
run succeeds the route's own run of the cycles succeeds and its samples are exactly the view-level run's. -/
theorem CoreMemDesign.runRows_seq {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (hm : E.memories.toList = []) (hclk : E.scalar.toDesign2.declWidth clk = some 1) :
    ∀ (ins : List SvState) (st : CoreMemState) (tr : List (SvState × SvState)), E.Coherent st →
      (∀ d ∈ ins, E.DataTyped clk d) → E.runV clk (E.scalar.view st.scalar) ins = .ok tr →
      ∃ rows, runCoreMemRows E st (cycleRows clk ins) = .ok rows ∧
        cyclePairs (rows.map fun s => E.scalar.view s.scalar) = tr
  | [], st, tr, _, _, hv => by
      simp only [CoreMemDesign.runV, Res.ok.injEq] at hv
      subst hv
      exact ⟨[], rfl, rfl⟩
  | d :: ds, st, tr, hc, hd, hv => by
      simp only [CoreMemDesign.runV, Res.bind_eq_ok, Res.ok.injEq] at hv
      obtain ⟨⟨pre, post⟩, hcyc, rest, hrest, rfl⟩ := hv
      obtain ⟨s1, s2, hs1, hs2, hv1, hv2, hc1, hc2⟩ :=
        CoreMemDesign.cycle_of_seqProfile hP hm hc (hd d (by simp)) (CoreMemDesign.highEntry_typed hclk) hcyc
      obtain ⟨rows, hrows, hpairs⟩ :=
        CoreMemDesign.runRows_seq hP hm hclk ds s2 rest hc2 (fun d' hd' => hd d' (by simp [hd'])) (by rw [hv2]; exact hrest)
      refine ⟨s1 :: s2 :: rows, ?_, ?_⟩
      · simp only [cycleRows, runCoreMemRows, hs1, hs2, Res.ok_bind,
          show (lowEntry clk d).isEmpty = false from rfl, show (highEntry clk).isEmpty = false from rfl,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, hrows]
      · simp [cyclePairs, hv1, hv2, hpairs]

#print axioms CoreMemDesign.runRows_seq

/-- A cycle reads its data entry only through the inputs it applies: two entries applying the same inputs give the same
cycle. -/
theorem CoreMemDesign.cycleMV_congr_data (E : CoreMemDesign) (clk : String) (σ : SvState × MemV) (d d' : SvState)
    (h : applyInputs2 E.scalar.toDesign2 (lowEntry clk d) σ.1 = applyInputs2 E.scalar.toDesign2 (lowEntry clk d') σ.1) :
    E.cycleMV clk σ d = E.cycleMV clk σ d' := by
  simp only [CoreMemDesign.cycleMV, CoreMemDesign.slotV, h]

theorem CoreMemDesign.cycleV_congr_data (E : CoreMemDesign) (clk : String) (v d d' : SvState)
    (h : applyInputs2 E.scalar.toDesign2 (lowEntry clk d) v = applyInputs2 E.scalar.toDesign2 (lowEntry clk d') v) :
    E.cycleV clk v d = E.cycleV clk v d' := by
  simp only [CoreMemDesign.cycleV, CoreMemDesign.cycleMV_congr_data E clk (v, memNone) d d' h]

/-! ## The prover's judgment: every run of a family member -/

/-- **Every clocked run of a canonical-E family member**: the instantiation succeeds and, from every coherent state with
a coherent memory (the x start and every power-up included, memory contents arbitrary), on every typed data list, the
route's own run of the cycles exists and its samples (pre, post; one pair per cycle; each a view and a memory view)
satisfy `P`. Never vacuous: the run's existence is part of the claim. -/
def SeqRunsM (r : Res CoreMemDesign) (clk : String) (P : List ((SvState × MemV) × (SvState × MemV)) → Prop) : Prop :=
  ∃ E, r = .ok E ∧ ∀ (st : CoreMemState) (ins : List SvState), E.Coherent st → E.MemCoherent st.memory →
    (∀ d ∈ ins, E.DataTyped clk d) → ∃ rows, runCoreMemRows E st (cycleRows clk ins) = .ok rows ∧
      P (cyclePairs (rows.map fun s => (E.scalar.view s.scalar, E.memOf s.memory)))

/-- **Every clocked run, a claim about the views**: `SeqRunsM` for a claim that reads the views of the samples only. -/
def SeqRuns (r : Res CoreMemDesign) (clk : String) (P : List (SvState × SvState) → Prop) : Prop :=
  SeqRunsM r clk fun tr => P (tr.map fun pp => (pp.1.1, pp.2.1))

/-- A run claim implies every weaker claim. -/
theorem SeqRunsM.mono {r : Res CoreMemDesign} {clk : String} {P Q : List ((SvState × MemV) × (SvState × MemV)) → Prop}
    (h : SeqRunsM r clk P) (hPQ : ∀ tr, P tr → Q tr) : SeqRunsM r clk Q := by
  obtain ⟨E, hr, hall⟩ := h
  exact ⟨E, hr, fun st ins hc hmc hd => by
    obtain ⟨rows, hrows, hp⟩ := hall st ins hc hmc hd
    exact ⟨rows, hrows, hPQ _ hp⟩⟩

theorem SeqRuns.mono {r : Res CoreMemDesign} {clk : String} {P Q : List (SvState × SvState) → Prop}
    (h : SeqRuns r clk P) (hPQ : ∀ tr, P tr → Q tr) : SeqRuns r clk Q :=
  SeqRunsM.mono h fun tr => hPQ _

/-- The shape of a view: one value per declaration, in declaration order, of its declared width. -/
def CoreMemDesign.ShapeV (E : CoreMemDesign) (v : SvState) : Prop :=
  v.map Prod.fst = E.scalar.decls.toList.map Decl.name ∧
    v.map (fun p => p.2.width) = E.scalar.decls.toList.map Decl.width

private theorem viewAux_widths {s : Store} {E : Elab} (hT : E.Typed s) :
    ∀ (ds : List Decl) (i : Nat), (∀ k (hk : k < ds.length), E.decls[i + k]? = some ds[k]) →
      (viewAux s ds i).map (fun p => p.2.width) = ds.map Decl.width
  | [], _, _ => rfl
  | d :: ds, i, h => by
      have h0 := h 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      have hdecl : E.declOf { decl := i } = some d := by simp [Elab.declOf, h0]
      simp only [viewAux, List.map_cons]
      congr 1
      · rw [(s { decl := i }).width_eq, hT _ d hdecl]; rfl
      · exact viewAux_widths hT ds (i + 1) fun k hk => by
          have := h (k + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- A coherent state's view has the shape. -/
theorem CoreMemDesign.Coherent.shape {E : CoreMemDesign} {st : CoreMemState} (hc : E.Coherent st) :
    E.ShapeV (E.scalar.view st.scalar) :=
  ⟨E.scalar.keys_view st.scalar, viewAux_widths hc.typed E.scalar.decls.toList 0 fun k hk => by simp⟩

/-- The shape of a memory view: every element of every memory of its element width. -/
def CoreMemDesign.MemShapeV (E : CoreMemDesign) (mv : MemV) : Prop :=
  ∀ md ∈ E.memories.toList, ∀ k, (mv md.source.name k).width = md.shape.elemWidth

/-- A coherent memory's view has the shape. -/
theorem CoreMemDesign.MemCoherent.shape {E : CoreMemDesign} (hmo : E.memOkB = true) {m : MemState}
    (hmc : E.MemCoherent m) : E.MemShapeV (E.memOf m) := by
  intro md hmd k
  obtain ⟨blk, hb, -, -, hw⟩ := hmc.blocks md hmd
  simp [CoreMemDesign.memOf, CoreMemDesign.memDecl?_self hmo hmd, hb, hw k]

/-- **How a `SeqRunsM` claim is proved**: from the profile, an invariant every coherent state's views have, the cycle's
success from the invariant keeping it (the cycle equations), and the claim about every view-level run from the
invariant (the prover's mathematics). -/
theorem SeqRunsM.intro {r : Res CoreMemDesign} {E : CoreMemDesign} {clk : String}
    {P : List ((SvState × MemV) × (SvState × MemV)) → Prop} (hr : r = .ok E) (hP : E.SeqProfile clk)
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) (Inv : SvState × MemV → Prop)
    (hinv : ∀ st, E.Coherent st → E.MemCoherent st.memory → Inv (E.scalar.view st.scalar, E.memOf st.memory))
    (hstep : ∀ σ d, Inv σ → E.DataTyped clk d → ∃ pre post, E.cycleMV clk σ d = .ok (pre, post) ∧ Inv post)
    (hrun : ∀ σ ins tr, Inv σ → (∀ d ∈ ins, E.DataTyped clk d) → E.runMV clk σ ins = .ok tr → P tr) :
    SeqRunsM r clk P := by
  refine ⟨E, hr, fun st ins hc hmc hd => ?_⟩
  have hex : ∀ (ins : List SvState) (σ : SvState × MemV), Inv σ → (∀ d ∈ ins, E.DataTyped clk d) →
      ∃ tr, E.runMV clk σ ins = .ok tr := by
    intro ins
    induction ins with
    | nil => intro σ _ _; exact ⟨[], rfl⟩
    | cons d ds ih =>
        intro σ hσ hd
        obtain ⟨pre, post, hcyc, hpost⟩ := hstep σ d hσ (hd d (by simp))
        obtain ⟨tr, htr⟩ := ih post hpost fun d' hd' => hd d' (by simp [hd'])
        exact ⟨(pre, post) :: tr, by simp [CoreMemDesign.runMV, hcyc, htr]⟩
  have hσ0 := hinv st hc hmc
  obtain ⟨tr, htr⟩ := hex ins _ hσ0 hd
  obtain ⟨rows, hrows, hpairs⟩ := CoreMemDesign.runRowsM_seq hP hclk ins st tr hc hmc hd htr
  exact ⟨rows, hrows, hpairs ▸ hrun _ ins tr hσ0 hd htr⟩

#print axioms SeqRunsM.intro

/-- **How a `SeqRuns` claim is proved, for a design without memories**: from the profile, an invariant every shaped
view has, the cycle's success from the invariant keeping it (the cycle equations), and the claim about every view-level
run from the invariant (the prover's mathematics). -/
theorem SeqRuns.intro {r : Res CoreMemDesign} {E : CoreMemDesign} {clk : String}
    {P : List (SvState × SvState) → Prop} (hr : r = .ok E) (hP : E.SeqProfile clk) (hm : E.memories.toList = [])
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) (Inv : SvState → Prop)
    (hinv : ∀ v, E.ShapeV v → Inv v)
    (hstep : ∀ v d, Inv v → E.DataTyped clk d → ∃ pre post, E.cycleV clk v d = .ok (pre, post) ∧ Inv post)
    (hrun : ∀ v ins tr, Inv v → (∀ d ∈ ins, E.DataTyped clk d) → E.runV clk v ins = .ok tr → P tr) :
    SeqRuns r clk P := by
  refine ⟨E, hr, fun st ins hc _ hd => ?_⟩
  have hex : ∀ (ins : List SvState) (v : SvState), Inv v → (∀ d ∈ ins, E.DataTyped clk d) →
      ∃ tr, E.runV clk v ins = .ok tr := by
    intro ins
    induction ins with
    | nil => intro v _ _; exact ⟨[], rfl⟩
    | cons d ds ih =>
        intro v hv hd
        obtain ⟨pre, post, hcyc, hpost⟩ := hstep v d hv (hd d (by simp))
        obtain ⟨tr, htr⟩ := ih post hpost fun d' hd' => hd d' (by simp [hd'])
        exact ⟨(pre, post) :: tr, by simp [CoreMemDesign.runV, hcyc, htr]⟩
  have hv0 := hinv _ hc.shape
  obtain ⟨tr, htr⟩ := hex ins _ hv0 hd
  obtain ⟨rows, hrows, hpairs⟩ := CoreMemDesign.runRows_seq hP hm hclk ins st tr hc hd htr
  refine ⟨rows, hrows, ?_⟩
  have hmap : (cyclePairs (rows.map fun s => (E.scalar.view s.scalar, E.memOf s.memory))).map
      (fun pp => (pp.1.1, pp.2.1)) = cyclePairs (rows.map fun s => E.scalar.view s.scalar) := by
    have := cyclePairs_map (fun (σ : SvState × MemV) => σ.1) (rows.map fun s => (E.scalar.view s.scalar, E.memOf s.memory))
    simp only [List.map_map, Function.comp_def] at this
    exact this.symm
  show P ((cyclePairs (rows.map fun s => (E.scalar.view s.scalar, E.memOf s.memory))).map fun pp => (pp.1.1, pp.2.1))
  rw [hmap, hpairs]
  exact hrun _ ins tr hv0 hd htr

#print axioms SeqRuns.intro

/-! ## Runs of a cycle function: the plumbing every claim needs, once

A prover states the design's cycle as a function `F σ d = (pre, post)` of the current state (a view, or a view and a
memory view) and the cycle's data (the cycle equations, `sv_equations`), and its claim about the samples `runF F σ ins`.
`SeqRunsM.of_cycleFn` / `SeqRuns.of_cycleFn` close the run judgment from the two; `runF_getElem?` and `stF_succ` index a
run (cycle `c` is `F` applied to the state before it). -/

/-- The samples of the run of a cycle function `F` from the state `σ` on the data list (one (pre, post) per cycle). -/
def runF {α : Type} (F : α → SvState → α × α) : α → List SvState → List (α × α)
  | _, [] => []
  | σ, d :: ds => F σ d :: runF F (F σ d).2 ds

/-- The state before cycle `c` of such a run. -/
def stF {α : Type} (F : α → SvState → α × α) : α → List SvState → Nat → α
  | σ, _, 0 => σ
  | σ, [], _ + 1 => σ
  | σ, d :: ds, c + 1 => stF F (F σ d).2 ds c

/-- Cycle `c` of a run is `F` applied to the state before it and the cycle's data. -/
theorem runF_getElem? {α : Type} (F : α → SvState → α × α) :
    ∀ (σ : α) (ins : List SvState) (c : Nat),
      (runF F σ ins)[c]? = (ins[c]?).map fun d => F (stF F σ ins c) d
  | σ, [], c => by simp [runF]
  | σ, d :: ds, 0 => by simp [runF, stF]
  | σ, d :: ds, c + 1 => by simp [runF, stF, runF_getElem? F (F σ d).2 ds c]

/-- The state before cycle `c + 1` is the post sample of cycle `c`. -/
theorem stF_succ {α : Type} (F : α → SvState → α × α) :
    ∀ (σ : α) (ins : List SvState) (c : Nat) (d : SvState), ins[c]? = some d →
      stF F σ ins (c + 1) = (F (stF F σ ins c) d).2
  | σ, [], c, d, h => by simp at h
  | σ, d' :: ds, 0, d, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [stF]
  | σ, d' :: ds, c + 1, d, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [stF]
      exact stF_succ F (F σ d').2 ds c d h

/-- An invariant the cycle function keeps holds before every cycle of a run. -/
theorem stF_inv {α : Type} (F : α → SvState → α × α) (Inv : α → Prop) (D : SvState → Prop)
    (hstep : ∀ σ d, Inv σ → D d → Inv (F σ d).2) :
    ∀ (σ : α) (ins : List SvState) (c : Nat), Inv σ → (∀ d ∈ ins, D d) → Inv (stF F σ ins c)
  | σ, [], c, hv, _ => by cases c <;> simpa [stF] using hv
  | σ, d :: ds, 0, hv, _ => by simpa [stF] using hv
  | σ, d :: ds, c + 1, hv, hd => by
      simp only [stF]
      exact stF_inv F Inv D hstep (F σ d).2 ds c (hstep σ d hv (hd d (by simp)))
        (fun d' h' => hd d' (by simp [h']))

/-- **How a `SeqRunsM` claim is proved from the cycle function**: the profile, an invariant every coherent state's views
have, the cycle equations (`cycleMV` computes `F` and `F` keeps the invariant), and the claim about the samples of
`F`'s runs. -/
theorem SeqRunsM.of_cycleFn {r : Res CoreMemDesign} {E : CoreMemDesign} {clk : String}
    {P : List ((SvState × MemV) × (SvState × MemV)) → Prop} (hr : r = .ok E) (hP : E.SeqProfile clk)
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) (Inv : SvState × MemV → Prop)
    (hinv : ∀ st, E.Coherent st → E.MemCoherent st.memory → Inv (E.scalar.view st.scalar, E.memOf st.memory))
    (F : SvState × MemV → SvState → (SvState × MemV) × (SvState × MemV))
    (hstep : ∀ σ d, Inv σ → E.DataTyped clk d → E.cycleMV clk σ d = .ok (F σ d) ∧ Inv (F σ d).2)
    (hrun : ∀ σ ins, Inv σ → (∀ d ∈ ins, E.DataTyped clk d) → P (runF F σ ins)) :
    SeqRunsM r clk P := by
  refine SeqRunsM.intro hr hP hclk Inv hinv
    (fun σ d hσ hd => ⟨(F σ d).1, (F σ d).2, (hstep σ d hσ hd).1, (hstep σ d hσ hd).2⟩) ?_
  intro σ ins tr hσ hd htr
  have hall : ∀ (ins : List SvState) (σ : SvState × MemV), Inv σ → (∀ d ∈ ins, E.DataTyped clk d) →
      E.runMV clk σ ins = .ok (runF F σ ins) := by
    intro ins
    induction ins with
    | nil => intro σ _ _; rfl
    | cons d ds ih =>
        intro σ hσ hd
        have h1 := hstep σ d hσ (hd d (by simp))
        simp [CoreMemDesign.runMV, runF, h1.1, ih _ h1.2 (fun d' h' => hd d' (by simp [h']))]
  rw [hall ins σ hσ hd, Res.ok.injEq] at htr
  subst htr
  exact hrun σ ins hσ hd

#print axioms SeqRunsM.of_cycleFn

/-- **How a `SeqRuns` claim is proved from the cycle function, for a design without memories**: the profile, an
invariant every shaped view has, the cycle equations (`cycleV` computes `F` and `F` keeps the invariant), and the claim
about the samples of `F`'s runs. -/
theorem SeqRuns.of_cycleFn {r : Res CoreMemDesign} {E : CoreMemDesign} {clk : String}
    {P : List (SvState × SvState) → Prop} (hr : r = .ok E) (hP : E.SeqProfile clk) (hm : E.memories.toList = [])
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) (Inv : SvState → Prop) (hinv : ∀ v, E.ShapeV v → Inv v)
    (F : SvState → SvState → SvState × SvState)
    (hstep : ∀ v d, Inv v → E.DataTyped clk d → E.cycleV clk v d = .ok (F v d) ∧ Inv (F v d).2)
    (hrun : ∀ v ins, Inv v → (∀ d ∈ ins, E.DataTyped clk d) → P (runF F v ins)) :
    SeqRuns r clk P := by
  refine SeqRuns.intro hr hP hm hclk Inv hinv
    (fun v d hv hd => ⟨(F v d).1, (F v d).2, (hstep v d hv hd).1, (hstep v d hv hd).2⟩) ?_
  intro v ins tr hv hd htr
  have hall : ∀ (ins : List SvState) (v : SvState), Inv v → (∀ d ∈ ins, E.DataTyped clk d) →
      E.runV clk v ins = .ok (runF F v ins) := by
    intro ins
    induction ins with
    | nil => intro v _ _; rfl
    | cons d ds ih =>
        intro v hv hd
        have h1 := hstep v d hv (hd d (by simp))
        simp [CoreMemDesign.runV, runF, h1.1, ih _ h1.2 (fun d' h' => hd d' (by simp [h']))]
  rw [hall ins v hv hd, Res.ok.injEq] at htr
  subst htr
  exact hrun v ins hv hd

#print axioms SeqRuns.of_cycleFn

/-! ## A cycle reads its data entry only through the values it applies -/

/-- A typed data entry binds an input at its declared width. -/
theorem CoreMemDesign.DataTyped.width {E : CoreMemDesign} {clk : String} {d : SvState} (hd : E.DataTyped clk d)
    {n : String} (hn : n ≠ clk) (hin : n ∈ E.scalar.toDesign2.inputNames.toList) {x : LVec}
    (hx : SvState.lookup d n = some x) : E.scalar.toDesign2.declWidth n = some x.width := by
  apply hd n x hin
  have hne : (clk == n) = false := by simpa using fun h => hn h.symm
  simp [lowEntry, SvState.lookup, hne, hx]

/-! ## A cycle reads its data entry only through the values it applies -/

/-- The value a cycle's data entry `d` applies to input `n` of the view `v`: the entry's own value, else the held
one. -/
def appliedIn (d v : SvState) (n : String) : LVec :=
  (SvState.lookup d n).getD ((SvState.lookup v n).getD ⟨#[]⟩)

/-- The data inputs of a design: its input ports other than the clock. -/
def CoreMemDesign.dataInputs (E : CoreMemDesign) (clk : String) : List String :=
  E.scalar.toDesign2.inputNames.toList.filter (· != clk)

/-- The entry binding every data input to the value `d` applies to `v`. -/
def CoreMemDesign.appliedEntry (E : CoreMemDesign) (clk : String) (d v : SvState) : SvState :=
  (E.dataInputs clk).map fun n => (n, appliedIn d v n)

private theorem lookup_map_pair (f : String → LVec) : ∀ (ns : List String) (n : String), n ∈ ns →
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
        · exact lookup_map_pair f ms n h

private theorem lookup_some_of_key : ∀ (v : SvState) (n : String), n ∈ v.map Prod.fst →
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
        · exact lookup_some_of_key rest n h

/-- **A cycle reads its data entry only through the values it applies**: from a view with every declaration
(`ShapeV`), the inputs a cycle on `d` applies are those of the entry binding every data input to its applied value. -/
theorem CoreMemDesign.applyInputs_applied {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) {v : SvState}
    (hv : E.ShapeV v) (d : SvState) :
    applyInputs2 E.scalar.toDesign2 (lowEntry clk d) v =
      applyInputs2 E.scalar.toDesign2 (lowEntry clk (E.appliedEntry clk d v)) v := by
  have h4' : ∀ dc ∈ E.scalar.toDesign2.decls.toList, dc.isInput = true → dc.twoState = false :=
    fun dc hdc _ => hP.four dc (by simpa [Elab.toDesign2] using hdc)
  have hkeys : ∀ n ∈ E.scalar.toDesign2.inputNames.toList, n ∈ v.map Prod.fst := by
    intro n hn
    rw [hv.1]
    obtain ⟨dc, hdc, -, rfl⟩ : ∃ dc ∈ E.scalar.decls.toList, dc.isInput = true ∧ dc.name = n := by
      simpa [Design2.inputNames, Elab.toDesign2] using hn
    exact List.mem_map_of_mem (f := Decl.name) hdc
  apply SvState.ext
  · rw [keys_applyInputs2 _ _ h4' hkeys, keys_applyInputs2 _ _ h4' hkeys]
  · rw [keys_applyInputs2 _ _ h4' hkeys, hv.1]; exact hP.names
  · intro n
    rw [lookup_applyInputs2 _ _ _ n h4', lookup_applyInputs2 _ _ _ n h4']
    split
    · rename_i hn
      obtain ⟨y, hy⟩ := lookup_some_of_key v n (hkeys n hn)
      by_cases hc : clk = n
      · subst hc; simp [lowEntry, SvState.lookup]
      · have hc' : (clk == n) = false := by simpa using hc
        have hmem : n ∈ E.dataInputs clk := by
          simp only [CoreMemDesign.dataInputs, List.mem_filter, bne_iff_ne, ne_eq]
          exact ⟨hn, fun h => hc h.symm⟩
        simp only [lowEntry, SvState.lookup, hc', Bool.false_eq_true, ↓reduceIte, CoreMemDesign.appliedEntry]
        rw [lookup_map_pair _ _ n hmem]
        cases hdn : SvState.lookup d n <;> simp [appliedIn, hdn, hy]
    · rfl

/-- A cycle (without memories) on `d` is the cycle on the entry binding every data input to its applied value (so the
cycle equations are computed once, for an entry that binds every data input). -/
theorem CoreMemDesign.cycleV_applied {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) {v : SvState}
    (hv : E.ShapeV v) (d : SvState) : E.cycleV clk v d = E.cycleV clk v (E.appliedEntry clk d v) :=
  CoreMemDesign.cycleV_congr_data E clk v d _ (CoreMemDesign.applyInputs_applied hP hv d)

/-- A cycle with memories on `d` is the cycle on the entry binding every data input to its applied value. -/
theorem CoreMemDesign.cycleMV_applied {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) {v : SvState}
    (mv : MemV) (hv : E.ShapeV v) (d : SvState) :
    E.cycleMV clk (v, mv) d = E.cycleMV clk (v, mv) (E.appliedEntry clk d v) :=
  CoreMemDesign.cycleMV_congr_data E clk (v, mv) d _ (CoreMemDesign.applyInputs_applied hP hv d)

/-- An applied input has its declared width (the entry is typed, the held value has the width). -/
theorem CoreMemDesign.appliedIn_width {E : CoreMemDesign} {clk : String} {d : SvState} (hd : E.DataTyped clk d)
    {n : String} (hn : n ∈ E.dataInputs clk) {w : Nat} (hw : E.scalar.toDesign2.declWidth n = some w)
    {v : SvState} {x : LVec} (hx : SvState.lookup v n = some x) (hxw : x.width = w) :
    (appliedIn d v n).width = w := by
  unfold appliedIn
  cases hdn : SvState.lookup d n with
  | none => simp [hx, hxw]
  | some y =>
      simp only [CoreMemDesign.dataInputs, List.mem_filter, bne_iff_ne, ne_eq] at hn
      have := CoreMemDesign.DataTyped.width hd hn.2 hn.1 hdn
      rw [hw] at this
      simp only [Option.getD_some]
      exact (Option.some.inj this).symm
end LeanModels.Sv.Kernel
