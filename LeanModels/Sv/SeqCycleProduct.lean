import LeanModels.Sv.SeqCycleInstant

/-!
# Domains without a crossing: the product theorem (`LeanModels.Sv.Kernel`, the clocked tactics' theory)

**Status: derived from the ordinary E route.** A DOMAIN of a design is a set of events `A` with the registers its
processes write. When no process of `A` reads anything outside a set `S` of names (its registers, its clocks and
resets, the data inputs it reads, continuous assigns over these), no other process writes into `S`, and the continuous
assigns into `S` read only `S`, the domain evolves on its own:

* `slotV_domain`: two slots on views that agree on `S`, on rows that apply the same values to `S`, land on views that
  agree on `S` (whatever the rest of the design does, and whatever the other clocks do in the row);
* `runRV_domain`: two runs from views agreeing on `S`, on row lists applying the same values to `S` row by row, agree
  on `S` sample by sample. So a run of the whole design projects to the run in which only `A`'s events occur (the
  other clocks stopped): a single-clock theorem about `A` transfers unchanged, and the interleaving with the other
  domains adds nothing to prove;
* `tick_comm`: a coincident instant of two such domains is the two single-domain instants in either order (the
  ticks commute) on what each domain owns.

Every edge body is nonblocking to whole signals (the obligations' form for several edge processes), so no edge process
writes a memory and the memory view is one through the run (a memory written across domains is the memory slice's,
next). Nothing here unfolds the route's step: the theorems are about the mirror's slot, which `step_seqI` and
`runRows_slots` relate to the route.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## What an edge body's evaluation reads -/

mutual

/-- **The names an edge body's evaluation reads on the view** (what `execV` evaluates, arm by arm: right-hand sides at
their target's width, conditions, case subjects and patterns), for the nonblocking whole-signal fragment. -/
def CoreMemDesign.stmtReadsV (E : CoreMemDesign) : PStmt → List String
  | .nbaAssign t e =>
      match E.scalarTarget t with
      | some w => E.readsV E.env E.elems (some w) e
      | none => []
  | .nbaAssignL (.ident t) e =>
      match E.scalarTarget t with
      | some w => E.readsV E.env E.elems (some w) e
      | none => []
  | .ifStmt c y n => E.readsV E.env E.elems (some 1) c ++ E.stmtReadsV y ++ E.optStmtReadsV n
  | .block body => E.listStmtReadsV body
  | .caseStmt s items d _ _ => E.readsV E.env E.elems none s ++ E.itemsStmtReadsV items ++ E.optStmtReadsV d
  | _ => []
termination_by structural s => s

/-- `stmtReadsV` of an optional statement. -/
def CoreMemDesign.optStmtReadsV (E : CoreMemDesign) : Option PStmt → List String
  | none => []
  | some s => E.stmtReadsV s
termination_by structural o => o

/-- `stmtReadsV` of a list. -/
def CoreMemDesign.listStmtReadsV (E : CoreMemDesign) : List PStmt → List String
  | [] => []
  | s :: ss => E.stmtReadsV s ++ E.listStmtReadsV ss
termination_by structural xs => xs

/-- `stmtReadsV` of the arms of a `case`. -/
def CoreMemDesign.itemsStmtReadsV (E : CoreMemDesign) : List (List PExpr × PStmt) → List String
  | [] => []
  | (ps, b) :: rest => E.readsListV E.env E.elems ps ++ E.stmtReadsV b ++ E.itemsStmtReadsV rest
termination_by structural xs => xs

end

/-- The arms' hit count reads only the patterns. -/
theorem CoreMemDesign.caseHitsV_congr {E : CoreMemDesign} {v v' : SvState} {mv : MemV} (sv : LVec)
    (mode : CaseMode) : ∀ (items : List (List PExpr × PStmt)),
      (∀ x ∈ E.itemsStmtReadsV items, SvState.lookup v x = SvState.lookup v' x) →
      E.caseHitsV v mv sv mode items = E.caseHitsV v' mv sv mode items
  | [], _ => rfl
  | (ps, b) :: rest, h => by
      simp only [CoreMemDesign.itemsStmtReadsV, List.mem_append] at h
      simp only [CoreMemDesign.caseHitsV]
      rw [CoreMemDesign.evalListV_congr ps (fun x hx => h x (Or.inl (Or.inl hx))),
        CoreMemDesign.caseHitsV_congr sv mode rest (fun x hx => h x (Or.inr hx))]

mutual

/-- **An edge body reads the view only where `stmtReadsV` says** (nonblocking whole-signal bodies): on two views that
agree there it issues the same updates. -/
theorem CoreMemDesign.execV_congr {E : CoreMemDesign} {v v' : SvState} {mv : MemV} :
    ∀ (b : PStmt), b.nbaWhole = true → (∀ x ∈ E.stmtReadsV b, SvState.lookup v x = SvState.lookup v' x) →
      ∀ (q : NbaQueue2) (mq : MemQV), E.execV v mv b = .ok (v, q, mq) → E.execV v' mv b = .ok (v', q, mq)
  | .nbaAssign t e, _, h, q, mq, hx => by
      simp only [CoreMemDesign.execV] at hx ⊢
      cases hw : E.scalarTarget t with
      | none => simp [hw] at hx
      | some w =>
          simp only [hw] at hx ⊢
          simp only [CoreMemDesign.stmtReadsV, hw] at h
          rw [← CoreMemDesign.evalV_congr (some w) e h]
          simp only [Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hx ⊢
          obtain ⟨x, hx1, -, rfl, rfl⟩ := hx
          exact ⟨x, hx1, by simp⟩
  | .nbaAssignL lhs e, hb, h, q, mq, hx => by
      cases lhs with
      | ident t =>
          simp only [CoreMemDesign.execV] at hx ⊢
          cases hw : E.scalarTarget t with
          | none => simp [hw] at hx
          | some w =>
              simp only [hw] at hx ⊢
              simp only [CoreMemDesign.stmtReadsV, hw] at h
              rw [← CoreMemDesign.evalV_congr (some w) e h]
              simp only [Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hx ⊢
              obtain ⟨x, hx1, -, rfl, rfl⟩ := hx
              exact ⟨x, hx1, by simp⟩
      | _ => simp [PStmt.nbaWhole] at hb
  | .ifStmt c y n, hb, h, q, mq, hx => by
      simp only [PStmt.nbaWhole, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.stmtReadsV, List.mem_append] at h
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at hx ⊢
      obtain ⟨cv, hcv, hx⟩ := hx
      refine ⟨cv, by rw [← CoreMemDesign.evalV_congr (some 1) c (fun x hx => h x (Or.inl (Or.inl hx)))]; exact hcv,
        ?_⟩
      by_cases hct : cv.condTrue = true
      · rw [if_pos hct] at hx ⊢
        exact CoreMemDesign.execV_congr y hb.1 (fun x hx => h x (Or.inl (Or.inr hx))) q mq hx
      · rw [if_neg hct] at hx ⊢
        cases n with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq, Prod.mk.injEq] at hx ⊢
            simpa using hx
        | some s =>
            simp only [CoreMemDesign.execOptV] at hx ⊢
            simp only [PStmt.optNbaWhole] at hb
            exact CoreMemDesign.execV_congr s hb.2 (fun x hx => h x (Or.inr (by simpa [CoreMemDesign.optStmtReadsV]
              using hx))) q mq hx
  | .block body, hb, h, q, mq, hx => by
      simp only [PStmt.nbaWhole] at hb
      simp only [CoreMemDesign.stmtReadsV] at h
      simp only [CoreMemDesign.execV] at hx ⊢
      exact CoreMemDesign.execListV_congr body hb h q mq hx
  | .caseStmt subject items d mode check, hb, h, q, mq, hx => by
      simp only [PStmt.nbaWhole, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.stmtReadsV, List.mem_append] at h
      have hdflt : ∀ q' mq', E.execOptV v mv d = .ok (v, q', mq') → E.execOptV v' mv d = .ok (v', q', mq') := by
        intro q' mq' hd
        cases d with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq, Prod.mk.injEq] at hd ⊢
            simpa using hd
        | some s =>
            simp only [CoreMemDesign.execOptV] at hd ⊢
            simp only [PStmt.optNbaWhole] at hb
            exact CoreMemDesign.execV_congr s hb.2 (fun x hx => h x (Or.inr (by simpa [CoreMemDesign.optStmtReadsV]
              using hx))) q' mq' hd
      have hreads : ∀ x ∈ E.itemsStmtReadsV items, SvState.lookup v x = SvState.lookup v' x :=
        fun x hx => h x (Or.inl (Or.inr hx))
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at hx ⊢
      obtain ⟨sv, hsv, hx⟩ := hx
      refine ⟨sv, by rw [← CoreMemDesign.evalV_congr none subject (fun x hx => h x (Or.inl (Or.inl hx)))]; exact hsv,
        ?_⟩
      cases check
      case none => exact CoreMemDesign.execItemsV_congr sv mode items _ _ hb.1 hreads hdflt q mq hx
      all_goals
        simp only [Res.bind_eq_ok] at hx ⊢
        obtain ⟨cn, hcn, hx⟩ := hx
        refine ⟨cn, by rw [← CoreMemDesign.caseHitsV_congr sv mode items hreads]; exact hcn, ?_⟩
        split at hx
        · rename_i hok
          rw [if_pos hok]
          exact CoreMemDesign.execItemsV_congr sv mode items _ _ hb.1 hreads hdflt q mq hx
        · simp at hx
  | .blockingAssign _ _, hb, _, _, _, _ => by simp [PStmt.nbaWhole] at hb
  | .blockingAssignL _ _, hb, _, _, _, _ => by simp [PStmt.nbaWhole] at hb
  | .forLoop .., hb, _, _, _, _ => by simp [PStmt.nbaWhole] at hb
  | .unsupported .., hb, _, _, _, _ => by simp [PStmt.nbaWhole] at hb

/-- The list form of `execV_congr`. -/
theorem CoreMemDesign.execListV_congr {E : CoreMemDesign} {v v' : SvState} {mv : MemV} :
    ∀ (bs : List PStmt), PStmt.listNbaWhole bs = true →
      (∀ x ∈ E.listStmtReadsV bs, SvState.lookup v x = SvState.lookup v' x) →
      ∀ (q : NbaQueue2) (mq : MemQV), E.execListV v mv bs = .ok (v, q, mq) → E.execListV v' mv bs = .ok (v', q, mq)
  | [], _, _, q, mq, hx => by
      simp only [CoreMemDesign.execListV, Res.ok.injEq, Prod.mk.injEq] at hx ⊢
      simpa using hx
  | s :: ss, hb, h, q, mq, hx => by
      simp only [PStmt.listNbaWhole, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.listStmtReadsV, List.mem_append] at h
      simp only [CoreMemDesign.execListV, Res.bind_eq_ok, Res.ok.injEq] at hx ⊢
      obtain ⟨⟨v1, a, ma⟩, h1, ⟨v2, b, mb⟩, h2, hq⟩ := hx
      have e1 := (CoreMemDesign.execV_nbaWhole v mv s v1 a ma hb.1 h1).1
      rw [e1] at h1 h2
      have e2 := (CoreMemDesign.execListV_nbaWhole v mv ss v2 b mb hb.2 h2).1
      rw [e2] at h2 hq
      refine ⟨(v', a, ma), CoreMemDesign.execV_congr s hb.1 (fun x hx => h x (Or.inl hx)) a ma h1, (v', b, mb),
        CoreMemDesign.execListV_congr ss hb.2 (fun x hx => h x (Or.inr hx)) b mb h2, ?_⟩
      simp only [Prod.mk.injEq] at hq ⊢
      simpa using hq

/-- The arms of a `case`, `execV_congr`'s form: the same arm is selected on both views (its patterns agree) and its
body issues the same updates. -/
theorem CoreMemDesign.execItemsV_congr {E : CoreMemDesign} {v v' : SvState} {mv : MemV} (sv : LVec)
    (mode : CaseMode) :
    ∀ (items : List (List PExpr × PStmt)) (dflt dflt' : Res ExecV), PStmt.itemsNbaWhole items = true →
      (∀ x ∈ E.itemsStmtReadsV items, SvState.lookup v x = SvState.lookup v' x) →
      (∀ q mq, dflt = .ok (v, q, mq) → dflt' = .ok (v', q, mq)) →
      ∀ (q : NbaQueue2) (mq : MemQV), E.execItemsV v mv sv mode items dflt = .ok (v, q, mq) →
        E.execItemsV v' mv sv mode items dflt' = .ok (v', q, mq)
  | [], dflt, dflt', _, _, hd, q, mq, hx => by
      simp only [CoreMemDesign.execItemsV] at hx ⊢
      exact hd q mq hx
  | (ps, b) :: rest, dflt, dflt', hb, h, hd, q, mq, hx => by
      simp only [PStmt.itemsNbaWhole, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.itemsStmtReadsV, List.mem_append] at h
      simp only [CoreMemDesign.execItemsV, Res.bind_eq_ok] at hx ⊢
      obtain ⟨vals, hvals, hx⟩ := hx
      refine ⟨vals, by rw [← CoreMemDesign.evalListV_congr ps (fun x hx => h x (Or.inl (Or.inl hx)))]; exact hvals,
        ?_⟩
      split at hx
      · rename_i hhit
        rw [if_pos hhit]
        exact CoreMemDesign.execV_congr b hb.1 (fun x hx => h x (Or.inl (Or.inr hx))) q mq hx
      · rename_i hhit
        rw [if_neg hhit]
        exact CoreMemDesign.execItemsV_congr sv mode rest dflt dflt' hb.2 (fun x hx => h x (Or.inr hx)) hd q mq hx

end

#print axioms CoreMemDesign.execV_congr

/-! ## The commit, read at one name -/

/-- One commit step: the update applied to the view (the body of `commitNba2`'s fold). -/
def commitStep (st : SvState) (u : String × Nat × LVec) : SvState :=
  match SvState.lookup st u.1 with
  | some old => SvState.set st u.1 (old.insertAt u.2.1 u.2.2)
  | none => st

theorem commitNba2_cons_step (st : SvState) (u : String × Nat × LVec) (us : NbaQueue2) :
    commitNba2 st (u :: us) = commitNba2 (commitStep st u) us := rfl

/-- One commit step changes only the name it updates. -/
theorem lookup_commitStep_ne (st : SvState) (u : String × Nat × LVec) {x : String} (h : u.1 ≠ x) :
    SvState.lookup (commitStep st u) x = SvState.lookup st x := by
  unfold commitStep
  split
  · rw [lookup_set']; simp [h]
  · rfl

/-- One commit step, read at a name, reads only that name. -/
theorem lookup_commitStep_agree {st st' : SvState} (u : String × Nat × LVec) {x : String}
    (hx : SvState.lookup st x = SvState.lookup st' x) :
    SvState.lookup (commitStep st u) x = SvState.lookup (commitStep st' u) x := by
  by_cases hu : u.1 = x
  · obtain ⟨n, lo, val⟩ := u
    simp only at hu
    subst hu
    unfold commitStep
    simp only
    rw [hx]
    cases h : SvState.lookup st' n with
    | none => simpa [h] using hx
    | some old => simp [lookup_set']
  · rw [lookup_commitStep_ne st u hu, lookup_commitStep_ne st' u hu]
    exact hx

/-- A queue of updates of `x` only, read at `x`, reads only `x`. -/
theorem commitNba2_only_at (x : String) :
    ∀ (q : NbaQueue2) (st st' : SvState), (∀ u ∈ q, u.1 = x) → SvState.lookup st x = SvState.lookup st' x →
      SvState.lookup (commitNba2 st q) x = SvState.lookup (commitNba2 st' q) x
  | [], _, _, _, h => h
  | u :: us, st, st', hq, h => by
      rw [commitNba2_cons_step, commitNba2_cons_step]
      exact commitNba2_only_at x us _ _ (fun u' hu' => hq u' (by simp [hu'])) (lookup_commitStep_agree u h)

/-- The commit, read at `x`, is the commit of the updates of `x`. -/
theorem commitNba2_filter_at (x : String) :
    ∀ (q : NbaQueue2) (st : SvState),
      SvState.lookup (commitNba2 st q) x = SvState.lookup (commitNba2 st (q.filter fun u => u.1 == x)) x
  | [], _ => rfl
  | u :: us, st => by
      by_cases hu : u.1 = x
      · have hux : (u.1 == x) = true := by simp [hu]
        rw [List.filter_cons, hux]
        simp only [ite_true]
        rw [commitNba2_cons_step, commitNba2_cons_step]
        exact commitNba2_filter_at x us _
      · have hux : (u.1 == x) = false := by simp [hu]
        rw [List.filter_cons, hux]
        simp only [Bool.false_eq_true, ite_false]
        rw [commitNba2_cons_step, commitNba2_filter_at x us _]
        exact commitNba2_only_at x _ _ _ (fun u' hu' => by simpa using (List.mem_filter.mp hu').2)
          (lookup_commitStep_ne st u hu)

/-- **The commit at one name** depends only on the updates of that name and the value before: from views that agree
at `x`, queues with the same updates of `x` commit to views that agree at `x`. -/
theorem commitNba2_agree_at (x : String) {q q' : NbaQueue2} {st st' : SvState}
    (h : SvState.lookup st x = SvState.lookup st' x)
    (hf : q.filter (fun u => u.1 == x) = q'.filter (fun u => u.1 == x)) :
    SvState.lookup (commitNba2 st q) x = SvState.lookup (commitNba2 st' q') x := by
  rw [commitNba2_filter_at x q st, commitNba2_filter_at x q' st', hf]
  exact commitNba2_only_at x _ _ _ (fun u' hu' => by simpa using (List.mem_filter.mp hu').2) h

/-! ## A domain without a crossing -/

/-- The names a continuous assign at index `i` reads, as the route evaluates it (the compiled expression's identifiers,
or for an assign that reads a memory the names `evalV` reads): `topoC`'s reading. -/
def CoreMemDesign.assignReadsAt (E : CoreMemDesign) (i : Nat) (n : String) (e : PExpr) : List String :=
  if LeanModels.Sv.PExpr.hasMemoryRead e || LeanModels.Sv.PExpr.hasFunctionCall e then
    match E.scalarWidth? n with
    | some w => E.readsV E.env E.elems (some w) e
    | none => []
  else
    match E.compiledAssigns[i]? with
    | some (some c) => c.idents
    | _ => []

/-- **A domain without a crossing**: the events `A` and the names `S` it owns. Its edge processes (those whose clock
event is in `A`) read only `S`, have their clock and reset in `S`; every other edge process writes nothing in `S`; a
continuous assign into `S` reads only `S`; every edge body is nonblocking to whole signals (the obligations' form for
several edge processes). -/
structure CoreMemDesign.Domain (E : CoreMemDesign) (A : List SeqEvent) (S : List String) : Prop where
  reads : ∀ f, CoreMemProc.edge f ∈ E.processes.toList → f.clockEvent ∈ A → ∀ x ∈ E.stmtReadsV f.body, x ∈ S
  clock : ∀ f, CoreMemProc.edge f ∈ E.processes.toList → f.clockEvent ∈ A → f.clock ∈ S
  reset : ∀ f, CoreMemProc.edge f ∈ E.processes.toList → f.clockEvent ∈ A → ∀ r, f.reset = some r → r ∈ S
  others : ∀ f, CoreMemProc.edge f ∈ E.processes.toList → f.clockEvent ∉ A → ∀ x ∈ f.body.writes, x ∉ S
  assigns : ∀ i n e, E.processes[i]? = some (.assign (.ident n) e) → n ∈ S → ∀ x ∈ E.assignReadsAt i n e, x ∈ S
  whole : ∀ f, CoreMemProc.edge f ∈ E.processes.toList → f.body.nbaWhole = true

/-- Two views agree on the names `S`. -/
def AgreeOn (S : List String) (a b : SvState) : Prop := ∀ x ∈ S, SvState.lookup a x = SvState.lookup b x

/-- A settle pass keeps two raw views' agreement on a domain's names (its assigns read only them). -/
theorem CoreMemDesign.settleRaw_domain {E : CoreMemDesign} {A : List SeqEvent} {S : List String} (hD : E.Domain A S)
    {mv : MemV} :
    ∀ (procs : List CoreMemProc) (idx : Nat), (∀ k p, procs[k]? = some p → E.processes[idx + k]? = some p) →
      ∀ (r1 r2 r1' r2' : SvState), AgreeOn S r1 r2 → E.settleRaw mv r1 idx procs = .ok r1' →
        E.settleRaw mv r2 idx procs = .ok r2' → AgreeOn S r1' r2'
  | [], _, _, r1, r2, r1', r2', h, h1, h2 => by
      simp only [CoreMemDesign.settleRaw, Res.ok.injEq] at h1 h2
      subst h1; subst h2; exact h
  | p :: rest, idx, hidx, r1, r2, r1', r2', h, h1, h2 => by
      have hp : E.processes[idx]? = some p := by simpa using hidx 0 p rfl
      have hrest : ∀ k q, rest[k]? = some q → E.processes[idx + 1 + k]? = some q := by
        intro k q hq
        have := hidx (k + 1) q (by simpa using hq)
        rwa [show idx + (k + 1) = idx + 1 + k by omega] at this
      -- the continuation from two set views
      have hset : ∀ (n : String) (y1 y2 : LVec), (n ∈ S → y1 = y2) →
          AgreeOn S (SvState.set r1 n y1) (SvState.set r2 n y2) := by
        intro n y1 y2 hy x hx
        rw [lookup_set', lookup_set']
        by_cases hnx : n = x
        · subst hnx; simp [hy hx]
        · simp only [hnx, ↓reduceIte]; exact h x hx
      cases p with
      | assign t e =>
          cases t with
          | ident n =>
              have hreads := hD.assigns idx n e hp
              simp only [CoreMemDesign.settleRaw] at h1 h2
              split at h1
              · rename_i hm
                simp only [hm, ↓reduceIte] at h2
                cases hw : E.scalarWidth? n with
                | none => simp [hw] at h1
                | some w =>
                    simp only [hw, Res.bind_eq_ok] at h1 h2
                    obtain ⟨y1, hy1, h1⟩ := h1
                    obtain ⟨y2, hy2, h2⟩ := h2
                    refine CoreMemDesign.settleRaw_domain hD rest (idx + 1) hrest _ _ r1' r2' (hset n y1 y2 ?_) h1 h2
                    intro hn
                    have hag : ∀ x ∈ E.readsV E.env E.elems (some w) e,
                        SvState.lookup (E.matV r1) x = SvState.lookup (E.matV r2) x := by
                      intro x hx
                      apply CoreMemDesign.lookup_matV_congr
                      apply h x
                      apply hreads hn x
                      simp [CoreMemDesign.assignReadsAt, hm, hw, hx]
                    rw [CoreMemDesign.evalV_congr (some w) e hag] at hy1
                    rw [hy1] at hy2
                    exact (Res.ok.inj hy2)
              · rename_i hm
                simp only [hm, Bool.false_eq_true, ↓reduceIte] at h2
                cases hc : E.compiledAssigns[idx]? with
                | none => simp [hc] at h1
                | some oc =>
                    cases oc with
                    | none => simp [hc] at h1
                    | some c =>
                        simp only [hc, Res.bind_eq_ok] at h1 h2
                        obtain ⟨y1, hy1, h1⟩ := h1
                        obtain ⟨y2, hy2, h2⟩ := h2
                        refine CoreMemDesign.settleRaw_domain hD rest (idx + 1) hrest _ _ r1' r2'
                          (hset n y1 y2 ?_) h1 h2
                        intro hn
                        have hag : ∀ x ∈ c.idents, SvState.lookup r1 x = SvState.lookup r2 x := by
                          intro x hx
                          apply h x
                          apply hreads hn x
                          simp [CoreMemDesign.assignReadsAt, hm, hc, hx]
                        rw [evalPure2_congr hag] at hy1
                        rw [hy1] at hy2
                        exact (Res.ok.inj hy2)
          | _ => simp [CoreMemDesign.settleRaw] at h1
      | edge f =>
          simp only [CoreMemDesign.settleRaw] at h1 h2
          exact CoreMemDesign.settleRaw_domain hD rest (idx + 1) hrest r1 r2 r1' r2' h h1 h2
      | initial _ => simp [CoreMemDesign.settleRaw] at h1
      | comb _ => simp [CoreMemDesign.settleRaw] at h1
      | implicit _ => simp [CoreMemDesign.settleRaw] at h1
      | latch _ => simp [CoreMemDesign.settleRaw] at h1
      | unsupported _ _ => simp [CoreMemDesign.settleRaw] at h1

/-- A settle keeps two views' agreement on a domain's names. -/
theorem CoreMemDesign.settleV_domain {E : CoreMemDesign} {A : List SeqEvent} {S : List String} (hD : E.Domain A S)
    {mv : MemV} {a b a' b' : SvState} (h : AgreeOn S a b) (h1 : E.settleV mv a = .ok a')
    (h2 : E.settleV mv b = .ok b') : AgreeOn S a' b' := by
  simp only [CoreMemDesign.settleV, Res.bind_eq_ok, Res.ok.injEq] at h1 h2
  obtain ⟨r1, hr1, rfl⟩ := h1
  obtain ⟨r2, hr2, rfl⟩ := h2
  intro x hx
  exact CoreMemDesign.lookup_matV_congr
    (CoreMemDesign.settleRaw_domain hD _ 0 (fun k p hk => by simpa using hk) a b r1 r2 h hr1 hr2 x hx)

/-- The edge pass of a domain: on views that agree on its names (and from start views that agree there) its
processes fire together and issue the same updates, and no other process updates its names. -/
theorem CoreMemDesign.edgesV_domain {E : CoreMemDesign} {A : List SeqEvent} {S : List String} (hD : E.Domain A S)
    {mv : MemV} {b1 b2 p1 p2 : SvState} (hb : AgreeOn S b1 b2) (hp : AgreeOn S p1 p2) :
    ∀ (procs : List CoreMemProc), (∀ q ∈ procs, q ∈ E.processes.toList) → ∀ (r1 r2 : ExecV),
      E.edgesV b1 p1 p1 mv procs = .ok r1 → E.edgesV b2 p2 p2 mv procs = .ok r2 →
        ∀ x ∈ S, r1.2.1.filter (fun u => u.1 == x) = r2.2.1.filter (fun u => u.1 == x)
  | [], _, r1, r2, h1, h2, x, _ => by
      simp only [CoreMemDesign.edgesV, Res.ok.injEq] at h1 h2
      subst h1; subst h2; rfl
  | q :: rest, hq, r1, r2, h1, h2, x, hx => by
      have hrest : ∀ q' ∈ rest, q' ∈ E.processes.toList := fun q' h' => hq q' (by simp [h'])
      have hmem := hq q (by simp)
      cases q with
      | edge f =>
          have hw := hD.whole f hmem
          have hw' : (CoreMemProc.edge f).nbaWholeP = true := by simpa [CoreMemProc.nbaWholeP] using hw
          obtain ⟨qa, rr1, hqa, hna, he1, rfl⟩ := CoreMemDesign.edgesV_cons_inv hw' h1
          obtain ⟨qb, rr2, hqb, hnb, he2, rfl⟩ := CoreMemDesign.edgesV_cons_inv hw' h2
          have ih := CoreMemDesign.edgesV_domain hD hb hp rest hrest rr1 rr2 he1 he2 x hx
          simp only [List.filter_append, ih]
          congr 1
          by_cases hA : f.clockEvent ∈ A
          · -- the domain's process: it fires on both views or on neither, with the same updates
            have hc := hD.clock f hmem hA
            have hfire : f.fires b1 p1 = f.fires b2 p2 := by
              unfold CoreMemEdge.fires
              rw [SvState.bit0_congr (hb _ hc), SvState.bit0_congr (hp _ hc)]
              cases hr : f.reset with
              | none => rfl
              | some r =>
                  have hr' := hD.reset f hmem hA r hr
                  simp only [SvState.bit0_congr (hb _ hr'), SvState.bit0_congr (hp _ hr')]
            simp only [CoreMemDesign.procQ] at hqa hqb
            rw [← hfire] at hqb
            split at hqa
            · rename_i hf
              rw [if_pos hf] at hqb
              simp only [Res.bind_eq_ok, Res.ok.injEq] at hqa hqb
              obtain ⟨⟨v1, a1, m1⟩, ha1, rfl⟩ := hqa
              obtain ⟨⟨v2, a2, m2⟩, ha2, rfl⟩ := hqb
              obtain ⟨rfl, -, -⟩ := CoreMemDesign.execV_nbaWhole p1 mv f.body v1 a1 m1 hw ha1
              have hc2 := CoreMemDesign.execV_congr (v' := p2) f.body hw
                (fun y hy => hp y (hD.reads f hmem hA y hy)) a1 m1 ha1
              rw [hc2] at ha2
              simp only [Res.ok.injEq, Prod.mk.injEq] at ha2
              rw [ha2.2.1]
            · rename_i hf
              rw [if_neg hf] at hqb
              simp only [Res.ok.injEq] at hqa hqb
              subst hqa; subst hqb; rfl
          · -- another domain's process: none of its updates names `x`
            have hnot : ∀ (qq : NbaQueue2), (∀ u ∈ qq, u.1 ∈ (CoreMemProc.edge f).targets) →
                qq.filter (fun u => u.1 == x) = [] := by
              intro qq hqq
              rw [List.filter_eq_nil_iff]
              intro u hu
              have := hqq u hu
              simp only [CoreMemProc.targets, List.mem_eraseDups] at this
              have hux : u.1 ≠ x := fun he => hD.others f hmem hA u.1 this (he ▸ hx)
              simpa using hux
            rw [hnot qa hna, hnot qb hnb]
      | assign t e =>
          simp only [CoreMemDesign.edgesV] at h1 h2
          exact CoreMemDesign.edgesV_domain hD hb hp rest hrest r1 r2 h1 h2 x hx
      | initial _ =>
          simp only [CoreMemDesign.edgesV] at h1 h2
          exact CoreMemDesign.edgesV_domain hD hb hp rest hrest r1 r2 h1 h2 x hx
      | comb _ =>
          simp only [CoreMemDesign.edgesV] at h1 h2
          exact CoreMemDesign.edgesV_domain hD hb hp rest hrest r1 r2 h1 h2 x hx
      | implicit _ =>
          simp only [CoreMemDesign.edgesV] at h1 h2
          exact CoreMemDesign.edgesV_domain hD hb hp rest hrest r1 r2 h1 h2 x hx
      | latch _ =>
          simp only [CoreMemDesign.edgesV] at h1 h2
          exact CoreMemDesign.edgesV_domain hD hb hp rest hrest r1 r2 h1 h2 x hx
      | unsupported _ _ =>
          simp only [CoreMemDesign.edgesV] at h1 h2
          exact CoreMemDesign.edgesV_domain hD hb hp rest hrest r1 r2 h1 h2 x hx

/-- The edge pass of nonblocking whole-signal processes leaves the view and the memory alone. -/
theorem CoreMemDesign.edgesV_whole {E : CoreMemDesign} {A : List SeqEvent} {S : List String} (hD : E.Domain A S)
    {mv : MemV} {b p : SvState} {r : ExecV} (h : E.edgesV b p p mv E.processes.toList = .ok r) :
    r.1 = p ∧ r.2.2 = [] :=
  CoreMemDesign.edgesV_view (fun q hq => by
    cases q with
    | edge f => simpa [CoreMemProc.nbaWholeP] using hD.whole f hq
    | _ => rfl) h

/-- **THE DOMAIN'S SLOT**: two slots on views that agree on a domain's names, on rows that apply the same values to
them, with one memory view, land on views that agree on the domain's names (whatever the rest of the design holds, and
whatever the other clocks do in the row); the memory view is unchanged. -/
theorem CoreMemDesign.slotV_domain {E : CoreMemDesign} {A : List SeqEvent} {S : List String} (hD : E.Domain A S)
    {v w r r' v1 w1 : SvState} {mv mv1 mw1 : MemV} (hvw : AgreeOn S v w)
    (hr : AgreeOn S (E.applyRow v r) (E.applyRow w r'))
    (h1 : E.slotV v mv r = .ok (v1, mv1)) (h2 : E.slotV w mv r' = .ok (w1, mw1)) :
    AgreeOn S v1 w1 ∧ mv1 = mv ∧ mw1 = mv := by
  simp only [CoreMemDesign.slotV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at h1 h2
  obtain ⟨p0, hp0, p, hp, rr, hrr, s1, hs1, s2, hs2, rfl, rfl⟩ := h1
  obtain ⟨q0, hq0, q, hq, rq, hrq, t1, ht1, t2, ht2, rfl, rfl⟩ := h2
  have a0 := CoreMemDesign.settleV_domain hD hr hp0 hq0
  have a1 := CoreMemDesign.settleV_domain hD a0 hp hq
  obtain ⟨hrr1, hrr2⟩ := CoreMemDesign.edgesV_whole hD hrr
  obtain ⟨hrq1, hrq2⟩ := CoreMemDesign.edgesV_whole hD hrq
  have hf := CoreMemDesign.edgesV_domain hD hvw a1 E.processes.toList (fun _ h => h) rr rq hrr hrq
  rw [hrr2] at hs1 hs2
  rw [hrq2] at ht1 ht2
  have ac : AgreeOn S (commitNba2 rr.1 rr.2.1) (commitNba2 rq.1 rq.2.1) := by
    intro x hx
    rw [hrr1, hrq1]
    exact commitNba2_agree_at x (a1 x hx) (hf x hx)
  have a2 := CoreMemDesign.settleV_domain hD ac hs1 ht1
  exact ⟨CoreMemDesign.settleV_domain hD a2 hs2 ht2, by rw [hrr2]; rfl, by rw [hrq2]; rfl⟩

#print axioms CoreMemDesign.slotV_domain

/-- Two row lists that bind the same values to the names `S`, row by row. -/
def RowsAgreeOn (S : List String) : List SvState → List SvState → Prop
  | [], [] => True
  | r :: rs, r' :: rs' => (∀ x ∈ S, SvState.lookup r x = SvState.lookup r' x) ∧ RowsAgreeOn S rs rs'
  | _, _ => False

/-- Rows that bind the same values to `S` apply the same values to views that agree on `S`. -/
theorem CoreMemDesign.applyRow_agreeOn {E : CoreMemDesign} (h4 : AllFour E.scalar) {S : List String}
    {v w r r' : SvState} (hvw : AgreeOn S v w) (hr : ∀ x ∈ S, SvState.lookup r x = SvState.lookup r' x) :
    AgreeOn S (E.applyRow v r) (E.applyRow w r') := by
  intro x hx
  rw [CoreMemDesign.lookup_applyRow h4, CoreMemDesign.lookup_applyRow h4, hr x hx, hvw x hx]

/-- **THE DOMAIN'S RUN**: two view-level runs from views that agree on a domain's names, with one memory view, on row
lists that bind the same values to them row by row, agree on the domain's names sample by sample. -/
theorem CoreMemDesign.runRV_domain {E : CoreMemDesign} (hP : E.SeqProfileI) {A : List SeqEvent} {S : List String}
    (hD : E.Domain A S) :
    ∀ (rows rows' : List SvState) (σ σ' : SvState × MemV) (tr tr' : List (SvState × MemV)),
      AgreeOn S σ.1 σ'.1 → σ.2 = σ'.2 → RowsAgreeOn S rows rows' → E.runRV σ rows = .ok tr →
      E.runRV σ' rows' = .ok tr' → tr.length = tr'.length ∧
        ∀ (k : Nat) (s s' : SvState × MemV), tr[k]? = some s → tr'[k]? = some s' → AgreeOn S s.1 s'.1
  | [], [], _, _, tr, tr', _, _, _, h1, h2 => by
      simp only [CoreMemDesign.runRV, Res.ok.injEq] at h1 h2
      subst h1; subst h2
      exact ⟨rfl, fun k s s' h _ => by simp at h⟩
  | r :: rs, r' :: rs', ⟨v, mv⟩, ⟨w, mw⟩, tr, tr', hag, hm, ⟨hr, hrs⟩, h1, h2 => by
      simp only at hag hm
      subst hm
      simp only [CoreMemDesign.runRV, Res.bind_eq_ok, Res.ok.injEq] at h1 h2
      obtain ⟨⟨v1, m1⟩, hs1, rest, hrest, rfl⟩ := h1
      obtain ⟨⟨w1, n1⟩, hs2, rest', hrest', rfl⟩ := h2
      obtain ⟨a1, hm1, hn1⟩ := CoreMemDesign.slotV_domain hD hag (CoreMemDesign.applyRow_agreeOn hP.four hag hr)
        hs1 hs2
      rw [hm1] at hrest
      rw [hn1] at hrest'
      obtain ⟨hlen, hall⟩ := CoreMemDesign.runRV_domain hP hD rs rs' (v1, mv) (w1, mv) rest rest' a1 rfl hrs
        hrest hrest'
      refine ⟨by simp [hlen], fun k s s' hk hk' => ?_⟩
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk hk'
          subst hk; subst hk'
          exact a1
      | succ k =>
          simp only [List.getElem?_cons_succ] at hk hk'
          exact hall k s s' hk hk'
  | [], _ :: _, _, _, _, _, _, _, h, _, _ => absurd h (by simp [RowsAgreeOn])
  | _ :: _, [], _, _, _, _, _, _, h, _, _ => absurd h (by simp [RowsAgreeOn])

#print axioms CoreMemDesign.runRV_domain

/-- A row restricted to the names `S` (the other domains' clocks and data dropped: held). -/
def projRow (S : List String) (r : SvState) : SvState := r.filter fun m => decide (m.1 ∈ S)

theorem lookup_projRow (S : List String) : ∀ (r : SvState) (x : String), x ∈ S →
    SvState.lookup (projRow S r) x = SvState.lookup r x
  | [], _, _ => rfl
  | (k, val) :: rest, x, hx => by
      by_cases hk : k ∈ S
      · simp only [projRow, List.filter_cons, hk, decide_true, ite_true, SvState.lookup]
        split
        · rfl
        · exact lookup_projRow S rest x hx
      · have hkx : (k == x) = false := by
          have : k ≠ x := fun h => hk (h ▸ hx)
          simpa using this
        simp only [projRow, List.filter_cons, hk, decide_false, Bool.false_eq_true, ite_false, SvState.lookup,
          hkx, ↓reduceIte]
        exact lookup_projRow S rest x hx

theorem rowsAgreeOn_proj (S : List String) : ∀ rows : List SvState, RowsAgreeOn S rows (rows.map (projRow S))
  | [] => trivial
  | r :: rs => ⟨fun x hx => (lookup_projRow S r x hx).symm, rowsAgreeOn_proj S rs⟩

/-- **A RUN PROJECTS TO ITS DOMAIN'S RUN**: on a domain's names, a run of the whole design (every other clock doing
what it does: interleaved, coincident, stopped) is the run in which every row binds only the domain's names (the other
clocks stopped, their data held). So a theorem about the domain's run alone transfers unchanged. -/
theorem CoreMemDesign.runRV_project {E : CoreMemDesign} (hP : E.SeqProfileI) {A : List SeqEvent}
    {S : List String} (hD : E.Domain A S) {rows : List SvState} {σ : SvState × MemV} {tr tr' : List (SvState × MemV)}
    (h1 : E.runRV σ rows = .ok tr) (h2 : E.runRV σ (rows.map (projRow S)) = .ok tr') :
    tr.length = tr'.length ∧
      ∀ (k : Nat) (s s' : SvState × MemV), tr[k]? = some s → tr'[k]? = some s' → AgreeOn S s.1 s'.1 :=
  CoreMemDesign.runRV_domain hP hD rows _ σ σ tr tr' (fun _ _ => rfl) rfl (rowsAgreeOn_proj S rows) h1 h2

/-- **THE ROUTE'S RUN, BY DOMAIN**: two runs of the route from coherent states whose views agree on a domain's names
(one memory view), on row lists binding the same values to them row by row: when the view-level runs succeed, the
route's runs succeed and agree on the domain's names sample by sample. -/
theorem CoreMemDesign.runRows_domain {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    {A : List SeqEvent} {S : List String} (hD : E.Domain A S) {st st' : CoreMemState} (hc : E.Coherent st)
    (hc' : E.Coherent st') (hmc : E.MemCoherent st.memory) (hmc' : E.MemCoherent st'.memory)
    (hag : AgreeOn S (E.scalar.view st.scalar) (E.scalar.view st'.scalar)) (hm : E.memOf st.memory = E.memOf st'.memory)
    {rows rows' : List SvState} (hrows : RowsAgreeOn S rows rows')
    (hty : ∀ r ∈ rows, r ≠ [] ∧ EntryTyped E.scalar.toDesign2 r)
    (hty' : ∀ r ∈ rows', r ≠ [] ∧ EntryTyped E.scalar.toDesign2 r) {tr tr' : List (SvState × MemV)}
    (h1 : E.runRV (E.scalar.view st.scalar, E.memOf st.memory) rows = .ok tr)
    (h2 : E.runRV (E.scalar.view st'.scalar, E.memOf st'.memory) rows' = .ok tr') :
    ∃ outs outs', runCoreMemRows E st rows = .ok outs ∧ runCoreMemRows E st' rows' = .ok outs' ∧
      outs.length = outs'.length ∧ ∀ (k : Nat) (s s' : CoreMemState), outs[k]? = some s → outs'[k]? = some s' →
        AgreeOn S (E.scalar.view s.scalar) (E.scalar.view s'.scalar) := by
  obtain ⟨outs, ho, hmap⟩ := CoreMemDesign.runRows_slots hP hO rows st tr hc hmc hty h1
  obtain ⟨outs', ho', hmap'⟩ := CoreMemDesign.runRows_slots hP hO rows' st' tr' hc' hmc' hty' h2
  obtain ⟨hlen, hall⟩ := CoreMemDesign.runRV_domain hP hD rows rows' _ _ tr tr' hag hm hrows h1 h2
  refine ⟨outs, outs', ho, ho', by rw [← List.length_map (f := fun s => (E.scalar.view s.scalar, E.memOf s.memory)),
    hmap, hlen, ← hmap', List.length_map], fun k s s' hk hk' => ?_⟩
  have e1 : tr[k]? = some (E.scalar.view s.scalar, E.memOf s.memory) := by rw [← hmap]; simp [hk]
  have e2 : tr'[k]? = some (E.scalar.view s'.scalar, E.memOf s'.memory) := by rw [← hmap']; simp [hk']
  exact hall k _ _ e1 e2

#print axioms CoreMemDesign.runRows_domain

/-! ## Coincident instants of two domains commute -/

theorem SvState.lookup_append (a b : SvState) (x : String) :
    SvState.lookup (a ++ b) x = (SvState.lookup a x).or (SvState.lookup b x) := by
  induction a with
  | nil => simp [SvState.lookup]
  | cons kv rest ih =>
      obtain ⟨k, w⟩ := kv
      simp only [List.cons_append, SvState.lookup]
      split <;> simp [ih]

theorem Instant.lookup_row_none {i : Instant} {x : String} (h : ∀ m ∈ i, m.1 ≠ x) :
    SvState.lookup i.row x = none := by
  induction i with
  | nil => rfl
  | cons m ms ih =>
      have hm : (m.1 == x) = false := by simpa using h m (by simp)
      simp only [Instant.row, List.map_cons, SvState.lookup, hm, Bool.false_eq_true, ↓reduceIte]
      exact ih fun m' hm' => h m' (by simp [hm'])

/-- The empty row applies nothing. -/
theorem applyInputs2_nil (d : Design2) (st : SvState) : applyInputs2 d [] st = st := by
  unfold applyInputs2
  have h : ∀ (l : List Decl) (s : SvState), l.foldl (fun s dc => if dc.isInput then
      (match SvState.lookup [] dc.name with
        | some v => SvState.set s dc.name (if dc.twoState then v.toTwoState else v)
        | none => s) else s) s = s := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons dc ds ih =>
        intro s
        simp only [List.foldl_cons]
        rw [show (if dc.isInput then (match SvState.lookup [] dc.name with
            | some v => SvState.set s dc.name (if dc.twoState then v.toTwoState else v)
            | none => s) else s) = s by split <;> rfl]
        exact ih s
  rw [← Array.foldl_toList]
  exact h _ _

/-- An edge pass in which no process fires issues nothing. -/
theorem CoreMemDesign.edgesV_quiet {E : CoreMemDesign} {b a v : SvState} {mv : MemV} :
    ∀ (procs : List CoreMemProc), (∀ f, CoreMemProc.edge f ∈ procs → f.fires b a = false) →
      E.edgesV b a v mv procs = .ok (v, [], [])
  | [], _ => rfl
  | p :: rest, h => by
      have hrest : ∀ f, CoreMemProc.edge f ∈ rest → f.fires b a = false := fun f hf => h f (by simp [hf])
      cases p with
      | edge f =>
          simp only [CoreMemDesign.edgesV, h f (by simp), Bool.false_eq_true, ↓reduceIte]
          exact CoreMemDesign.edgesV_quiet rest hrest
      | _ =>
          simp only [CoreMemDesign.edgesV]
          exact CoreMemDesign.edgesV_quiet rest hrest

/-- **The empty row's slot is the identity** on a settled view. -/
theorem CoreMemDesign.slotV_nil {E : CoreMemDesign} {v : SvState} {mv : MemV} (hs : E.settleV mv v = .ok v) :
    E.slotV v mv [] = .ok (v, mv) := by
  unfold CoreMemDesign.slotV
  rw [applyInputs2_nil, hs]
  simp only [Res.ok_bind]
  rw [hs]
  simp only [Res.ok_bind]
  rw [CoreMemDesign.edgesV_quiet _ (fun f _ => CoreMemEdge.fires_of_agree rfl fun _ _ => rfl)]
  simp only [Res.ok_bind]
  show (do let s1 ← E.settleV mv (commitNba2 v []); let s2 ← E.settleV mv s1; .ok (s2, mv)) = _
  rw [show commitNba2 v [] = v from rfl, hs]
  simp only [Res.ok_bind]
  rw [hs]
  rfl

/-- A slot's result is a settled view. -/
theorem CoreMemDesign.slotV_settled {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    {v r v1 : SvState} {mv mv1 : MemV} (h : E.slotV v mv r = .ok (v1, mv1)) : E.settleV mv1 v1 = .ok v1 := by
  simp only [CoreMemDesign.slotV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨p0, -, p, -, rr, -, s1, hs1, s2, hs2, rfl, rfl⟩ := h
  exact CoreMemDesign.settleV_idem (CoreMemDesign.seqOblI_spec hO).2.1
    (CoreMemDesign.matV_settleV hP.names hP.four hs1) hs2

/-- The materialized view has no name the design does not declare. -/
theorem CoreMemDesign.lookup_matV_none {E : CoreMemDesign} (r : SvState) {x : String}
    (hx : x ∉ E.scalar.decls.toList.map Decl.name) : SvState.lookup (E.matV r) x = none := by
  unfold CoreMemDesign.matV
  generalize E.scalar.decls.toList = ds at hx ⊢
  induction ds with
  | nil => rfl
  | cons dc ds ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at hx
      have hne : (dc.name == x) = false := by simpa using fun h => hx.1 h.symm
      simp only [List.map_cons, SvState.lookup, hne, Bool.false_eq_true, ↓reduceIte]
      exact ih hx.2

/-- A slot's result is a materialized view. -/
theorem CoreMemDesign.slotV_matV {E : CoreMemDesign} (hP : E.SeqProfileI) {v r v1 : SvState} {mv mv1 : MemV}
    (h : E.slotV v mv r = .ok (v1, mv1)) : E.matV v1 = v1 := by
  simp only [CoreMemDesign.slotV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨p0, -, p, -, rr, -, s1, -, s2, hs2, rfl, rfl⟩ := h
  exact CoreMemDesign.matV_settleV hP.names hP.four hs2

/-- **COINCIDENT INSTANTS OF TWO DOMAINS COMMUTE**: on a design partitioned into two domains without a crossing
(every name owned by one of them), from a settled view, the instant moving both domains' sources at once is the first
domain's instant followed by the second's: the same view, name by name, and the same memory view. -/
theorem CoreMemDesign.tick_comm {E : CoreMemDesign} (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    {A B : List SeqEvent} {SA SB : List String} (hA : E.Domain A SA) (hB : E.Domain B SB)
    (hcover : ∀ x ∈ E.scalar.decls.toList.map Decl.name, x ∈ SA ∨ x ∈ SB) {σ : SvState × MemV}
    (hs : E.settleV σ.2 σ.1 = .ok σ.1)
    {iA iB : Instant} (hiA : ∀ m ∈ iA, m.1 ∉ SB) (hiB : ∀ m ∈ iB, m.1 ∉ SA)
    {σ1 σA σ2 : SvState × MemV} (h : E.tick (iA ++ iB) σ = .ok σ1) (h1 : E.tick iA σ = .ok σA)
    (h2 : E.tick iB σA = .ok σ2) :
    (∀ x, SvState.lookup σ1.1 x = SvState.lookup σ2.1 x) ∧ σ1.2 = σ2.2 := by
  obtain ⟨v, mv⟩ := σ
  obtain ⟨v1, m1⟩ := σ1
  obtain ⟨vA, mA⟩ := σA
  obtain ⟨v2, m2⟩ := σ2
  simp only [CoreMemDesign.tick] at h h1 h2 hs
  have hrowapp : (iA ++ iB).row = iA.row ++ iB.row := List.map_append
  rw [hrowapp] at h
  have hnone : ∀ (i : Instant) (S : List String), (∀ m ∈ i, m.1 ∉ S) → ∀ x ∈ S, SvState.lookup i.row x = none :=
    fun i S hi x hx => Instant.lookup_row_none fun m hm he => hi m hm (he ▸ hx)
  have hrefl : ∀ (S : List String) (a : SvState), AgreeOn S a a := fun _ _ _ _ => rfl
  -- the second instant's slot starts from a settled view, with the memory view unchanged
  have hsA : E.settleV mA vA = .ok vA := CoreMemDesign.slotV_settled hP hO h1
  -- the A part
  obtain ⟨aA1, hm1, hmA⟩ := CoreMemDesign.slotV_domain hA (hrefl SA v)
    (CoreMemDesign.applyRow_agreeOn hP.four (hrefl SA v) fun x hx => by
      rw [SvState.lookup_append, hnone iB SA hiB x hx]; cases SvState.lookup iA.row x <;> rfl) h h1
  subst hm1
  subst hmA
  obtain ⟨aA2, hm2, -⟩ := CoreMemDesign.slotV_domain hA (hrefl SA vA)
    (CoreMemDesign.applyRow_agreeOn hP.four (hrefl SA vA) fun x hx => by
      rw [hnone iB SA hiB x hx]; rfl) h2 (CoreMemDesign.slotV_nil hsA)
  -- the B part: the first instant leaves B's names alone
  obtain ⟨aB0, -, -⟩ := CoreMemDesign.slotV_domain hB (hrefl SB v)
    (CoreMemDesign.applyRow_agreeOn hP.four (hrefl SB v) fun x hx => by
      rw [hnone iA SB hiA x hx]; rfl) h1 (CoreMemDesign.slotV_nil hs)
  obtain ⟨aB, -, -⟩ := CoreMemDesign.slotV_domain hB (fun x hx => (aB0 x hx).symm)
    (CoreMemDesign.applyRow_agreeOn hP.four (fun x hx => (aB0 x hx).symm) fun x hx => by
      rw [SvState.lookup_append, hnone iA SB hiA x hx]; rfl) h h2
  refine ⟨fun x => ?_, by simp only; rw [hm2]⟩
  by_cases hdx : x ∈ E.scalar.decls.toList.map Decl.name
  · rcases hcover x hdx with hx | hx
    · exact (aA1 x hx).trans (aA2 x hx).symm
    · exact aB x hx
  · show SvState.lookup v1 x = SvState.lookup v2 x
    rw [← CoreMemDesign.slotV_matV hP h, ← CoreMemDesign.slotV_matV hP h2, CoreMemDesign.lookup_matV_none _ hdx,
      CoreMemDesign.lookup_matV_none _ hdx]

#print axioms CoreMemDesign.tick_comm

end LeanModels.Sv.Kernel
