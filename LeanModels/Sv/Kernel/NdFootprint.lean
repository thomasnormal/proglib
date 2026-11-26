import LeanModels.Sv.Kernel.NdConfluence

/-! # Non-interference as a property of the design (the footprint test)

`NdConfluence.lean` proves that a NON-INTERFERING start state of one event has
one observable outcome (`Nd.settled_view`).  There the condition
`Nd.NonInterfering` is stated per start state.  This file gives a condition
on the DESIGN, decided by a `Bool` test on the loaded design, proves that it
implies `Nd.NonInterfering` at every admissible start state of every event,
and derives the event as a function on scalar views.

## The design-level condition (`CoreMemDesign.NdFootprint`)

`E.ndFootprintOk : Bool`, computed from the write and read footprints of the
process bodies, together with the structural equation `edgeBase`
(`rfl` on a loaded design):

* every process is an edge or event process, there is no resolved net,
  `$readmemh` or declaration initializer (`E.ndAdmitted`), no memory, every
  scalar declaration is four-state and the declared names are distinct;
* **writes**: every process body is built from `begin ... end`, `if` and
  nonblocking assignments to a WHOLE signal (`PStmt.footOk`).  So there is no
  blocking write at all: no process reads what another one writes in the same
  event through a blocking write.  (Blocking writes to process-local targets
  are the next widening; they are not in this test.)
* **no write to a control signal**: no assignment targets a clock or event
  source of any process (`E.ndEventSources`);
* **one write per target on every path**: inside one body, two statements of
  one `begin ... end` never name the same target (the two branches of an `if`
  may);
* **pairwise disjoint write targets**: the write footprints
  (`CoreMemProc.footWrites`) of two different processes share no name
  (`footDisjoint`).  This is asked of ALL pairs of processes, not only of
  those one event wakes together; it is a sufficient condition, and it
  rejects two processes on different clocks that write one signal.
* no x observer (`===`, `!==`, `==?`, `!=?`) and no function call in a
  condition or a right-hand side.

## Admissible start states: where the event is a function (`eventV`)

`E.eventV v row : Option SvState` is a total, fuel-free function on scalar
views.  It answers `none` exactly when one of the following holds, and each
is one of the relation's own refusals or oracle sites:

* the row binds an input at a width other than the declared one;
* a clock or event source is x/z before or after the row's inputs (the
  relation refuses it; open owner question "x on a control value", interim
  option: refused, statements assume control signals known);
* an `if` condition met on the path evaluates to a value with an unknown bit
  (an oracle site: there the outcome really depends on the oracle, so no
  function exists);
* the expression evaluator refuses a condition or a right-hand side.

Otherwise it answers `some v'`: the inputs applied first (interim option
"inputs-first within a row"), the woken processes' updates collected on that
view (each read sees the view after the inputs, because no body changes the
store before the commit), and the updates committed at once (interim option
"atomic non-blocking commit").

## What is proved

* `CoreMemDesign.NdFootprint.nonInterfering`: on a design that passes the
  test, at every coherent store and row where `eventQueueV` is defined, the
  start state of the event satisfies `Nd.NonInterfering`, under every oracle.
* `CoreMemDesign.NdFootprint.event_view`: then EVERY settled outcome of the
  event, for every oracle and every schedule, has the scalar view
  `E.eventV (view of the start store) row`, and its store is coherent.
* `CoreMemDesign.NdFootprint.event_exists`: a settled outcome exists.
* `CoreMemDesign.NdFootprint.event_view_unique`: one observable view.

The step of the relation cuts at every parser node (open owner question
"granularity"); the process-atomic, functional reading of an event is DERIVED
here under the footprint test, never assumed.  Operand reads of an unknown,
ternary conditions and select indices keep the four-state merge of the reused
evaluator (open owner question); only `if` conditions are oracle sites.
Elaboration is outside the relation.

## Limits

* The observable is the scalar view.  Designs with memories are outside the
  test.
* `for` loops are outside the test (a loop of whole-signal nonblocking
  assignments writes one target more than once).
* One NBA round per event (no write to a clock).
* The test does not look at which processes can be woken together.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Write footprints and the syntactic test on a body -/

mutual

/-- The write footprint of a body: the targets of its whole-signal
nonblocking assignments, both branches of an `if` included. -/
def _root_.LeanModels.Sv.PStmt.footWrites : PStmt → List String
  | .nbaAssign t _ => [t]
  | .nbaAssignL (.ident t) _ => [t]
  | .block body => PStmt.footWritesList body
  | .ifStmt _ yes no => PStmt.footWrites yes ++ PStmt.footWritesOpt no
  | _ => []

/-- `footWrites` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.footWritesOpt : Option PStmt → List String
  | none => []
  | some s => PStmt.footWrites s

/-- `footWrites` of a statement list. -/
def _root_.LeanModels.Sv.PStmt.footWritesList : List PStmt → List String
  | [] => []
  | s :: ss => PStmt.footWrites s ++ PStmt.footWritesList ss

end

mutual

/-- **The footprint test on a body.**  Blocks, `if` and nonblocking
assignments to a whole signal that is not in `srcs`; no x observer and no
function call in a condition or right-hand side; two statements of one block
never write the same target. -/
def _root_.LeanModels.Sv.PStmt.footOk (srcs : List String) : PStmt → Bool
  | .nbaAssign t v =>
      decide (t ∉ srcs) && (ndXObserver? v).isNone && !LeanModels.Sv.PExpr.hasFunctionCall v
  | .nbaAssignL (.ident t) v =>
      decide (t ∉ srcs) && (ndXObserver? v).isNone && !LeanModels.Sv.PExpr.hasFunctionCall v
  | .block body => PStmt.footOkList srcs body
  | .ifStmt c yes no =>
      (ndXObserver? c).isNone && !LeanModels.Sv.PExpr.hasFunctionCall c &&
        PStmt.footOk srcs yes && PStmt.footOkOpt srcs no
  | _ => false

/-- `footOk` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.footOkOpt (srcs : List String) : Option PStmt → Bool
  | none => true
  | some s => PStmt.footOk srcs s

/-- `footOk` of a statement list: every statement passes, and no statement
writes a target that a later statement of the list writes. -/
def _root_.LeanModels.Sv.PStmt.footOkList (srcs : List String) : List PStmt → Bool
  | [] => true
  | s :: ss =>
      PStmt.footOk srcs s && PStmt.footOkList srcs ss &&
        (PStmt.footWrites s).all (fun t => !(PStmt.footWritesList ss).contains t)

end

/-! ## What a body issues, as a function of the view -/

/-- The update a whole-signal nonblocking assignment issues on the view `v`:
the right-hand side evaluated at the target's declared width. -/
def CoreMemDesign.soloLeafV (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (t : String) (e : PExpr) : Option NbaQueue2 :=
  match E.scalarTarget t with
  | none => none
  | some w =>
      match E.evalV env E.elems v mv (some w) e with
      | .ok x => some [(t, 0, x)]
      | _ => none

mutual

/-- **The updates a body issues, as a function of the view.**  Structural
recursion on the statement; no fuel.  `none` when the evaluator refuses, when
the statement is outside the footprint test, or when an `if` condition has an
unknown bit (an oracle site of the relation: no function exists there). -/
def CoreMemDesign.soloV (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV) :
    PStmt → Option NbaQueue2
  | .nbaAssign t e => E.soloLeafV env v mv t e
  | .nbaAssignL (.ident t) e => E.soloLeafV env v mv t e
  | .block body => E.soloListV env v mv body
  | .ifStmt c yes no =>
      match E.evalV env E.elems v mv (some 1) c with
      | .ok cv =>
          if cv.bits.toList.all Logic.isKnown then
            if cv.condTrue then E.soloV env v mv yes else E.soloOptV env v mv no
          else none
      | _ => none
  | _ => none

/-- `soloV` of an optional statement. -/
def CoreMemDesign.soloOptV (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV) :
    Option PStmt → Option NbaQueue2
  | none => some []
  | some s => E.soloV env v mv s

/-- `soloV` of a statement list: the queues concatenated in source order. -/
def CoreMemDesign.soloListV (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV) :
    List PStmt → Option NbaQueue2
  | [] => some []
  | s :: ss =>
      match E.soloV env v mv s, E.soloListV env v mv ss with
      | some q, some q' => some (q ++ q')
      | _, _ => none

end

/-! ## A body alone: `soloV` gives `NdSolo` -/

/-- A whole-signal nonblocking assignment in the executor's leaf, from the
view-level value: the store is unchanged and the one update is issued. -/
theorem CoreMemDesign.soloLeafV_exec {E : CoreMemDesign}
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory) {env : IEnv}
    {t : String} {e : PExpr} {q : NbaQueue2}
    (hfc : LeanModels.Sv.PExpr.hasFunctionCall e = false)
    (h : E.soloLeafV env (E.scalar.view st.scalar) (E.memOf st.memory) t e = some q) :
    E.execStmtFuel env E.elems st [] 1 (.nbaAssign t e) = .ok ⟨st, q, [], []⟩ ∧
      E.execStmtFuel env E.elems st [] 1 (.nbaAssignL (.ident t) e) = .ok ⟨st, q, [], []⟩ ∧
      q.map (·.1) = [t] := by
  unfold CoreMemDesign.soloLeafV at h
  cases hw : E.scalarTarget t with
  | none => simp [hw] at h
  | some w =>
      cases hx : E.evalV env E.elems (E.scalar.view st.scalar) (E.memOf st.memory) (some w) e with
      | timeout => simp [hw, hx] at h
      | unsupported msg => simp [hw, hx] at h
      | ok x =>
          simp only [hw, hx, Option.some.injEq] at h
          subst h
          refine ⟨?_, ?_, rfl⟩
          · obtain ⟨st', hex, -⟩ := CoreMemDesign.execStmtFuel_V hnd h4 (.nbaAssign t e) env 1 st
              (E.scalar.view st.scalar) [(t, 0, x)] [] hc hmc (by simp [PStmt.edgeOkB, hfc])
              (by simp [PStmt.need]) (by simp [CoreMemDesign.execV, hw, hx])
            have hst := (execStmtFuel_nbaAssign_ok (fuel := 0) hex).1
            simp only at hst
            subst hst
            exact hex
          · obtain ⟨st', hex, -⟩ := CoreMemDesign.execStmtFuel_V hnd h4
              (.nbaAssignL (.ident t) e) env 1 st
              (E.scalar.view st.scalar) [(t, 0, x)] [] hc hmc
              (by simp [PStmt.edgeOkB, hfc, PLhs.hasCall])
              (by simp [PStmt.need]) (by simp [CoreMemDesign.execV, hw, hx])
            have hst := (execStmtFuel_nbaAssignIdent_ok (fuel := 0) hex).1
            simp only at hst
            subst hst
            exact hex

/-- The conclusion of the body lemma: the cursor that still has `w` and then
`tail` to execute is `NdSolo` and issues `q` before what `tail` issues; the
names in `q` are distinct, are in `writes`, and are not in `srcs`. -/
def FootSolo (E : CoreMemDesign) (st : CoreMemState) (srcs : List String) (w : EdgeWork)
    (writes : List String) (q : NbaQueue2) : Prop :=
  (∀ (tail : List EdgeWork) (q' : NbaQueue2) (mq' : MemNbaQueue),
      NdSolo E st ⟨tail, []⟩ q' mq' → NdSolo E st ⟨w :: tail, []⟩ (q ++ q') mq') ∧
    (q.map (·.1)).Nodup ∧ ∀ u ∈ q, u.1 ∈ writes ∧ u.1 ∉ srcs

theorem FootSolo.leaf {E : CoreMemDesign} {st : CoreMemState} {srcs : List String}
    {w : EdgeWork} {t : String} {q : NbaQueue2} (ht : t ∉ srcs) (hq : q.map (·.1) = [t])
    (hopen : ∀ o : Oracle, w.ndOpen E st [] o = .ok (⟨st, q, [], []⟩, [], o)) :
    FootSolo E st srcs w [t] q := by
  refine ⟨fun tail q' mq' hrest => ?_, by rw [hq]; simp, fun u hu => ?_⟩
  · exact NdSolo.step (c := ⟨w :: tail, []⟩) (exposed := []) (r := ⟨st, q, [], []⟩) rfl hopen rfl
      hrest
  · have : u.1 ∈ q.map (·.1) := List.mem_map_of_mem hu
    rw [hq] at this
    have hut : u.1 = t := by simpa using this
    rw [hut]
    exact ⟨by simp, ht⟩

/-- A node that issues nothing and exposes the nodes `ws`. -/
theorem NdSolo.idle {E : CoreMemDesign} {st : CoreMemState} {w : EdgeWork} {ws tail : List EdgeWork}
    {q : NbaQueue2} {mq : MemNbaQueue}
    (hopen : ∀ o : Oracle, w.ndOpen E st [] o = .ok (.idle st [], ws, o))
    (hrest : NdSolo E st ⟨ws ++ tail, []⟩ q mq) : NdSolo E st ⟨w :: tail, []⟩ q mq :=
  NdSolo.step (c := ⟨w :: tail, []⟩) (exposed := ws) (r := .idle st []) rfl hopen rfl hrest

mutual

/-- **A body alone.**  On a coherent store, if the body passes the footprint
test and `soloV` gives the queue `q` on the store's view, then the cursor of
the body never changes the store, gives the same result under every oracle,
and issues exactly `q`. -/
theorem CoreMemDesign.soloV_solo {E : CoreMemDesign}
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    (srcs : List String) (env : IEnv) :
    ∀ (stmt : PStmt) (q : NbaQueue2), PStmt.footOk srcs stmt = true →
      E.soloV env (E.scalar.view st.scalar) (E.memOf st.memory) stmt = some q →
      FootSolo E st srcs (.edgeStmt env stmt) (PStmt.footWrites stmt) q
  | .nbaAssign t e, q, hok, h => by
      simp only [PStmt.footOk, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none,
        Bool.not_eq_true'] at hok
      obtain ⟨⟨ht, hobs⟩, hfc⟩ := hok
      simp only [CoreMemDesign.soloV] at h
      obtain ⟨hex, -, hq⟩ := CoreMemDesign.soloLeafV_exec hnd h4 hc hmc hfc h
      exact FootSolo.leaf ht hq (fun o => by
        simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, hobs, ndLeaf, hex])
  | .nbaAssignL (.ident t) e, q, hok, h => by
      simp only [PStmt.footOk, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none,
        Bool.not_eq_true'] at hok
      obtain ⟨⟨ht, hobs⟩, hfc⟩ := hok
      simp only [CoreMemDesign.soloV] at h
      obtain ⟨-, hex, hq⟩ := CoreMemDesign.soloLeafV_exec hnd h4 hc hmc hfc h
      exact FootSolo.leaf ht hq (fun o => by
        simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr,
          CoreMemDesign.ndCheckTarget, ndIndexExprs, CoreMemDesign.ndCheckIndexExprs, hobs,
          ndLeaf, hex])
  | .block body, q, hok, h => by
      simp only [PStmt.footOk] at hok
      simp only [CoreMemDesign.soloV] at h
      obtain ⟨hs, hn, hm⟩ := CoreMemDesign.soloListV_solo hnd h4 hc hmc srcs env body q hok h
      exact ⟨fun tail q' mq' hrest => NdSolo.idle (ws := [.edgeBlock env body]) (fun o => rfl)
        (hs tail q' mq' hrest), hn, hm⟩
  | .ifStmt c yes no, q, hok, h => by
      simp only [PStmt.footOk, Bool.and_eq_true, Option.isNone_iff_eq_none,
        Bool.not_eq_true'] at hok
      obtain ⟨⟨⟨hobs, hfc⟩, hyes⟩, hno⟩ := hok
      simp only [CoreMemDesign.soloV] at h
      have heq := CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some 1) c hfc
      cases hcv : E.evalV env E.elems (E.scalar.view st.scalar) (E.memOf st.memory) (some 1) c with
      | timeout => simp [hcv] at h
      | unsupported msg => simp [hcv] at h
      | ok cv =>
          rw [hcv] at heq
          simp only [hcv] at h
          by_cases hkn : cv.bits.toList.all Logic.isKnown = true
          · simp only [hkn, ↓reduceIte] at h
            by_cases hct : cv.condTrue = true
            · simp only [hct, ↓reduceIte] at h
              obtain ⟨hs, hn, hm⟩ := CoreMemDesign.soloV_solo hnd h4 hc hmc srcs env yes q hyes h
              refine ⟨fun tail q' mq' hrest => NdSolo.idle (ws := [.edgeStmt env yes]) (fun o => ?_)
                (hs tail q' mq' hrest), hn, fun u hu => ⟨?_, (hm u hu).2⟩⟩
              · simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, hobs, heq,
                  Oracle.read_known _ _ hkn, hct]
              · simp only [PStmt.footWrites, List.mem_append]
                exact Or.inl (hm u hu).1
            · simp only [hct, Bool.false_eq_true, ↓reduceIte] at h
              cases no with
              | none =>
                  simp only [CoreMemDesign.soloOptV, Option.some.injEq] at h
                  subst h
                  refine ⟨fun tail q' mq' hrest => NdSolo.idle (ws := []) (fun o => ?_) hrest,
                    by simp, fun u hu => by simp at hu⟩
                  simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, hobs, heq,
                    Oracle.read_known _ _ hkn, hct]
              | some s =>
                  simp only [CoreMemDesign.soloOptV] at h
                  simp only [PStmt.footOkOpt] at hno
                  obtain ⟨hs, hn, hm⟩ :=
                    CoreMemDesign.soloV_solo hnd h4 hc hmc srcs env s q hno h
                  refine ⟨fun tail q' mq' hrest => NdSolo.idle (ws := [.edgeStmt env s])
                    (fun o => ?_) (hs tail q' mq' hrest), hn, fun u hu => ⟨?_, (hm u hu).2⟩⟩
                  · simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, hobs, heq,
                      Oracle.read_known _ _ hkn, hct]
                  · simp only [PStmt.footWrites, PStmt.footWritesOpt, List.mem_append]
                    exact Or.inr (hm u hu).1
          · simp [hkn] at h
  | .nbaAssignL (.bitSel _ _) _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .nbaAssignL (.partSel _ _ _) _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .nbaAssignL (.concat _) _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .nbaAssignL (.arrayElem _ _) _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .nbaAssignL (.arrayBitSel _ _ _) _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .nbaAssignL (.arrayPart _ _ _ _ _) _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .nbaAssignL (.aggregateMember _ _) _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .forLoop _ _ _ _ _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .caseStmt _ _ _ _ _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .blockingAssign _ _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .blockingAssignL _ _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .localDecl _ _ _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .automaticDecl _ _ _, _, hok, _ => by simp [PStmt.footOk] at hok
  | .unsupported _ _, _, hok, _ => by simp [PStmt.footOk] at hok

/-- The same for the statements of a block. -/
theorem CoreMemDesign.soloListV_solo {E : CoreMemDesign}
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    (srcs : List String) (env : IEnv) :
    ∀ (ss : List PStmt) (q : NbaQueue2), PStmt.footOkList srcs ss = true →
      E.soloListV env (E.scalar.view st.scalar) (E.memOf st.memory) ss = some q →
      FootSolo E st srcs (.edgeBlock env ss) (PStmt.footWritesList ss) q
  | [], q, _, h => by
      simp only [CoreMemDesign.soloListV, Option.some.injEq] at h
      subst h
      exact ⟨fun tail q' mq' hrest => NdSolo.idle (ws := []) (fun o => rfl) hrest, by simp,
        fun u hu => by simp at hu⟩
  | s :: ss, q, hok, h => by
      simp only [PStmt.footOkList, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not] at hok
      obtain ⟨⟨hs, hss⟩, hdis⟩ := hok
      simp only [CoreMemDesign.soloListV] at h
      cases h1 : E.soloV env (E.scalar.view st.scalar) (E.memOf st.memory) s with
      | none => simp [h1] at h
      | some q1 =>
          cases h2 : E.soloListV env (E.scalar.view st.scalar) (E.memOf st.memory) ss with
          | none => simp [h1, h2] at h
          | some q2 =>
              simp only [h1, h2, Option.some.injEq] at h
              subst h
              obtain ⟨hs1, hn1, hm1⟩ := CoreMemDesign.soloV_solo hnd h4 hc hmc srcs env s q1 hs h1
              obtain ⟨hs2, hn2, hm2⟩ :=
                CoreMemDesign.soloListV_solo hnd h4 hc hmc srcs env ss q2 hss h2
              refine ⟨fun tail q' mq' hrest => ?_, ?_, fun u hu => ?_⟩
              · rw [List.append_assoc]
                exact NdSolo.idle (ws := [.edgeStmt env s, .edgeBlock env ss]) (fun o => rfl)
                  (hs1 _ _ _ (hs2 tail q' mq' hrest))
              · rw [List.map_append, List.nodup_append]
                refine ⟨hn1, hn2, fun a ha b hb hab => ?_⟩
                obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
                obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hb
                exact hdis u.1 (hm1 u hu).1 (hab ▸ (hm2 u' hu').1)
              · simp only [PStmt.footWritesList, List.mem_append]
                rcases List.mem_append.mp hu with hu | hu
                · exact ⟨Or.inl (hm1 u hu).1, (hm1 u hu).2⟩
                · exact ⟨Or.inr (hm2 u hu).1, (hm2 u hu).2⟩

end

/-! ## The processes one event wakes -/

/-- The body of a clocked process. -/
def CoreMemProc.footBody? : CoreMemProc → Option PStmt
  | .edge p => some p.body
  | .event _ body => some body
  | _ => none

/-- The footprint test on a process. -/
def CoreMemProc.footOk (srcs : List String) (p : CoreMemProc) : Bool :=
  match p.footBody? with
  | some body => PStmt.footOk srcs body
  | none => true

/-- The write footprint of a process. -/
def CoreMemProc.footWrites (p : CoreMemProc) : List String :=
  match p.footBody? with
  | some body => PStmt.footWrites body
  | none => []

/-- The body a process executes when its event occurs between two views
(the test of `CoreMemProc.ndWake`). -/
def CoreMemProc.wakeBody? (before after : SvState) : CoreMemProc → Option PStmt
  | .edge p => if p.fires before after then some p.body else none
  | .event events body => if coreMemEventsFire before after events then some body else none
  | _ => none

theorem CoreMemProc.ndWake_eq_wakeBody (E : CoreMemDesign) (before after : SvState)
    (p : CoreMemProc) :
    CoreMemProc.ndWake E before after p =
      (p.wakeBody? before after).map (EdgeCursor.start E.env) := by
  cases p <;> simp only [CoreMemProc.ndWake, CoreMemProc.wakeBody?] <;> first | rfl | (split <;> rfl)

theorem CoreMemProc.wakeBody?_footBody {before after : SvState} {p : CoreMemProc} {body : PStmt}
    (h : p.wakeBody? before after = some body) : p.footBody? = some body := by
  cases p <;> simp only [CoreMemProc.wakeBody?] at h
  · split at h
    · exact h
    · cases h
  all_goals first
    | cases h
    | (split at h
       · exact h
       · cases h)

/-- Pairwise disjoint name lists. -/
def footDisjoint : List (List String) → Bool
  | [] => true
  | l :: ls => l.all (fun t => ls.all (fun l' => !l'.contains t)) && footDisjoint ls

/-- **The updates one event issues, as a function of the views**: the queues
of the woken processes, in source order.  `before`/`after` decide who wakes;
`v` is the view every body reads. -/
def CoreMemDesign.wakeQueueV (E : CoreMemDesign) (before after v : SvState) (mv : MemV) :
    List CoreMemProc → Option NbaQueue2
  | [] => some []
  | p :: rest =>
      match p.wakeBody? before after with
      | none => E.wakeQueueV before after v mv rest
      | some body =>
          match E.soloV E.env v mv body, E.wakeQueueV before after v mv rest with
          | some q, some q' => some (q ++ q')
          | _, _ => none

/-- **The woken processes are non-interfering.**  If every process passes
the footprint test, the write footprints are pairwise disjoint and
`wakeQueueV` gives `q` on the store's view, then the woken cursors are
`NdPending` with the queue `q`, whose names are distinct and off `srcs`. -/
theorem CoreMemDesign.wakeQueueV_pending {E : CoreMemDesign}
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    (srcs : List String) (before after : SvState) :
    ∀ (procs : List CoreMemProc) (q : NbaQueue2),
      (∀ p ∈ procs, p.footOk srcs = true) →
      footDisjoint (procs.map CoreMemProc.footWrites) = true →
      E.wakeQueueV before after (E.scalar.view st.scalar) (E.memOf st.memory) procs = some q →
      NdPending E st (E.ndWakeList before after procs) q [] ∧ (q.map (·.1)).Nodup ∧
        ∀ u ∈ q, u.1 ∈ procs.flatMap CoreMemProc.footWrites ∧ u.1 ∉ srcs
  | [], q, _, _, h => by
      simp only [CoreMemDesign.wakeQueueV, Option.some.injEq] at h
      subst h
      exact ⟨.nil, by simp, fun u hu => by simp at hu⟩
  | p :: rest, q, hok, hdis, h => by
      simp only [List.map_cons, footDisjoint, Bool.and_eq_true, List.all_eq_true,
        Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hdis
      obtain ⟨hdp, hdr⟩ := hdis
      have ih := CoreMemDesign.wakeQueueV_pending hnd h4 hc hmc srcs before after rest
      have hokr : ∀ p' ∈ rest, p'.footOk srcs = true :=
        fun p' hp' => hok p' (List.mem_cons_of_mem _ hp')
      simp only [CoreMemDesign.wakeQueueV] at h
      have hwl : E.ndWakeList before after (p :: rest) =
          ((p.wakeBody? before after).map (EdgeCursor.start E.env)).toList ++
            E.ndWakeList before after rest := by
        simp only [CoreMemDesign.ndWakeList, List.filterMap_cons,
          CoreMemProc.ndWake_eq_wakeBody]
        cases p.wakeBody? before after <;> rfl
      rw [hwl]
      cases hb : p.wakeBody? before after with
      | none =>
          simp only [hb] at h
          obtain ⟨hp, hn, hm⟩ := ih q hokr hdr h
          refine ⟨by simpa using hp, hn, fun u hu => ⟨?_, (hm u hu).2⟩⟩
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inr (hm u hu).1
      | some body =>
          simp only [hb] at h
          have hfb := CoreMemProc.wakeBody?_footBody hb
          have hpok : PStmt.footOk srcs body = true := by
            have := hok p (List.mem_cons_self ..)
            simpa [CoreMemProc.footOk, hfb] using this
          have hpw : p.footWrites = PStmt.footWrites body := by
            simp [CoreMemProc.footWrites, hfb]
          cases h1 : E.soloV E.env (E.scalar.view st.scalar) (E.memOf st.memory) body with
          | none => simp [h1] at h
          | some q1 =>
              cases h2 : E.wakeQueueV before after (E.scalar.view st.scalar) (E.memOf st.memory)
                  rest with
              | none => simp [h1, h2] at h
              | some q2 =>
                  simp only [h1, h2, Option.some.injEq] at h
                  subst h
                  obtain ⟨hs1, hn1, hm1⟩ :=
                    CoreMemDesign.soloV_solo hnd h4 hc hmc srcs E.env body q1 hpok h1
                  obtain ⟨hp2, hn2, hm2⟩ := ih q2 hokr hdr h2
                  have hsolo : NdSolo E st (EdgeCursor.start E.env body) q1 [] := by
                    have := hs1 [] [] [] (.done rfl)
                    simpa [EdgeCursor.start] using this
                  refine ⟨?_, ?_, fun u hu => ?_⟩
                  · have := NdPending.cons hsolo hp2
                    simpa using this
                  · rw [List.map_append, List.nodup_append]
                    refine ⟨hn1, hn2, fun a ha b hb' hab => ?_⟩
                    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
                    obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hb'
                    obtain ⟨p', hp', hin⟩ := List.mem_flatMap.mp (hm2 u' hu').1
                    exact hdp u.1 (hpw ▸ (hm1 u hu).1) _ (List.mem_map_of_mem hp') (hab ▸ hin)
                  · simp only [List.flatMap_cons, List.mem_append]
                    rcases List.mem_append.mp hu with hu | hu
                    · exact ⟨Or.inl (hpw ▸ (hm1 u hu).1), (hm1 u hu).2⟩
                    · exact ⟨Or.inr (hm2 u hu).1, (hm2 u hu).2⟩

/-- Updates with distinct names are pairwise disjoint. -/
theorem pairwise_nbaDisj_of_nodup {q : NbaQueue2} (h : (q.map (·.1)).Nodup) :
    q.Pairwise NbaDisj := by
  have h' : q.Pairwise (fun u u' => u.1 ≠ u'.1) := by
    simpa [List.Nodup, List.pairwise_map] using h
  exact h'.imp (fun hne => Or.inl hne)

/-! ## The design-level condition -/

/-- **The footprint test on a design**, a `Bool`.  See the file header for
the reading of each conjunct. -/
def CoreMemDesign.ndFootprintOk (E : CoreMemDesign) : Bool :=
  E.ndAdmitted && E.memories.toList.isEmpty &&
    E.scalar.decls.toList.all (fun dc => !dc.twoState) &&
    decide ((E.scalar.decls.toList.map Decl.name).Nodup) &&
    E.processes.toList.all (CoreMemProc.footOk E.ndEventSources) &&
    footDisjoint (E.processes.toList.map CoreMemProc.footWrites)

/-- **Non-interference as a property of the design.**  The `Bool` test, and
the structural equation `edgeBase` (`rfl` on a loaded design). -/
structure CoreMemDesign.NdFootprint (E : CoreMemDesign) : Prop where
  ok : E.ndFootprintOk = true
  edgeBase : E.scalarEdge.base = E.scalar

namespace CoreMemDesign.NdFootprint

variable {E : CoreMemDesign}

theorem admitted (h : E.NdFootprint) : E.ndAdmitted = true := by
  have := h.ok
  simp only [CoreMemDesign.ndFootprintOk, Bool.and_eq_true] at this
  exact this.1.1.1.1.1

theorem noMem (h : E.NdFootprint) : E.memories.toList = [] := by
  have := h.ok
  simp only [CoreMemDesign.ndFootprintOk, Bool.and_eq_true] at this
  exact List.isEmpty_iff.mp this.1.1.1.1.2

theorem allFour (h : E.NdFootprint) : AllFour E.scalar := by
  have := h.ok
  simp only [CoreMemDesign.ndFootprintOk, Bool.and_eq_true] at this
  intro dc hdc
  simpa using List.all_eq_true.mp this.1.1.1.2 dc hdc

theorem names (h : E.NdFootprint) : (E.scalar.decls.toList.map Decl.name).Nodup := by
  have := h.ok
  simp only [CoreMemDesign.ndFootprintOk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1.2

theorem bodies (h : E.NdFootprint) :
    ∀ p ∈ E.processes.toList, p.footOk E.ndEventSources = true := by
  have := h.ok
  simp only [CoreMemDesign.ndFootprintOk, Bool.and_eq_true] at this
  exact List.all_eq_true.mp this.1.2

theorem disjoint (h : E.NdFootprint) :
    footDisjoint (E.processes.toList.map CoreMemProc.footWrites) = true := by
  have := h.ok
  simp only [CoreMemDesign.ndFootprintOk, Bool.and_eq_true] at this
  exact this.2

theorem memCoherent (h : E.NdFootprint) (m : MemState) : E.MemCoherent m :=
  CoreMemDesign.memCoherent_noMem h.noMem m

end CoreMemDesign.NdFootprint

/-! ## The event as a function on views -/

/-- The row binds every input it names at the declared width (`EntryTyped`,
as a `Bool`). -/
def _root_.LeanModels.Sv.Design2.entryTypedB (d : Design2) (entry : SvState) : Bool :=
  d.inputNames.toList.all fun n =>
    match SvState.lookup entry n with
    | some v => d.declWidth n == some v.width
    | none => true

theorem _root_.LeanModels.Sv.Design2.entryTyped_of_B {d : Design2} {entry : SvState}
    (h : d.entryTypedB entry = true) : EntryTyped d entry := by
  intro n v hn hl
  have := List.all_eq_true.mp h n hn
  simpa [hl] using this

/-- **The updates of one event, as a function of the view before the row.**
`none` when the row is not typed, when a control signal is unknown before or
after the inputs, or when `wakeQueueV` is undefined. -/
def CoreMemDesign.eventQueueV (E : CoreMemDesign) (v row : SvState) : Option NbaQueue2 :=
  if E.scalar.toDesign2.entryTypedB row && E.ndControlsKnownIn v &&
      E.ndControlsKnownIn (applyInputs2 E.scalar.toDesign2 row v) then
    E.wakeQueueV v (applyInputs2 E.scalar.toDesign2 row v)
      (applyInputs2 E.scalar.toDesign2 row v) memNone E.processes.toList
  else none

/-- **The event as a function on scalar views.**  The inputs of the row are
applied, the woken processes' updates are collected on that view, and the
updates are committed.  `none` where the relation refuses or consults the
oracle (see the file header). -/
def CoreMemDesign.eventV (E : CoreMemDesign) (v row : SvState) : Option SvState :=
  (E.eventQueueV v row).map (commitNba2 (applyInputs2 E.scalar.toDesign2 row v))

theorem CoreMemDesign.eventQueueV_inv {E : CoreMemDesign} {v row : SvState} {T : NbaQueue2}
    (h : E.eventQueueV v row = some T) :
    E.scalar.toDesign2.entryTypedB row = true ∧ E.ndControlsKnownIn v = true ∧
      E.ndControlsKnownIn (applyInputs2 E.scalar.toDesign2 row v) = true ∧
      E.wakeQueueV v (applyInputs2 E.scalar.toDesign2 row v)
        (applyInputs2 E.scalar.toDesign2 row v) memNone E.processes.toList = some T := by
  unfold CoreMemDesign.eventQueueV at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    exact ⟨hg.1.1, hg.1.2, hg.2, h⟩
  · cases h

theorem CoreMemDesign.eventV_inv {E : CoreMemDesign} {v row v' : SvState}
    (h : E.eventV v row = some v') :
    ∃ T, E.eventQueueV v row = some T ∧
      v' = commitNba2 (applyInputs2 E.scalar.toDesign2 row v) T := by
  unfold CoreMemDesign.eventV at h
  cases hq : E.eventQueueV v row with
  | none => simp [hq] at h
  | some T =>
      simp only [hq, Option.map_some, Option.some.injEq] at h
      exact ⟨T, rfl, h.symm⟩

namespace CoreMemDesign.NdFootprint

variable {E : CoreMemDesign}

/-- The view after a typed row's inputs is `applyInputs2` of the view. -/
theorem input_view (hD : E.NdFootprint) {st : CoreMemState} (hc : E.Coherent st) {row : SvState}
    (hty : E.scalar.toDesign2.entryTypedB row = true) :
    E.scalar.view (E.ndInput st row).scalar =
      applyInputs2 E.scalar.toDesign2 row (E.scalar.view st.scalar) := by
  unfold CoreMemDesign.ndInput
  rw [CoreMemDesign.normalizeScalar_view,
    Elab.view_applyInputs hD.names hD.allFour hc.typed (Design2.entryTyped_of_B hty)]

theorem input_coherent {st : CoreMemState} (hc : E.Coherent st) (row : SvState) :
    E.Coherent (E.ndInput st row) :=
  E.normalizeScalar_coherent _ (hc.typed.applyInputs row)

/-- **The design-level condition implies `Nd.NonInterfering` at every
admissible start state.**  On a design that passes the footprint test, from
every coherent store and every row for which `eventQueueV` is defined, the
start state of the event is non-interfering, under every oracle, with the
queue `eventQueueV` computes. -/
theorem nonInterfering (hD : E.NdFootprint) {st : CoreMemState} (hc : E.Coherent st)
    {row : SvState} {T : NbaQueue2}
    (hq : E.eventQueueV (E.scalar.view st.scalar) row = some T) (o : Oracle) :
    Nd.NonInterfering E (E.ndStart st row o) T [] := by
  obtain ⟨hty, -, -, hw⟩ := CoreMemDesign.eventQueueV_inv hq
  have hic := input_coherent hc row
  have hiv := hD.input_view hc hty
  rw [← hiv, ← CoreMemDesign.memOf_noMem hD.noMem (E.ndInput st row).memory] at hw
  obtain ⟨hpend, hnodup, hmem⟩ := CoreMemDesign.wakeQueueV_pending hD.names hD.allFour hic
    (hD.memCoherent _) E.ndEventSources (E.scalar.view st.scalar)
    (E.scalar.view (E.ndInput st row).scalar) E.processes.toList T hD.bodies hD.disjoint hw
  exact
    { unsettled := rfl
      scalarQ := rfl
      memoryQ := rfl
      base := rfl
      solo := hpend
      disjoint := pairwise_nbaDisj_of_nodup hnodup
      offSources := fun u hu => (hmem u hu).2
      edgeBase := hD.edgeBase
      fourState := hD.allFour
      typed := hic.typed
      keys := by
        show ((E.scalar.view (E.ndInput st row).scalar).map Prod.fst).Nodup
        rw [E.scalar.keys_view]
        exact hD.names }

/-- **The event is a function on views.**  On a design that passes the
footprint test, from a coherent store, if `eventV` is defined on the store's
view and the row, then EVERY settled outcome of the event, under every
oracle and every schedule, with no bound on the run, has that scalar view;
and its store is coherent. -/
theorem event_view (hD : E.NdFootprint) {st : CoreMemState} (hc : E.Coherent st)
    {row v' : SvState} (hev : E.eventV (E.scalar.view st.scalar) row = some v')
    {o : Oracle} {t : NdState} (h : Nd.EventSettles E st row o t) :
    E.scalar.view t.store.scalar = v' ∧ E.Coherent t.store := by
  obtain ⟨T, hq, rfl⟩ := CoreMemDesign.eventV_inv hev
  obtain ⟨hty, -, -, -⟩ := CoreMemDesign.eventQueueV_inv hq
  have hni := hD.nonInterfering hc hq o
  refine ⟨?_, ?_⟩
  · rw [Nd.EventSettles.view_eq hni h, hD.input_view hc hty]
  · obtain ⟨s₀, hb, hr, hs⟩ := h
    obtain ⟨-, rfl, -, -⟩ := NdState.begin_next_inv hb
    obtain ⟨q, mq, m, -, -, -, hstore⟩ := Nd.settled_store hni hr hs
    rw [hstore]
    exact CoreMemDesign.ndCommitted_coherent hD.edgeBase (input_coherent hc row).typed q m

/-- **A settled outcome exists** wherever `eventV` is defined, under every
oracle.  So `event_view` is never a statement about an empty set of runs. -/
theorem event_exists (hD : E.NdFootprint) {st : CoreMemState} (hc : E.Coherent st)
    {row v' : SvState} (hev : E.eventV (E.scalar.view st.scalar) row = some v') (o : Oracle) :
    ∃ t, Nd.EventSettles E st row o t := by
  obtain ⟨T, hq, rfl⟩ := CoreMemDesign.eventV_inv hev
  obtain ⟨hty, hk, hk', -⟩ := CoreMemDesign.eventQueueV_inv hq
  have hni := hD.nonInterfering hc hq o
  refine Nd.EventSettles.exists_of_nonInterfering hD.admitted hk ?_ hni
    (m := (E.ndInput st row).memory) rfl
  unfold CoreMemDesign.ControlsKnown
  rw [hD.input_view hc hty]
  exact hk'

/-- **One observable view.**  Two settled outcomes of one event, under any
two oracles and schedules, have the same scalar view. -/
theorem event_view_unique (hD : E.NdFootprint) {st : CoreMemState} (hc : E.Coherent st)
    {row v' : SvState} (hev : E.eventV (E.scalar.view st.scalar) row = some v')
    {o₁ o₂ : Oracle} {t₁ t₂ : NdState} (h₁ : Nd.EventSettles E st row o₁ t₁)
    (h₂ : Nd.EventSettles E st row o₂ t₂) :
    E.scalar.view t₁.store.scalar = E.scalar.view t₂.store.scalar := by
  rw [(hD.event_view hc hev h₁).1, (hD.event_view hc hev h₂).1]

end CoreMemDesign.NdFootprint

#print axioms CoreMemDesign.soloLeafV_exec
#print axioms CoreMemDesign.soloV_solo
#print axioms CoreMemDesign.wakeQueueV_pending
#print axioms CoreMemDesign.NdFootprint.nonInterfering
#print axioms CoreMemDesign.NdFootprint.event_view
#print axioms CoreMemDesign.NdFootprint.event_exists
#print axioms CoreMemDesign.NdFootprint.event_view_unique

end LeanModels.Sv.Kernel
