import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleObl
import LeanModels.Sv.Kernel.NdConfluence

/-!
# Two clocks rising in one batch: every settled outcome is the swap

```systemverilog
module simultaneous_nba (input logic clk_a, input logic clk_b, output logic a, output logic b);
  always_ff @(posedge clk_a) a <= b;
  always_ff @(posedge clk_b) b <= a;
endmodule
```

The statements are about the choice-explicit relation of
`LeanModels/Sv/Kernel/NdStep.lean` (scheduling choice and per-read oracle
explicit, no fuel), on the design as loaded from its envelope.

Start hypotheses of every statement, stated in each one: the store is
coherent (`E.Coherent st`) and its scalar view is
`view .l0 .l0 a b`: BOTH CLOCKS ARE KNOWN (0), and `a`, `b` hold any of the
four values, x and z included.  The relation refuses an x on a clock, so it
has no run from the power-on store; what a statement says about a start with
unknown clocks is an open owner question and nothing is claimed for it here.

* `swap_only`: for every admissible start store, every oracle, every
  scheduling choice and every run length, every settled outcome of the row
  that raises both clocks is the swap.
* `swap_exists`: such a settled outcome exists, for every oracle.
* `swap_unique`: two settled outcomes, under any two oracles, have the same
  scalar view (the footprint lemma L2, `Nd.EventSettles.view_unique`).
* `start_store_exists`: the hypotheses on the store are satisfiable for all
  16 value pairs.
* `swap_step_sound`: the instance of the executor soundness theorem
  `CoreMemDesign.step_sound` on this design; `step_rise` proves that the
  executor does return on every admissible start store, and
  `swap_step_sound_run` joins the two, so the theorem is not vacuous here.
* `swap_executor`: whatever the executor returns on that row is the swap
  (soundness composed with `swap_only`).
* `swap_rows_trace`: the row-list form (`runCoreMemRows_sound`) on the
  stimulus rise, fall, rise, from every admissible start store.
* `swap_row4`: the instance `a = 0`, `b = 1` is row 4 of `check.py`.
* `if_condition_x_read_twice_can_differ`: an `if` whose condition is x, asked
  twice, can take the then branch and then the else branch.  This is about an
  `if` CONDITION (the only oracle site today).  It is not "x read twice in one
  expression": operand reads of an unknown are not oracle sites yet.

How `swap_only` is proved (by hand, no enumeration of schedules): the
footprint facts `solo_a`, `solo_b` say that each process alone leaves the
store untouched, issues one update, and gives the same result under every
oracle; with disjoint targets that are not clocks this is
`Nd.NonInterfering` (`start_nonInterfering`), and L2
(`Nd.EventSettles.view_eq`, an invariant argument through L1) gives the view
of every settled state as the commit of the two updates (`commit_T`).

No simulator was run for this file.  The only simulator evidence for this
design is the existing `check.py` receipt recorded in `README.md`.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.simultaneous_nba

load_design_sv2 sn from "Examples/system-verilog/sem2/simultaneous_nba/simultaneous_nba.sv.json"

def E : CoreMemDesign := match sn.e with | .ok d => d | _ => default

set_option maxRecDepth 100000

theorem E_ok : sn.e = .ok E := by rfl

def bit (b : Logic) : LVec := ⟨#[b]⟩

def view (ca cb a b : Logic) : SvState :=
  [("clk_a", bit ca), ("clk_b", bit cb), ("a", bit a), ("b", bit b)]

def rise : SvState := [("clk_a", bit .l1), ("clk_b", bit .l1)]

def fall : SvState := [("clk_a", bit .l0), ("clk_b", bit .l0)]

/-! ## The design is in the fragment of the soundness theorem -/

theorem E_admitted : E.ndAdmitted = true := by decide

theorem E_sources : E.ndEventSources = ["clk_a", "clk_b"] := by decide

/-- The design is in `CoreMemDesign.NbaClocked`: each field is decided by the
kernel on the loaded design. -/
theorem E_nbaClocked : E.NbaClocked :=
  { admitted := E_admitted
    bodies := by decide
    fourState := by decide
    edgeBase := by rfl }

theorem E_base : E.scalarEdge.base = E.scalar := E_nbaClocked.edgeBase

theorem E_four : AllFour E.scalar := E_nbaClocked.allFour

theorem E_names : (E.scalar.decls.toList.map Decl.name).Nodup := by decide

theorem E_noMem : E.memories.toList = [] := by rfl

theorem rise_typed : EntryTyped E.scalar.toDesign2 rise := by
  intro n v hn hl
  have hin : E.scalar.toDesign2.inputNames.toList = ["clk_a", "clk_b"] := by rfl
  rw [hin] at hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · have : v = bit .l1 := by simpa [rise, SvState.lookup] using hl.symm
    subst this; rfl
  · have : v = bit .l1 := by simpa [rise, SvState.lookup] using hl.symm
    subst this; rfl

/-! ## The start hypotheses give known controls -/

theorem controls_known (ca cb a b : Logic) (hca : ca.isKnown = true) (hcb : cb.isKnown = true) :
    E.ndControlsKnownIn (view ca cb a b) = true := by
  cases ca <;> cases cb <;> first | rfl | simp [Logic.isKnown] at hca hcb

theorem start_controls {st : CoreMemState} {a b : Logic}
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) : E.ControlsKnown st := by
  unfold CoreMemDesign.ControlsKnown
  rw [hview]
  exact controls_known _ _ _ _ rfl rfl

theorem fall_typed : EntryTyped E.scalar.toDesign2 fall := by
  intro n v hn hl
  have hin : E.scalar.toDesign2.inputNames.toList = ["clk_a", "clk_b"] := by rfl
  rw [hin] at hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · have : v = bit .l0 := by simpa [fall, SvState.lookup] using hl.symm
    subst this; rfl
  · have : v = bit .l0 := by simpa [fall, SvState.lookup] using hl.symm
    subst this; rfl

/-- The view after the row that raises both clocks: the clocks are 1, the
flops are untouched. -/
theorem pre_view {st : CoreMemState} (hc : E.Coherent st) {ca cb a b : Logic}
    (hview : E.scalar.view st.scalar = view ca cb a b) :
    E.scalar.view (E.ndInput st rise).scalar = view .l1 .l1 a b := by
  unfold CoreMemDesign.ndInput
  rw [CoreMemDesign.normalizeScalar_view, Elab.view_applyInputs E_names E_four hc.typed rise_typed,
    hview]
  rfl

/-- The view after the row that lowers both clocks. -/
theorem fall_view {st : CoreMemState} (hc : E.Coherent st) {ca cb a b : Logic}
    (hview : E.scalar.view st.scalar = view ca cb a b) :
    E.scalar.view (E.ndInput st fall).scalar = view .l0 .l0 a b := by
  unfold CoreMemDesign.ndInput
  rw [CoreMemDesign.normalizeScalar_view, Elab.view_applyInputs E_names E_four hc.typed fall_typed,
    hview]
  rfl

theorem input_coherent {st : CoreMemState} (hc : E.Coherent st) (row : SvState) :
    E.Coherent (E.ndInput st row) :=
  E.normalizeScalar_coherent _ (hc.typed.applyInputs row)

theorem pre_coherent {st : CoreMemState} (hc : E.Coherent st) : E.Coherent (E.ndInput st rise) :=
  input_coherent hc rise

theorem input_controls {st : CoreMemState} (hc : E.Coherent st) {a b : Logic}
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) :
    E.ControlsKnown (E.ndInput st rise) := by
  unfold CoreMemDesign.ControlsKnown
  rw [pre_view hc hview]
  exact controls_known _ _ _ _ rfl rfl

/-! ## What each process does alone -/

theorem wake_eq (a b : Logic) :
    E.ndWake (view .l0 .l0 a b) (view .l1 .l1 a b) =
      [⟨[.edgeStmt E.env (.nbaAssign "a" (.ident "b"))], []⟩,
       ⟨[.edgeStmt E.env (.nbaAssign "b" (.ident "a"))], []⟩] := by rfl

theorem execV_a (mv : MemV) (ca cb a b : Logic) :
    E.execV E.env (view ca cb a b) mv (.nbaAssign "a" (.ident "b")) =
      .ok (view ca cb a b, [("a", 0, bit b)], []) := by
  have h1 : E.scalarTarget "a" = some 1 := by rfl
  have h2 : instExpr2 E.env (E.widthsOf E.elems) (some 1) (.ident "b") = Expr2.ident "b" := by simp
  simp only [CoreMemDesign.execV, h1, CoreMemDesign.evalV, CoreMemDesign.evalScalarV, h2]
  rfl

theorem execV_b (mv : MemV) (ca cb a b : Logic) :
    E.execV E.env (view ca cb a b) mv (.nbaAssign "b" (.ident "a")) =
      .ok (view ca cb a b, [("b", 0, bit a)], []) := by
  have h1 : E.scalarTarget "b" = some 1 := by rfl
  have h2 : instExpr2 E.env (E.widthsOf E.elems) (some 1) (.ident "a") = Expr2.ident "a" := by simp
  simp only [CoreMemDesign.execV, h1, CoreMemDesign.evalV, CoreMemDesign.evalScalarV, h2]
  rfl

/-- The process `a <= b`, on any coherent store: the store is unchanged and
one update of `a` with the current value of `b` is queued. -/
theorem exec_a {st : CoreMemState} (hc : E.Coherent st) {ca cb a b : Logic}
    (hv : E.scalar.view st.scalar = view ca cb a b) :
    E.execStmtFuel E.env E.elems st [] 1 (.nbaAssign "a" (.ident "b")) =
      .ok ⟨st, [("a", 0, bit b)], [], []⟩ := by
  obtain ⟨st', hex, -⟩ := CoreMemDesign.execStmtFuel_V E_names E_four (.nbaAssign "a" (.ident "b"))
    E.env 1 st (view ca cb a b) [("a", 0, bit b)] [] hc (CoreMemDesign.memCoherent_noMem E_noMem _)
    (by rfl) (by decide) (by rw [hv]; exact execV_a _ ca cb a b)
  have hst := (execStmtFuel_nbaAssign_ok (fuel := 0) hex).1
  simp only at hst
  subst hst
  exact hex

theorem exec_b {st : CoreMemState} (hc : E.Coherent st) {ca cb a b : Logic}
    (hv : E.scalar.view st.scalar = view ca cb a b) :
    E.execStmtFuel E.env E.elems st [] 1 (.nbaAssign "b" (.ident "a")) =
      .ok ⟨st, [("b", 0, bit a)], [], []⟩ := by
  obtain ⟨st', hex, -⟩ := CoreMemDesign.execStmtFuel_V E_names E_four (.nbaAssign "b" (.ident "a"))
    E.env 1 st (view ca cb a b) [("b", 0, bit a)] [] hc (CoreMemDesign.memCoherent_noMem E_noMem _)
    (by rfl) (by decide) (by rw [hv]; exact execV_b _ ca cb a b)
  have hst := (execStmtFuel_nbaAssign_ok (fuel := 0) hex).1
  simp only at hst
  subst hst
  exact hex

/-! ## The footprint facts (the hypotheses of L2) -/

/-- The updates the two processes issue, in source order. -/
def T (a b : Logic) : NbaQueue2 := [("a", 0, bit b), ("b", 0, bit a)]

/-- `a <= b` alone: one node, the store untouched, no unknown read at a
decision (the result is the same under every oracle). -/
theorem solo_a {st : CoreMemState} (hc : E.Coherent st) {ca cb a b : Logic}
    (hv : E.scalar.view st.scalar = view ca cb a b) :
    NdSolo E st ⟨[.edgeStmt E.env (.nbaAssign "a" (.ident "b"))], []⟩ [("a", 0, bit b)] [] := by
  have h := NdSolo.step (E := E) (st := st)
    (c := ⟨[.edgeStmt E.env (.nbaAssign "a" (.ident "b"))], []⟩) (tail := []) (exposed := [])
    (r := ⟨st, [("a", 0, bit b)], [], []⟩) (q := []) (mq := []) rfl
    (fun o => by
      simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, ndXObserver?, ndLeaf,
        exec_a hc hv])
    rfl (.done rfl)
  simpa using h

theorem solo_b {st : CoreMemState} (hc : E.Coherent st) {ca cb a b : Logic}
    (hv : E.scalar.view st.scalar = view ca cb a b) :
    NdSolo E st ⟨[.edgeStmt E.env (.nbaAssign "b" (.ident "a"))], []⟩ [("b", 0, bit a)] [] := by
  have h := NdSolo.step (E := E) (st := st)
    (c := ⟨[.edgeStmt E.env (.nbaAssign "b" (.ident "a"))], []⟩) (tail := []) (exposed := [])
    (r := ⟨st, [("b", 0, bit a)], [], []⟩) (q := []) (mq := []) rfl
    (fun o => by
      simp [EdgeWork.ndOpen, ndOpenStmt, CoreMemDesign.ndCheckExpr, ndXObserver?, ndLeaf,
        exec_b hc hv])
    rfl (.done rfl)
  simpa using h

theorem pending {st : CoreMemState} (hc : E.Coherent st) {ca cb a b : Logic}
    (hv : E.scalar.view st.scalar = view ca cb a b) :
    NdPending E st
      [⟨[.edgeStmt E.env (.nbaAssign "a" (.ident "b"))], []⟩,
       ⟨[.edgeStmt E.env (.nbaAssign "b" (.ident "a"))], []⟩] (T a b) [] := by
  have h := NdPending.cons (solo_a hc hv) (NdPending.cons (solo_b hc hv) .nil)
  simpa [T] using h

/-- The two updates write different signals. -/
theorem T_disjoint (a b : Logic) : (T a b).Pairwise NbaDisj := by
  simp [T, NbaDisj]

/-- Neither update writes a clock. -/
theorem T_offSources (a b : Logic) : ∀ u ∈ T a b, u.1 ∉ E.ndEventSources := by
  intro u hu
  rw [E_sources]
  simp only [T, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> simp

theorem commit_T (a b : Logic) : commitNba2 (view .l1 .l1 a b) (T a b) = view .l1 .l1 b a := by rfl

theorem view_keys (ca cb a b : Logic) : ((view ca cb a b).map Prod.fst).Nodup := by
  have h : (view ca cb a b).map Prod.fst = ["clk_a", "clk_b", "a", "b"] := rfl
  rw [h]
  decide

/-- **The swap satisfies the non-interference condition of L2**, from every
admissible start store and under every oracle. -/
theorem start_nonInterfering {st : CoreMemState} (hc : E.Coherent st) {a b : Logic}
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (o : Oracle) :
    Nd.NonInterfering E (E.ndStart st rise o) (T a b) [] :=
  { unsettled := rfl
    scalarQ := rfl
    memoryQ := rfl
    base := rfl
    solo := by
      show NdPending E (E.ndInput st rise)
        (E.ndWake (E.scalar.view st.scalar) (E.scalar.view (E.ndInput st rise).scalar)) _ _
      rw [hview, pre_view hc hview, wake_eq]
      exact pending (pre_coherent hc) (pre_view hc hview)
    disjoint := T_disjoint a b
    offSources := T_offSources a b
    edgeBase := E_base
    fourState := E_four
    typed := (pre_coherent hc).typed
    keys := by
      show ((E.scalar.view (E.ndInput st rise).scalar).map Prod.fst).Nodup
      rw [pre_view hc hview]
      exact view_keys _ _ _ _ }

/-! ## The acceptance theorems -/

/-- **Every settled outcome is the swap.**  From every coherent store in
which both clocks are 0 and `a`, `b` hold any of the four values, when one
input row raises both clocks, every run of the relation that reaches a
settled state, under every scheduling choice and every oracle, ends with `a`
holding the old `b` and `b` holding the old `a`.  No step count, no fuel. -/
theorem swap_only (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (o : Oracle) (t : NdState)
    (h : Nd.EventSettles E st rise o t) :
    E.scalar.view t.store.scalar = view .l1 .l1 b a := by
  rw [Nd.EventSettles.view_eq (start_nonInterfering hc hview o) h, pre_view hc hview, commit_T]

/-- **A settled outcome exists**, under every oracle.  So `swap_only` is not
a statement about an empty set of runs. -/
theorem swap_exists (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (o : Oracle) :
    ∃ t, Nd.EventSettles E st rise o t :=
  Nd.EventSettles.exists_of_nonInterfering E_admitted (start_controls hview)
    (input_controls hc hview) (start_nonInterfering hc hview o)
    (m := (E.ndInput st rise).memory) rfl

/-- **The observable outcome is unique**, as a corollary of the footprint
lemma alone: two settled outcomes of the event, under any two oracles and any
schedules, have the same scalar view. -/
theorem swap_unique (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (o₁ o₂ : Oracle) (t₁ t₂ : NdState)
    (h₁ : Nd.EventSettles E st rise o₁ t₁) (h₂ : Nd.EventSettles E st rise o₂ t₂) :
    E.scalar.view t₁.store.scalar = E.scalar.view t₂.store.scalar :=
  Nd.EventSettles.view_unique (fun o => start_nonInterfering hc hview o) h₁ h₂

/-- **The hypotheses are satisfiable**: for all four-state values of `a` and
`b` there is a coherent store with both clocks 0. -/
theorem start_store_exists (a b : Logic) :
    ∃ st, E.Coherent st ∧ E.scalar.view st.scalar = view .l0 .l0 a b := by
  refine ⟨E.normalizeScalar E.initial (E.storeFromView (view .l0 .l0 a b)),
    E.normalizeScalar_coherent _ (E.typed_storeFromView _), ?_⟩
  rw [CoreMemDesign.normalizeScalar_view, CoreMemDesign.view_storeFromView]
  cases a <;> cases b <;> rfl

/-! ## The executor, through the relation -/

/-- **The soundness theorem instantiated on this design.**  For every
admissible start store: if the executor's slot function returns `next` on the
row that raises both clocks, the relation has a settled run from the same
start, under the executor's choices (the always-0 oracle), ending in `next`. -/
theorem swap_step_sound (st next : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (h : E.step st rise = .ok next) :
    ∃ t, Nd.EventSettles E st rise Oracle.zero t ∧ t.store = next ∧ t.oracle = Oracle.zero :=
  CoreMemDesign.step_sound E_nbaClocked hc.typed (start_controls hview) h
    ((CoreMemDesign.step_input_controls E_nbaClocked hc.typed h).mpr (input_controls hc hview))

/-- **The executor's answer is the swap.**  Its result is a settled run of
the relation (`swap_step_sound`), and every settled run is the swap
(`swap_only`). -/
theorem swap_executor (st next : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (h : E.step st rise = .ok next) :
    E.scalar.view next.scalar = view .l1 .l1 b a := by
  obtain ⟨t, hev, hst, -⟩ := swap_step_sound st next hc a b hview h
  rw [← hst]
  exact swap_only st hc a b hview Oracle.zero t hev

/-- The oracle row of `check.py` (row 4: from `a = 0`, `b = 1`, both clocks
rise, the simulators print `a = 1`, `b = 0`): every settled outcome of the
relation is that row. -/
theorem swap_row4 (st : CoreMemState) (hc : E.Coherent st)
    (hview : E.scalar.view st.scalar = view .l0 .l0 .l0 .l1) (o : Oracle) (t : NdState)
    (h : Nd.EventSettles E st rise o t) :
    (SvState.showSignal (E.scalar.view t.store.scalar) "a",
      SvState.showSignal (E.scalar.view t.store.scalar) "b") = ("1", "0") := by
  rw [swap_only st hc .l0 .l1 hview o t h]
  decide

/-! ## The executor does return: the hypothesis of the soundness theorem is met

The executor's slot function is not evaluated here; its result is derived
from what each process does alone (`exec_a`, `exec_b`), for EVERY admissible
start store. -/

theorem E_procs : E.processes.toList =
    [.edge { clock := "clk_a", body := .nbaAssign "a" (.ident "b") },
     .edge { clock := "clk_b", body := .nbaAssign "b" (.ident "a") }] := by rfl

theorem fuel_a (st : CoreMemState) :
    E.execStmtFuel E.env E.elems st [] 4096 (.nbaAssign "a" (.ident "b")) =
      E.execStmtFuel E.env E.elems st [] 1 (.nbaAssign "a" (.ident "b")) :=
  execStmtFuel_nbaAssign_fuel E E.env st [] 4095 "a" (.ident "b")

theorem fuel_b (st : CoreMemState) :
    E.execStmtFuel E.env E.elems st [] 4096 (.nbaAssign "b" (.ident "a")) =
      E.execStmtFuel E.env E.elems st [] 1 (.nbaAssign "b" (.ident "a")) :=
  execStmtFuel_nbaAssign_fuel E E.env st [] 4095 "b" (.ident "a")

/-- The Active region of the executor on the rising row: both processes run,
the store is unchanged, the two updates are queued in source order. -/
theorem runEdges_rise {st : CoreMemState} (hc : E.Coherent st) {a b : Logic}
    (hv : E.scalar.view st.scalar = view .l1 .l1 a b) :
    E.runEdges E.env E.elems st (view .l0 .l0 a b) (view .l1 .l1 a b) E.processes.toList =
      .ok ⟨st, T a b, [], []⟩ := by
  rw [E_procs]
  have f1 : CoreMemEdge.fires { clock := "clk_a", body := .nbaAssign "a" (.ident "b") }
      (view .l0 .l0 a b) (view .l1 .l1 a b) = true := by rfl
  have f2 : CoreMemEdge.fires { clock := "clk_b", body := .nbaAssign "b" (.ident "a") }
      (view .l0 .l0 a b) (view .l1 .l1 a b) = true := by rfl
  simp only [CoreMemDesign.runEdges, f1, f2, ↓reduceIte, CoreMemDesign.execStmt, fuel_a, fuel_b,
    exec_a hc hv, exec_b hc hv, Res.ok_bind]
  rfl

/-- The same when no clock rises: no process runs. -/
theorem runEdges_idle (st : CoreMemState) (ca cb a b : Logic) (hca : ca ≠ .l0) (hcb : cb ≠ .l0) :
    E.runEdges E.env E.elems st (view ca cb a b) (view .l0 .l0 a b) E.processes.toList =
      .ok ⟨st, [], [], []⟩ := by
  rw [E_procs]
  have f1 : CoreMemEdge.fires { clock := "clk_a", body := .nbaAssign "a" (.ident "b") }
      (view ca cb a b) (view .l0 .l0 a b) = false := by
    cases ca <;> first | rfl | exact absurd rfl hca
  have f2 : CoreMemEdge.fires { clock := "clk_b", body := .nbaAssign "b" (.ident "a") }
      (view ca cb a b) (view .l0 .l0 a b) = false := by
    cases cb <;> first | rfl | exact absurd rfl hcb
  simp only [CoreMemDesign.runEdges, f1, f2, Bool.false_eq_true, ↓reduceIte]

/-- **The executor returns on the rising row**, from every admissible start
store, and its result is coherent and is the swap. -/
theorem step_rise (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) :
    ∃ next, E.step st rise = .ok next ∧ E.Coherent next ∧
      E.scalar.view next.scalar = view .l1 .l1 b a := by
  have hpc := pre_coherent hc
  have hpv := pre_view hc hview
  have he : E.runEdges E.env E.elems (E.ndInput st rise) (E.scalar.view st.scalar)
      (E.scalar.view (E.ndInput st rise).scalar) E.processes.toList =
        .ok ⟨E.ndInput st rise, T a b, [], []⟩ := by
    rw [hview, hpv]
    exact runEdges_rise hpc hpv
  refine ⟨_, CoreMemDesign.step_eq_of_runEdges E_nbaClocked hc.typed he
      (m := (E.ndInput st rise).memory) rfl,
    CoreMemDesign.ndCommitted_coherent E_base hpc.typed _ _, ?_⟩
  rw [CoreMemDesign.ndCommitted_view E_base E_four hpc.typed, hpv, commit_T]

/-- The executor returns on the falling row: the clocks go to 0 and nothing
else changes. -/
theorem step_fall (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l1 .l1 a b) :
    ∃ next, E.step st fall = .ok next ∧ E.Coherent next ∧
      E.scalar.view next.scalar = view .l0 .l0 a b := by
  have hpc := input_coherent hc fall
  have hpv := fall_view hc hview
  have he : E.runEdges E.env E.elems (E.ndInput st fall) (E.scalar.view st.scalar)
      (E.scalar.view (E.ndInput st fall).scalar) E.processes.toList =
        .ok ⟨E.ndInput st fall, [], [], []⟩ := by
    rw [hview, hpv]
    exact runEdges_idle _ .l1 .l1 a b (by decide) (by decide)
  refine ⟨_, CoreMemDesign.step_eq_of_runEdges E_nbaClocked hc.typed he
      (m := (E.ndInput st fall).memory) rfl,
    CoreMemDesign.ndCommitted_coherent E_base hpc.typed _ _, ?_⟩
  rw [CoreMemDesign.ndCommitted_view E_base E_four hpc.typed, hpv]
  rfl

/-- **`step_sound` has an instance with every hypothesis discharged**: for
every admissible start store the executor returns a store, that store is the
end of a settled run of the relation under the executor's choices, and its
view is the swap. -/
theorem swap_step_sound_run (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) :
    ∃ next t, E.step st rise = .ok next ∧ Nd.EventSettles E st rise Oracle.zero t ∧
      t.store = next ∧ t.oracle = Oracle.zero ∧
      E.scalar.view next.scalar = view .l1 .l1 b a := by
  obtain ⟨next, hstep, -, hnv⟩ := step_rise st hc a b hview
  obtain ⟨t, hev, hst, ho⟩ := swap_step_sound st next hc a b hview hstep
  exact ⟨next, t, hstep, hev, hst, ho, hnv⟩

/-! ## The row-list form: rise, fall, rise -/

theorem rise_not_repeat : (rise.isEmpty && E.scalarAssignInputsOnly) = false := by rfl

theorem fall_not_repeat : (fall.isEmpty && E.scalarAssignInputsOnly) = false := by rfl

/-- **The row-list soundness theorem instantiated**, for every admissible
start store: on the stimulus `rise, fall, rise` the executor returns three
stores, with `a` and `b` swapped, held, and swapped back, and those stores
are a trace of the relation with the oracle threaded from row to row. -/
theorem swap_rows_trace (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) :
    ∃ outs, runCoreMemRows E st [rise, fall, rise] = .ok outs ∧
      outs.map (fun s => E.scalar.view s.scalar) =
        [view .l1 .l1 b a, view .l0 .l0 b a, view .l1 .l1 a b] ∧
      Nd.Trace E st Oracle.zero [rise, fall, rise] outs Oracle.zero := by
  obtain ⟨s1, h1, hc1, hv1⟩ := step_rise st hc a b hview
  obtain ⟨s2, h2, hc2, hv2⟩ := step_fall s1 hc1 b a hv1
  obtain ⟨s3, h3, hc3, hv3⟩ := step_rise s2 hc2 b a hv2
  have hrun : runCoreMemRows E st [rise, fall, rise] = .ok [s1, s2, s3] := by
    simp only [runCoreMemRows, h1, h2, h3, Res.ok_bind, rise_not_repeat, fall_not_repeat,
      Bool.false_eq_true, ↓reduceIte]
  refine ⟨[s1, s2, s3], hrun, by simp [hv1, hv2, hv3], ?_⟩
  refine runCoreMemRows_sound E_nbaClocked _ st _ hc.typed (start_controls hview) ?_ hrun ?_
  · intro row hrow
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl
    · exact rise_not_repeat
    · exact fall_not_repeat
    · exact rise_not_repeat
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    unfold CoreMemDesign.ControlsKnown
    rcases hs with rfl | rfl | rfl
    · rw [hv1]; exact controls_known _ _ _ _ rfl rfl
    · rw [hv2]; exact controls_known _ _ _ _ rfl rfl
    · rw [hv3]; exact controls_known _ _ _ _ rfl rfl

/-! ## An x in an `if` condition, read twice, can differ

The hand-built node `if (a) a <= 1; else a <= 0;` is not part of the design.
It is executed on any store of the design in which `a` is x (the power-on
store is one, `initial_view`).  Two executions of that node consult
the oracle twice: the first can take the then branch and the second the else
branch.  The site is the `if` CONDITION.  An unknown read twice inside ONE
expression (`a ^ a`) is combined by the four-state operators and does not
consult the oracle; whether operand reads become oracle sites is an open
owner question and nothing is claimed for that case. -/

def yes : PStmt := .nbaAssign "a" (.int 1)
def no : Option PStmt := some (.nbaAssign "a" (.int 0))

/-- On a store whose view has `a = x`, the condition `a` evaluates to x. -/
theorem a_is_x {st : CoreMemState} {ca cb b : Logic}
    (hview : E.scalar.view st.scalar = view ca cb .lx b) :
    E.evalExprLocals E.env E.elems st (some 1) [] (.ident "a") = .ok ⟨#[Logic.lx]⟩ := by
  rw [CoreMemDesign.evalExprLocals_eq_evalV (CoreMemDesign.memCoherent_noMem E_noMem _) E.env
    E.elems (some 1) (.ident "a") (by rfl), hview]
  have h2 : instExpr2 E.env (E.widthsOf E.elems) (some 1) (.ident "a") = Expr2.ident "a" := by simp
  simp only [CoreMemDesign.evalV, CoreMemDesign.evalScalarV, h2]
  rfl

theorem initial_view : E.scalar.view E.initial.scalar = view .lx .lx .lx .lx := by decide +kernel

/-- **An x in an `if` condition, read twice, can differ.**  On every store in
which `a` is x: under the oracle `true, false, o` the node takes the
then branch and leaves `false, o`; under what is left it takes the else
branch.  Satisfiable: `start_store_exists .lx b`, and the power-on store
(`if_condition_x_read_twice_at_power_on`). -/
theorem if_condition_x_read_twice_can_differ (st : CoreMemState)
    (ca cb b : Logic) (hview : E.scalar.view st.scalar = view ca cb .lx b) (o : Oracle) :
    ndOpenStmt E st [] (Oracle.cons true (Oracle.cons false o)) E.env
        (.ifStmt (.ident "a") yes no) =
      .ok (.idle st [], [EdgeWork.edgeStmt E.env yes], Oracle.cons false o) ∧
    ndOpenStmt E st [] (Oracle.cons false o) E.env
        (.ifStmt (.ident "a") yes no) =
      .ok (.idle st [], [EdgeWork.edgeStmt E.env (.nbaAssign "a" (.int 0))], o) :=
  ndOpenStmt_if_unknown_twice E st [] E.env (.ident "a") yes no (a_is_x hview) (by rfl) o

/-- The same on the design's power-on store. -/
theorem if_condition_x_read_twice_at_power_on (o : Oracle) :
    ndOpenStmt E E.initial [] (Oracle.cons true (Oracle.cons false o)) E.env
        (.ifStmt (.ident "a") yes no) =
      .ok (.idle E.initial [], [EdgeWork.edgeStmt E.env yes], Oracle.cons false o) ∧
    ndOpenStmt E E.initial [] (Oracle.cons false o) E.env
        (.ifStmt (.ident "a") yes no) =
      .ok (.idle E.initial [], [EdgeWork.edgeStmt E.env (.nbaAssign "a" (.int 0))], o) :=
  if_condition_x_read_twice_can_differ E.initial .lx .lx .lx initial_view o

#print axioms E_nbaClocked
#print axioms start_nonInterfering
#print axioms swap_only
#print axioms swap_exists
#print axioms swap_unique
#print axioms start_store_exists
#print axioms swap_step_sound
#print axioms swap_executor
#print axioms swap_row4
#print axioms swap_step_sound_run
#print axioms swap_rows_trace
#print axioms step_rise
#print axioms if_condition_x_read_twice_can_differ
#print axioms if_condition_x_read_twice_at_power_on

end Examples.«system-verilog».sem2.simultaneous_nba
