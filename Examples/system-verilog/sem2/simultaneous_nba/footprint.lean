import Examples.«system-verilog».sem2.simultaneous_nba.relation
import LeanModels.Sv.Kernel.NdTrace

/-!
# The swap through the design-level non-interference test

`relation.lean` proves the swap statements from `Nd.NonInterfering`, built by
hand for this design at each start store (`start_nonInterfering`).  Here the
same facts come from the DESIGN-LEVEL test of
`LeanModels/Sv/Kernel/NdFootprint.lean`:

* `E_footprint`: the design passes `CoreMemDesign.NdFootprint`; the `Bool`
  test is decided by the kernel on the loaded design.
* `swap_eventV`: the event function of the design on the row that raises both
  clocks is the swap, as a computation on views (no run, no schedule).
* `start_nonInterfering_of_design`: `Nd.NonInterfering` at every admissible
  start store, from the design-level theorem.
* `swap_only_of_design`, `swap_exists_of_design`, `swap_unique_of_design`:
  the acceptance statements of `relation.lean`, re-derived through the event
  function.  The statements of `relation.lean` are unchanged.

Start hypotheses as in `relation.lean`: a coherent store whose view is
`view .l0 .l0 a b` (both clocks KNOWN; `a`, `b` any four-state value).
No simulator was run for this file.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.simultaneous_nba

set_option maxRecDepth 100000

/-- **The swap design passes the design-level non-interference test.** -/
theorem E_footprint : E.NdFootprint := { ok := by decide, edgeBase := by rfl }

theorem soloV_a (ca cb a b : Logic) :
    E.soloV E.env (view ca cb a b) memNone (.nbaAssign "a" (.ident "b")) =
      some [("a", 0, bit b)] := by
  have h1 : E.scalarTarget "a" = some 1 := by rfl
  have h2 : instExpr2 E.env (E.widthsOf E.elems) (some 1) (.ident "b") = Expr2.ident "b" := by simp
  simp only [CoreMemDesign.soloV, CoreMemDesign.soloLeafV, h1, CoreMemDesign.evalV,
    CoreMemDesign.evalScalarV, h2]
  rfl

theorem soloV_b (ca cb a b : Logic) :
    E.soloV E.env (view ca cb a b) memNone (.nbaAssign "b" (.ident "a")) =
      some [("b", 0, bit a)] := by
  have h1 : E.scalarTarget "b" = some 1 := by rfl
  have h2 : instExpr2 E.env (E.widthsOf E.elems) (some 1) (.ident "a") = Expr2.ident "a" := by simp
  simp only [CoreMemDesign.soloV, CoreMemDesign.soloLeafV, h1, CoreMemDesign.evalV,
    CoreMemDesign.evalScalarV, h2]
  rfl

/-- The updates of the event, computed on views: the queue `T a b`. -/
theorem swap_queue (a b : Logic) : E.eventQueueV (view .l0 .l0 a b) rise = some (T a b) := by
  have hin : applyInputs2 E.scalar.toDesign2 rise (view .l0 .l0 a b) = view .l1 .l1 a b := by rfl
  have hty : E.scalar.toDesign2.entryTypedB rise = true := by rfl
  have hk := controls_known .l0 .l0 a b rfl rfl
  have hk' := controls_known .l1 .l1 a b rfl rfl
  have f1 : CoreMemEdge.fires { clock := "clk_a", body := .nbaAssign "a" (.ident "b") }
      (view .l0 .l0 a b) (view .l1 .l1 a b) = true := by rfl
  have f2 : CoreMemEdge.fires { clock := "clk_b", body := .nbaAssign "b" (.ident "a") }
      (view .l0 .l0 a b) (view .l1 .l1 a b) = true := by rfl
  unfold CoreMemDesign.eventQueueV
  rw [hin, hty, hk, hk', E_procs]
  simp only [Bool.and_self, ↓reduceIte, CoreMemDesign.wakeQueueV, CoreMemProc.wakeBody?, f1, f2,
    soloV_a, soloV_b]
  rfl

/-- **The event is the swap, as a function on views.** -/
theorem swap_eventV (a b : Logic) :
    E.eventV (view .l0 .l0 a b) rise = some (view .l1 .l1 b a) := by
  unfold CoreMemDesign.eventV
  rw [swap_queue]
  rfl

/-- **`Nd.NonInterfering` from the design-level test**, at every admissible
start store and under every oracle. -/
theorem start_nonInterfering_of_design {st : CoreMemState} (hc : E.Coherent st) {a b : Logic}
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (o : Oracle) :
    Nd.NonInterfering E (E.ndStart st rise o) (T a b) [] :=
  E_footprint.nonInterfering hc (by rw [hview]; exact swap_queue a b) o

/-- Every settled outcome is the swap, through the event function. -/
theorem swap_only_of_design (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (o : Oracle) (t : NdState)
    (h : Nd.EventSettles E st rise o t) :
    E.scalar.view t.store.scalar = view .l1 .l1 b a :=
  (E_footprint.event_view hc (by rw [hview]; exact swap_eventV a b) h).1

/-- A settled outcome exists, through the design-level test. -/
theorem swap_exists_of_design (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (o : Oracle) :
    ∃ t, Nd.EventSettles E st rise o t :=
  E_footprint.event_exists hc (by rw [hview]; exact swap_eventV a b) o

/-- One observable view, through the design-level test. -/
theorem swap_unique_of_design (st : CoreMemState) (hc : E.Coherent st) (a b : Logic)
    (hview : E.scalar.view st.scalar = view .l0 .l0 a b) (o₁ o₂ : Oracle) (t₁ t₂ : NdState)
    (h₁ : Nd.EventSettles E st rise o₁ t₁) (h₂ : Nd.EventSettles E st rise o₂ t₂) :
    E.scalar.view t₁.store.scalar = E.scalar.view t₂.store.scalar :=
  E_footprint.event_view_unique hc (by rw [hview]; exact swap_eventV a b) h₁ h₂

#print axioms E_footprint
#print axioms swap_eventV
#print axioms start_nonInterfering_of_design
#print axioms swap_only_of_design
#print axioms swap_exists_of_design
#print axioms swap_unique_of_design

end Examples.«system-verilog».sem2.simultaneous_nba
