import LeanModels.Sv.Kernel.NdFootprint

/-! # Invariants over traces, and the event as a function

`Nd.Trace` (`NdStep.lean`) is the multi-row closure of the relation: rows are
taken one at a time, each leads to a settled state by `Nd.EventSettles`, the
oracle is threaded.  This file gives the proof principles a hand proof uses
over it.  None of them enumerates a schedule or an oracle, and none has a
bound on the number of rows or on the length of a run.

## For every design

* `Nd.Trace.invariant`: a property of stores that holds at the start and is
  preserved by every settled outcome of every admitted row holds at every
  store of every trace.

## For a design that passes the footprint test (`CoreMemDesign.NdFootprint`)

There the event is a function on scalar views (`CoreMemDesign.eventV`,
`NdFootprint.lean`), so a proof rewrites with a function:

* `CoreMemDesign.eventStep E v row`: the view after the event, `v` itself
  where `eventV` is undefined (a junk value, never used: every theorem asks
  for definedness).
* `CoreMemDesign.NdFootprint.event_step`:
  `Nd.EventSettles E st row o t → view t = E.eventStep (view st) row`,
  where `eventV` is defined.
* `CoreMemDesign.NdFootprint.trace_invariant`: from `I (view st₀)` and
  "for every view with `I` and every admitted row, `eventV` is defined and
  its result has `I`", `I` holds at the view of every store of every trace,
  for every row list, every oracle and every schedule.
* `CoreMemDesign.NdFootprint.trace_refines`: if the design's event function
  is an abstract function `f` through an abstraction `abs`
  (`eventV (abs a) (mk i) = some (abs (f a i))`, `mk` building the row of a
  stimulus item), then the views of every trace are the running fold of `f`
  (`Nd.scan`), for every stimulus; `trace_refines_at` is the same at the
  `k`-th row.
* `CoreMemDesign.NdFootprint.trace_exists`: under the same hypothesis a
  trace exists for every stimulus and every oracle.

The functional reading is derived from the node-granular relation under the
footprint test; it is not a second semantics.  Interim options of the open
owner questions are those of `NdFootprint.lean` (inputs-first within a row,
atomic nonblocking commit, control signals known, node-level granularity
with the process-atomic event derived).
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Every design: an invariant of stores over traces -/

/-- **Invariants over traces.**  If `I` holds at the start store and every
settled outcome of every row satisfying `R`, from a store with `I`, under
any oracle, has `I`, then `I` holds at every store of every trace over rows
satisfying `R`.  No bound on the number of rows. -/
theorem Nd.Trace.invariant {E : CoreMemDesign} {I : CoreMemState → Prop} {R : SvState → Prop}
    (hstep : ∀ (st : CoreMemState) (row : SvState) (o : Oracle) (t : NdState),
      I st → R row → Nd.EventSettles E st row o t → I t.store)
    {st : CoreMemState} {o o' : Oracle} {rows : List SvState} {out : List CoreMemState}
    (h₀ : I st) (hR : ∀ row ∈ rows, R row) (ht : Nd.Trace E st o rows out o') :
    ∀ s ∈ out, I s := by
  induction ht with
  | nil st o => intro s hs; cases hs
  | cons hrow htail ih =>
      intro s hs
      have hI := hstep _ _ _ _ h₀ (hR _ (List.mem_cons_self ..)) hrow
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hI
      · exact ih hI (fun r hr => hR r (List.mem_cons_of_mem _ hr)) s hs

/-- The running fold: the states after each element (the start excluded). -/
def Nd.scan {α β : Type} (f : α → β → α) : α → List β → List α
  | _, [] => []
  | a, b :: bs => f a b :: Nd.scan f (f a b) bs

@[simp] theorem Nd.scan_nil {α β : Type} (f : α → β → α) (a : α) : Nd.scan f a [] = [] := rfl

@[simp] theorem Nd.scan_cons {α β : Type} (f : α → β → α) (a : α) (b : β) (bs : List β) :
    Nd.scan f a (b :: bs) = f a b :: Nd.scan f (f a b) bs := rfl

theorem Nd.scan_length {α β : Type} (f : α → β → α) : ∀ (a : α) (bs : List β),
    (Nd.scan f a bs).length = bs.length
  | _, [] => rfl
  | a, b :: bs => by simp [Nd.scan_length f (f a b) bs]

/-- The `k`-th state of the running fold is the fold of the first `k + 1`
elements. -/
theorem Nd.scan_getElem? {α β : Type} (f : α → β → α) : ∀ (a : α) (bs : List β) (k : Nat),
    k < bs.length → (Nd.scan f a bs)[k]? = some ((bs.take (k + 1)).foldl f a)
  | _, [], k, h => by simp at h
  | a, b :: bs, 0, _ => by simp
  | a, b :: bs, k + 1, h => by
      have := Nd.scan_getElem? f (f a b) bs k (by simpa using h)
      simpa using this

/-! ## The event function of a footprint design -/

/-- **The functional event step** on scalar views: the view after the event
where `eventV` is defined; the view itself (junk) elsewhere. -/
def CoreMemDesign.eventStep (E : CoreMemDesign) (v row : SvState) : SvState :=
  (E.eventV v row).getD v

theorem CoreMemDesign.eventStep_of_eventV {E : CoreMemDesign} {v row v' : SvState}
    (h : E.eventV v row = some v') : E.eventStep v row = v' := by
  simp [CoreMemDesign.eventStep, h]

namespace CoreMemDesign.NdFootprint

variable {E : CoreMemDesign}

/-- **The derived functional event step.**  On a design that passes the
footprint test, from a coherent store where the event function is defined,
every settled outcome of the event, for every oracle and schedule, has the
view `eventStep (view of the start) row`. -/
theorem event_step (hD : E.NdFootprint) {st : CoreMemState} (hc : E.Coherent st) {row : SvState}
    (hdef : (E.eventV (E.scalar.view st.scalar) row).isSome = true)
    {o : Oracle} {t : NdState} (h : Nd.EventSettles E st row o t) :
    E.scalar.view t.store.scalar = E.eventStep (E.scalar.view st.scalar) row := by
  obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp hdef
  rw [CoreMemDesign.eventStep_of_eventV hv']
  exact (hD.event_view hc hv' h).1

/-- **Invariants over traces, with the event as a function.**  On a design
that passes the footprint test: if `I` holds at the view of the start store,
and for every view with `I` and every row with `R` the event function is
defined and its result has `I`, then `I` holds at the view of every store of
every trace over rows with `R`: for every row list, every oracle, every
schedule. -/
theorem trace_invariant (hD : E.NdFootprint) {I : SvState → Prop} {R : SvState → Prop}
    (hstep : ∀ v row, I v → R row → ∃ v', E.eventV v row = some v' ∧ I v')
    {st : CoreMemState} (hc : E.Coherent st) (h₀ : I (E.scalar.view st.scalar))
    {rows : List SvState} (hR : ∀ row ∈ rows, R row)
    {o o' : Oracle} {out : List CoreMemState} (ht : Nd.Trace E st o rows out o') :
    ∀ s ∈ out, I (E.scalar.view s.scalar) := by
  have h := Nd.Trace.invariant (E := E)
    (I := fun s => E.Coherent s ∧ I (E.scalar.view s.scalar)) (R := R)
    (fun st row o t hI hrow hev => by
      obtain ⟨v', hv', hIv'⟩ := hstep _ row hI.2 hrow
      obtain ⟨hview, hcoh⟩ := hD.event_view hI.1 hv' hev
      exact ⟨hcoh, by rw [hview]; exact hIv'⟩)
    ⟨hc, h₀⟩ hR ht
  exact fun s hs => (h s hs).2

/-- **A trace is the running fold of the design's function.**  On a design
that passes the footprint test: let `mk` build the input row of a stimulus
item, and suppose that, through an abstraction `abs`, the event function is
`f` (`eventV (abs a) (mk i) = some (abs (f a i))`, for every `a` and `i`).
Then from a coherent store whose view is `abs a`, the views of the stores of
EVERY trace over the rows `ins.map mk` are `abs` of the running fold of `f`
from `a`: for every stimulus `ins` of any length, every oracle, every
schedule. -/
theorem trace_refines (hD : E.NdFootprint) {α ι : Type} {abs : α → SvState}
    {mk : ι → SvState} {f : α → ι → α}
    (hf : ∀ a i, E.eventV (abs a) (mk i) = some (abs (f a i))) :
    ∀ (ins : List ι) (st : CoreMemState) (a : α) (o o' : Oracle)
      (out : List CoreMemState), E.Coherent st → E.scalar.view st.scalar = abs a →
      Nd.Trace E st o (ins.map mk) out o' →
      out.map (fun s => E.scalar.view s.scalar) = (Nd.scan f a ins).map abs
  | [], st, a, o, o', out, _, _, ht => by
      cases ht
      rfl
  | i :: rest, st, a, o, o', out, hc, ha, ht => by
      cases ht with
      | cons hrow htail =>
          have hev := hf a i
          rw [← ha] at hev
          obtain ⟨hview, hcoh⟩ := hD.event_view hc hev hrow
          have ih := trace_refines hD hf rest _ (f a i) _ _ _ hcoh hview htail
          simp only [List.map_cons, Nd.scan_cons, hview, ih]

/-- **A trace exists**, for every stimulus and every oracle, under the
hypothesis of `trace_refines`.  So `trace_refines` is not a statement about
an empty set of traces. -/
theorem trace_exists (hD : E.NdFootprint) {α ι : Type} {abs : α → SvState}
    {mk : ι → SvState} {f : α → ι → α}
    (hf : ∀ a i, E.eventV (abs a) (mk i) = some (abs (f a i))) :
    ∀ (ins : List ι) (st : CoreMemState) (a : α) (o : Oracle),
      E.Coherent st → E.scalar.view st.scalar = abs a →
      ∃ out o', Nd.Trace E st o (ins.map mk) out o'
  | [], st, _, o, _, _ => ⟨[], o, .nil st o⟩
  | i :: rest, st, a, o, hc, ha => by
      have hev := hf a i
      rw [← ha] at hev
      obtain ⟨t, ht⟩ := hD.event_exists hc hev o
      obtain ⟨hview, hcoh⟩ := hD.event_view hc hev ht
      obtain ⟨out, o', htail⟩ := trace_exists hD hf rest t.store (f a i) t.oracle hcoh hview
      exact ⟨t.store :: out, o', .cons ht htail⟩

/-- The view after the `k`-th row of a trace is `abs` of the fold of `f` over
the first `k + 1` stimulus items. -/
theorem trace_refines_at (hD : E.NdFootprint) {α ι : Type} {abs : α → SvState}
    {mk : ι → SvState} {f : α → ι → α}
    (hf : ∀ a i, E.eventV (abs a) (mk i) = some (abs (f a i)))
    {ins : List ι} {st : CoreMemState} {a : α} {o o' : Oracle} {out : List CoreMemState}
    (hc : E.Coherent st) (ha : E.scalar.view st.scalar = abs a)
    (ht : Nd.Trace E st o (ins.map mk) out o') {k : Nat} (hk : k < ins.length) :
    (out[k]?).map (fun s => E.scalar.view s.scalar) = some (abs ((ins.take (k + 1)).foldl f a)) := by
  have h := trace_refines hD hf ins st a o o' out hc ha ht
  have h2 : (out.map (fun s => E.scalar.view s.scalar))[k]? =
      ((Nd.scan f a ins).map abs)[k]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map, Nd.scan_getElem? f a ins k hk] at h2
  exact h2

end CoreMemDesign.NdFootprint

#print axioms Nd.Trace.invariant
#print axioms Nd.scan_getElem?
#print axioms CoreMemDesign.NdFootprint.event_step
#print axioms CoreMemDesign.NdFootprint.trace_invariant
#print axioms CoreMemDesign.NdFootprint.trace_refines
#print axioms CoreMemDesign.NdFootprint.trace_exists
#print axioms CoreMemDesign.NdFootprint.trace_refines_at

end LeanModels.Sv.Kernel
