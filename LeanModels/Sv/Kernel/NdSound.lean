import LeanModels.Sv.Kernel.NdStep

/-! # T2 soundness boundary for the choice-explicit relation

The relation in `NdStep` is the meaning.  This file states the executor
soundness theorem at the exact boundary where the existing slot evaluator is
still used.  The fragment hypothesis exposes the one remaining proof
obligation, namely that each successful `edgeQuiesce` call is reproduced by a
finite relation run.  Admission and x/z control knownness remain visible in
that hypothesis through the relation's `NdState` start and commit rules.

No fuel occurs in `Nd.Run` or `Nd.EventSettles`.  The only fuel is the
executor's `step` hypothesis and its `edgeQuiesce` call.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv
set_option autoImplicit false

/-- The clocked NBA fragment at the executor/relation seam.  The body and
admission predicates are retained as explicit evidence for callers. -/
structure CoreMemDesign.NbaClocked (E : CoreMemDesign) : Prop where
  admitted : E.ndAdmitted = true
  bodies : ∀ p ∈ E.processes.toList, p.ndClocked = true
  /-- The executor's successful quiescence result is a settled relation run.
  This is the concrete T2 proof obligation for the imported executor core. -/
  edge_sound : ∀ (n : Nat) (st next : CoreMemState) (before after : SvState),
    E.edgeQuiesce n st before after st = .ok next →
    ∃ t, Nd.Run E
        { store := st, active := E.ndWake before after, scalarQ := [],
          memoryQ := [], base := after, oracle := Oracle.zero,
          settled := false } t ∧
      t.settled = true ∧ t.store = next ∧ t.oracle = Oracle.zero
  /-- The executor's preparation phase agrees with the relation's input
  transition, including the visible control-knownness refusal. -/
  begin_sound : ∀ (st : CoreMemState) (entry : SvState)
      (pre : CoreMemState) (before after : SvState),
      E.prepareStep st entry = .ok (pre, before, after) →
      NdState.begin E st entry Oracle.zero = .next
        { store := pre, active := E.ndWake before after, scalarQ := [], memoryQ := [],
          base := after, oracle := Oracle.zero, settled := false }

/-- T2 for one input row.  The executor's actual result is related to the
same start store and row, under the zero oracle. -/
theorem CoreMemDesign.step_sound {E : CoreMemDesign} (hE : E.NbaClocked)
    {st next : CoreMemState} {entry : SvState}
    (h : E.step st entry = .ok next) :
    ∃ t, Nd.EventSettles E st entry Oracle.zero t ∧
      t.store = next ∧ t.oracle = Oracle.zero := by
  unfold CoreMemDesign.step at h
  cases hp : E.prepareStep st entry with
  | timeout => simp [hp] at h
  | unsupported msg => simp [hp] at h
  | ok triple =>
      obtain ⟨pre, before, after⟩ := triple
      simp only [hp, Res.ok_bind] at h
      obtain ⟨t, hrun, hsettled, hstore, horacle⟩ :=
        hE.edge_sound 4096 pre next before after h
      refine ⟨t, ?_, hstore, horacle⟩
      refine ⟨_, ?_, hrun, hsettled⟩
      exact hE.begin_sound st entry pre before after hp

/-- A row-by-row trace relation for the executor. -/
inductive NdZeroTrace (E : CoreMemDesign) :
    CoreMemState → List SvState → List CoreMemState → Prop where
  | nil (st : CoreMemState) : NdZeroTrace E st [] []
  | cons {st st' : CoreMemState} {row : SvState}
      {rest : List SvState} {out : List CoreMemState}
      (hrow : ∃ t, Nd.EventSettles E st row Oracle.zero t ∧ t.store = st')
      (htail : NdZeroTrace E st' rest out) :
      NdZeroTrace E st (row :: rest) (st' :: out)

/-- Any successful choice-explicit executor move is a relation step. -/
theorem ndStep_sound {E : CoreMemDesign} {s t : NdState} {choice : Nat}
    (h : ndStep E choice s = .next t) : Nd.Step E s t :=
  ⟨choice, h⟩

/-- The relation closure is closed under one choice-zero successor. -/
theorem ndRun_append_step {E : CoreMemDesign} {s t u : NdState}
    (hr : Nd.Run E s t) (h : ndStep E 0 t = .next u) : Nd.Run E s u :=
  hr.tail ⟨0, h⟩

/-- The executor's list runner is sound row by row whenever it returns a
successful output list. -/
theorem runCoreMemRows_sound {E : CoreMemDesign} (hE : E.NbaClocked) :
    ∀ (rows : List SvState) (st : CoreMemState) (out : List CoreMemState),
      (∀ row ∈ rows, row.isEmpty = false) →
      runCoreMemRows E st rows = .ok out → NdZeroTrace E st rows out
  | [], st, out, _, h => by
      simp only [runCoreMemRows, Res.ok.injEq] at h
      subst h
      exact .nil st
  | row :: rest, st, out, hne, h => by
      have hrow := hne row (List.mem_cons_self ..)
      simp only [runCoreMemRows, hrow, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨st', hstep, h⟩ := Res.bind_eq_ok.mp h
      obtain ⟨tail, htail, h⟩ := Res.bind_eq_ok.mp h
      cases h
      obtain ⟨t, hev, hst, _⟩ := CoreMemDesign.step_sound hE hstep
      exact .cons ⟨t, hev, hst⟩
        (runCoreMemRows_sound hE rest st' tail
          (fun r hr => hne r (List.mem_cons_of_mem _ hr)) htail)

#print axioms CoreMemDesign.step_sound
#print axioms runCoreMemRows_sound

end LeanModels.Sv.Kernel
