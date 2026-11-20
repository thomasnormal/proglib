import LeanModels.Sv.ObserveE
import LeanModels.Sv.Kernel.XResolve

/-!
# X-E bridge for cycle observations

This is the observation-level bridge used by cycle contracts.  It relates the
pre and post port reads independently and projects back to equal reads when a
consumer proves those reads known.  It does not define a cycle machine or
touch the provisional run2 route.
-/

namespace LeanModels.Sv.Observe

open LeanModels.Sv.Kernel

def OptionXRead (source concrete : Option LVec) : Prop :=
  match source, concrete with
  | none, none => True
  | some source, some concrete => XRead source concrete
  | _, _ => False

theorem optionXRead_width {source concrete : Option LVec}
    (hread : OptionXRead source concrete) :
    source.map LVec.width = concrete.map LVec.width := by
  cases source with
  | none => cases concrete <;> simp [OptionXRead] at hread ⊢
  | some source =>
      cases concrete with
      | none => simp [OptionXRead] at hread
      | some concrete =>
          have hwidth := xRead_width hread
          simpa using hwidth.symm

def CycleXRead (source concrete : CycleObs PortSample) : Prop :=
  ∀ name,
    OptionXRead (source.pre.read name) (concrete.pre.read name) ∧
      OptionXRead (source.post.read name) (concrete.post.read name)

theorem optionXRead_eq_of_known {source concrete : Option LVec}
    (hread : OptionXRead source concrete)
    (hknown : ∀ value, source = some value → value.bits.toList.all Logic.isKnown = true) :
    source = concrete := by
  cases source with
  | none => cases concrete <;> simp [OptionXRead] at hread ⊢
  | some source =>
      cases concrete with
      | none => simp [OptionXRead] at hread
      | some concrete =>
          have heq := xRead_eq_of_known (hknown source rfl) hread
          cases heq
          rfl

theorem CycleXRead.pre_read_eq_of_known {source concrete : CycleObs PortSample}
    (hread : CycleXRead source concrete)
    (hknown : ∀ name value, source.pre.read name = some value →
      value.bits.toList.all Logic.isKnown = true) :
    ∀ name, source.pre.read name = concrete.pre.read name := by
  intro name
  exact optionXRead_eq_of_known (hread name).1 (fun value hvalue => hknown name value hvalue)

theorem CycleXRead.post_read_eq_of_known {source concrete : CycleObs PortSample}
    (hread : CycleXRead source concrete)
    (hknown : ∀ name value, source.post.read name = some value →
      value.bits.toList.all Logic.isKnown = true) :
    ∀ name, source.post.read name = concrete.post.read name := by
  intro name
  exact optionXRead_eq_of_known (hread name).2 (fun value hvalue => hknown name value hvalue)

theorem CycleXRead.read_eq_of_known {source concrete : CycleObs PortSample}
    (hread : CycleXRead source concrete)
    (hknownPre : ∀ name value, source.pre.read name = some value →
      value.bits.toList.all Logic.isKnown = true)
    (hknownPost : ∀ name value, source.post.read name = some value →
      value.bits.toList.all Logic.isKnown = true) :
    ∀ name,
      source.pre.read name = concrete.pre.read name ∧
        source.post.read name = concrete.post.read name := by
  intro name
  exact ⟨hread.pre_read_eq_of_known hknownPre name,
    hread.post_read_eq_of_known hknownPost name⟩

theorem CycleXRead.width_eq {source concrete : CycleObs PortSample}
    (hread : CycleXRead source concrete) :
    ∀ name,
      (source.pre.read name).map LVec.width = (concrete.pre.read name).map LVec.width ∧
        (source.post.read name).map LVec.width = (concrete.post.read name).map LVec.width := by
  intro name
  exact ⟨optionXRead_width (hread name).1, optionXRead_width (hread name).2⟩

/-! A complete observation trace carries one independent witness per cycle.
The relation is paired structurally so a concrete trace cannot gain or lose a
sample while its per-cycle reads are being resolved. -/

inductive CycleXReadRun : List (CycleObs PortSample) → List (CycleObs PortSample) → Prop where
  | nil : CycleXReadRun [] []
  | cons {source concrete : CycleObs PortSample}
      {sources concreteTail : List (CycleObs PortSample)} :
      CycleXRead source concrete → CycleXReadRun sources concreteTail →
      CycleXReadRun (source :: sources) (concrete :: concreteTail)

inductive CycleReadEqRun (name : String) :
    List (CycleObs PortSample) → List (CycleObs PortSample) → Prop where
  | nil : CycleReadEqRun name [] []
  | cons {source concrete : CycleObs PortSample}
      {sources concreteTail : List (CycleObs PortSample)} :
      (source.pre.read name = concrete.pre.read name ∧
        source.post.read name = concrete.post.read name) →
      CycleReadEqRun name sources concreteTail →
      CycleReadEqRun name (source :: sources) (concrete :: concreteTail)

theorem CycleXReadRun.append
    {leftSource leftConcrete rightSource rightConcrete : List (CycleObs PortSample)}
    (left : CycleXReadRun leftSource leftConcrete)
    (right : CycleXReadRun rightSource rightConcrete) :
    CycleXReadRun (leftSource ++ rightSource) (leftConcrete ++ rightConcrete) := by
  induction left generalizing right with
  | nil => simpa using right
  | cons hhead htail ih =>
      simpa using CycleXReadRun.cons hhead (ih right)

theorem CycleXReadRun.read_eq_of_known
    {source concrete : List (CycleObs PortSample)}
    (hread : CycleXReadRun source concrete)
    (hknown : ∀ cycle, cycle ∈ source →
      (∀ name value, cycle.pre.read name = some value →
        value.bits.toList.all Logic.isKnown = true) ∧
      (∀ name value, cycle.post.read name = some value →
        value.bits.toList.all Logic.isKnown = true)) :
    ∀ name, CycleReadEqRun name source concrete := by
  induction hread with
  | nil =>
      intro name
      exact .nil
  | @cons source concrete sources concreteTail hhead htail ih =>
      intro name
      apply CycleReadEqRun.cons
      · have hknownHead := hknown source (by simp)
        exact hhead.read_eq_of_known hknownHead.1 hknownHead.2 name
      · apply ih
        intro cycle hcycle
        exact hknown cycle (by simp [hcycle])

end LeanModels.Sv.Observe

#print axioms LeanModels.Sv.Observe.optionXRead_eq_of_known
#print axioms LeanModels.Sv.Observe.optionXRead_width
#print axioms LeanModels.Sv.Observe.CycleXRead.pre_read_eq_of_known
#print axioms LeanModels.Sv.Observe.CycleXRead.post_read_eq_of_known
#print axioms LeanModels.Sv.Observe.CycleXRead.read_eq_of_known
#print axioms LeanModels.Sv.Observe.CycleXRead.width_eq
#print axioms LeanModels.Sv.Observe.CycleXReadRun.append
#print axioms LeanModels.Sv.Observe.CycleXReadRun.read_eq_of_known
