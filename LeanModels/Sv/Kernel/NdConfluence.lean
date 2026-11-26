import LeanModels.Sv.Kernel.NdStep

namespace LeanModels.Sv.Kernel

open LeanModels.Sv
set_option autoImplicit false

/-! T3 confluence interface.  The relation remains the meaning.  A race-free
admission supplies the settled-endpoint confluence fact for one event.  This
file keeps that fact visible and lifts it to the store and oracle observations
used by specifications. -/

/-- A race-free admitted fragment has at most one settled endpoint from any
common start.  This is the footprint/confluence proof obligation, stated over
the choice-explicit relation rather than over the executor. -/
def Nd.SettledConfluent (E : CoreMemDesign) : Prop :=
  ∀ s t u, Nd.Run E s t → Nd.Run E s u →
    t.settled = true → u.settled = true → t = u

/-- T3 uniqueness of settled outcomes under the visible race-free admission
hypothesis. -/
theorem Nd.settled_unique {E : CoreMemDesign}
    (hconfluent : Nd.SettledConfluent E)
    {s t u : NdState}
    (h₁ : Nd.Run E s t) (h₂ : Nd.Run E s u)
    (ht : t.settled = true) (hu : u.settled = true) : t = u :=
  hconfluent s t u h₁ h₂ ht hu

/-- The unique settled endpoint fixes both the store and the oracle. -/
theorem Nd.settled_observation_unique {E : CoreMemDesign}
    (hconfluent : Nd.SettledConfluent E)
    {s t u : NdState}
    (h₁ : Nd.Run E s t) (h₂ : Nd.Run E s u)
    (ht : t.settled = true) (hu : u.settled = true) :
    t.store = u.store ∧ t.oracle = u.oracle ∧ t = u := by
  have h := Nd.settled_unique hconfluent h₁ h₂ ht hu
  exact ⟨by cases h; rfl, by cases h; rfl, h⟩

#print axioms Nd.settled_unique
#print axioms Nd.settled_observation_unique

end LeanModels.Sv.Kernel
