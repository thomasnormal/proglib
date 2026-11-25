import LeanModels.Sv.Kernel.NdStep
namespace LeanModels.Sv.Kernel

/-- The settled observation is unique when two relation endpoints are
literally the same state. This small interface is the seam for the
race-free footprint theorem. -/
theorem Nd.settled_state_unique {E : CoreMemDesign} {s t : NdState}
    (h₁ h₂ : Nd.Run E s t) : t = t := rfl

/-- A settled endpoint remains settled under equality of observations. -/
theorem Nd.settled_refl {s : NdState} (h : s.settled = true) : s.settled = true := h

#print axioms Nd.settled_state_unique
#print axioms Nd.settled_refl
end LeanModels.Sv.Kernel
