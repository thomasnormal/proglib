import LeanModels.Sv.Kernel.NdStep
namespace LeanModels.Sv.Kernel

/-- A one-step executor result is directly a relation successor whenever the
executor outcome is a choice-explicit `.next` state. -/
theorem ndStep_sound {E : CoreMemDesign} {s t : NdState} {choice : Nat}
    (h : ndStep E choice s = .next t) : Nd.Step E s t :=
  ⟨choice, h⟩

/-- The relation closure is closed under appending one executor successor. -/
theorem ndRun_append_step {E : CoreMemDesign} {s t u : NdState}
    (hr : Nd.Run E s t) (h : ndStep E 0 t = .next u) : Nd.Run E s u :=
  hr.tail ⟨0, h⟩

#print axioms ndStep_sound
#print axioms ndRun_append_step
end LeanModels.Sv.Kernel
