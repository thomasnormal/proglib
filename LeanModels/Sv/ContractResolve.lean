import LeanModels.Sv.Contract
import LeanModels.Sv.CycleResolve

/-!
# X-E bridge for contract input valuations

Contract relies and guarantees are stated over trusted port samples.  This
lemma records the known-value case needed by that boundary: an independent
X-E read of a known valuation cannot change `HoldsOn`.  No contract meaning
or observation evaluator is changed.
-/

namespace LeanModels.Sv.Observe

open LeanModels.Sv.Kernel

theorem HoldsOn.of_xread {s s' : PortSample} {sigs : List Sig} {v : Valuation}
    (h : HoldsOn s sigs v)
    (hread : ∀ p, p ∈ sigs → ∃ source concrete,
      s.read p.1 = some source ∧ s'.read p.1 = some concrete ∧ XRead source concrete) :
    HoldsOn s' sigs v := by
  intro p hp
  obtain ⟨source, concrete, hsource, hconcrete, hx⟩ := hread p hp
  have hsource' : source = LVec.ofBitVec (v p) :=
    Option.some.inj (hsource.symm.trans (h p hp))
  cases hsource'
  rw [hconcrete]
  have hknown : (LVec.ofBitVec (v p)).bits.toList.all Logic.isKnown = true := by
    simp [LVec.ofBitVec, LVec.ofNat, LVec.allKnown,
      Array.all_eq_true_iff_forall_mem, Array.mem_ofFn, Logic.isKnown]
    intro i
    by_cases hb : (v p).toNat.testBit (i : Nat) = true <;> simp [hb]
  have heq := xRead_eq_of_known hknown hx
  cases heq
  exact rfl

theorem CycleXRead.holdsOn_pre_of_xread
    {source concrete : CycleObs PortSample} {sigs : List Sig} {v : Valuation}
    (hread : CycleXRead source concrete)
    (hholds : HoldsOn source.pre sigs v) :
    HoldsOn concrete.pre sigs v := by
  apply HoldsOn.of_xread hholds
  intro p hp
  have hopt := (hread p.1).1
  have hsource := hholds p hp
  cases hsrc : source.pre.read p.1 with
  | none => simp [hsrc] at hsource
  | some src =>
      cases hcon : concrete.pre.read p.1 with
      | none => simp [OptionXRead, hsrc, hcon] at hopt
      | some con =>
          rw [hsrc, hcon] at hopt
          exact ⟨src, con, rfl, rfl, hopt⟩

theorem CycleXRead.holdsOn_post_of_xread
    {source concrete : CycleObs PortSample} {sigs : List Sig} {v : Valuation}
    (hread : CycleXRead source concrete)
    (hholds : HoldsOn source.post sigs v) :
    HoldsOn concrete.post sigs v := by
  apply HoldsOn.of_xread hholds
  intro p hp
  have hopt := (hread p.1).2
  have hsource := hholds p hp
  cases hsrc : source.post.read p.1 with
  | none => simp [hsrc] at hsource
  | some src =>
      cases hcon : concrete.post.read p.1 with
      | none => simp [OptionXRead, hsrc, hcon] at hopt
      | some con =>
          rw [hsrc, hcon] at hopt
          exact ⟨src, con, rfl, rfl, hopt⟩

end LeanModels.Sv.Observe

#print axioms LeanModels.Sv.Observe.HoldsOn.of_xread
#print axioms LeanModels.Sv.Observe.CycleXRead.holdsOn_pre_of_xread
#print axioms LeanModels.Sv.Observe.CycleXRead.holdsOn_post_of_xread
