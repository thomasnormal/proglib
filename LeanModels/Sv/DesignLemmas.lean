import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.CombHier
import LeanModels.Sv.CombEBase
import LeanModels.Sv.Comb2Term

/-!
# Reader's index for compositional SystemVerilog design proofs

This module is an index, not a second semantics.  The named lemmas below are
stated over the ordinary source-shaped parameter and `Design2` definitions.
They are the hand-proof entry points used by hierarchy and generate proofs.

* `PDesign.instantiateRec_of_ok` splits one hierarchical instantiation into
  its parameter environment, declarations, elements, and generated processes.
* `GenItem.expandH_genFor_ascending_flatMap` gives one structural induction
  step for an ascending generate-for; `generated_child_family` and
  `generated_child_at_prefix` expose the same equations under stable names for
  hand proofs, while `GenItem.expandH_inst` and `instExpandH_of` expose one
  child's flattened declarations and processes.
* `PDesign.assembleH_decls` and `PDesign.assembleH_processes` connect the
  generated pieces back to the ordinary hierarchical design.
* `CombDesign` and `Acyclic` are the profile and dependency contracts for a
  settled combinational design; `CombDesign.of_single` is the base case and
  `Acyclic.of_single` is the corresponding one-process rank case.
* `CombView.comb_of_summary`, `CombView.acyclic_of_summary`, and
  `CombView.acyclic_of_lex` turn a proved source-shaped summary into those
  contracts without introducing a new evaluator.
* `CombHier.instantiateHDAlias2_twin` is the bridge when a module-level
  hierarchy has a flat twin; its hypotheses are the named parameter, width,
  fragment, and child-environment obligations.

A hand proof should use these equations first and only then invoke a tactic as
an optional plumbing layer.  No theorem in this index is bounded by an
executor fuel or by a fixed number of cycles; the `F` arguments in the
instantiation equations are the language's generate-expansion interface and
are discharged by the corresponding structural theorem.
-/

namespace LeanModels.Sv

/-! The declarations above are intentionally the public index.  Keeping this
file import-only makes the index cheap to read and prevents it from becoming a
parallel proof layer. -/

end LeanModels.Sv

namespace LeanModels.Sv

/-- One ascending generate family whose body is a single generated child.
The equation keeps the source loop symbolic and exposes the child's ordinary
`flattenInst` at each genvar value; no loop is unrolled by this lemma. -/
theorem generated_child_family
    {cb : ChildInst} {env : IEnv} {elems : List (String × Nat)} {F : Nat}
    {label : Option String} {g : String} {initE bound : PExpr} {rc : Option Nat}
    {i0 N : Int} {inst : PInst} {f : Int → List Decl × List Process2}
    (hi : evalInt env initE = .ok i0)
    (hbound : ∀ i : Int, bound.isInt (env.bindVal g i) = true)
    (hvalue : ∀ i : Int, evalInt (env.bindVal g i) bound = .ok N)
    (hfuel : (N - i0).toNat < F)
    (hbody : ∀ v : Int, i0 ≤ v → v < N →
      expandListH cb (env.bindVal g v) elems F [.inst inst] = .ok (f v)) :
    (GenItem.genFor label g initE (.binary .slt (.genvarRef g) bound)
      (.unary .inc (.genvarRef g)) rc [.inst inst]).expandH cb env elems F =
      .ok ((intRange i0 (N - i0).toNat).flatMap (fun v => (f v).1),
        (intRange i0 (N - i0).toNat).flatMap (fun v => (f v).2)) := by
  rw [GenItem.expandH_genFor_ascending_flatMap hi hbound hvalue hfuel]
  intro v hv0 hvN
  exact hbody v hv0 hvN

/-- A generated child expansion can be discharged directly from a decided
prefix and child design.  This is the hand-proof equation used at each leaf
of a nested family. -/
theorem generated_child_at_prefix
    {cb : ChildInst} {env : IEnv} {elems : List (String × Nat)} {F : Nat}
    {inst : PInst} {pfx : String} {child : Design2}
    (hprefix : inst.prefix env = .ok pfx)
    (hchild : cb env inst = .ok child) :
    GenItem.expandH cb env elems F (.inst inst) =
      .ok (flattenInst env elems pfx inst child) := by
  rw [GenItem.expandH_inst, instExpandH_of hprefix hchild]

end LeanModels.Sv


namespace LeanModels.Sv

/-- The two-level ascending-family equation used by nested generated gate
arrays.  Both bounds remain symbolic; the inner family is expanded under
an outer genvar binding and concatenated in source order. -/
theorem generated_child_nested_family
    {cb : ChildInst} {env : IEnv} {elems : List (String × Nat)} {F : Nat}
    {outerLabel innerLabel : Option String} {outerG innerG : String}
    {outerInit outerBound innerInit innerBound : PExpr}
    {outerRc innerRc : Option Nat} {outerI0 outerN innerI0 innerN : Int}
    {inst : PInst} {f : Int → Int → List Decl × List Process2}
    (hOuterInit : evalInt env outerInit = .ok outerI0)
    (hOuterBound : ∀ i : Int, outerBound.isInt (env.bindVal outerG i) = true)
    (hOuterValue : ∀ i : Int, evalInt (env.bindVal outerG i) outerBound = .ok outerN)
    (hOuterFuel : (outerN - outerI0).toNat < F)
    (hInnerInit : ∀ outer : Int,
      evalInt (env.bindVal outerG outer) innerInit = .ok innerI0)
    (hInnerBound : ∀ outer i : Int,
      innerBound.isInt ((env.bindVal outerG outer).bindVal innerG i) = true)
    (hInnerValue : ∀ outer i : Int,
      evalInt ((env.bindVal outerG outer).bindVal innerG i) innerBound = .ok innerN)
    (hInnerFuel : (innerN - innerI0).toNat < F)
    (hBody : ∀ outer inner : Int, outerI0 ≤ outer → outer < outerN →
      innerI0 ≤ inner → inner < innerN →
      expandListH cb ((env.bindVal outerG outer).bindVal innerG inner) elems F [.inst inst] =
        .ok (f outer inner)) :
    (GenItem.genFor outerLabel outerG outerInit
      (.binary .slt (.genvarRef outerG) outerBound)
      (.unary .inc (.genvarRef outerG)) outerRc
      [GenItem.genFor innerLabel innerG innerInit
        (.binary .slt (.genvarRef innerG) innerBound)
        (.unary .inc (.genvarRef innerG)) innerRc [.inst inst]]).expandH cb env elems F =
      .ok
        ((intRange outerI0 (outerN - outerI0).toNat).flatMap fun outer =>
          (intRange innerI0 (innerN - innerI0).toNat).flatMap fun inner => (f outer inner).1,
         (intRange outerI0 (outerN - outerI0).toNat).flatMap fun outer =>
          (intRange innerI0 (innerN - innerI0).toNat).flatMap fun inner => (f outer inner).2)  := by
  let g : Int → List Decl × List Process2 := fun outer =>
    ( (intRange innerI0 (innerN - innerI0).toNat).flatMap fun inner =>
        (f outer inner).1,
      (intRange innerI0 (innerN - innerI0).toNat).flatMap fun inner =>
        (f outer inner).2 )
  have houter : ∀ outer : Int, outerI0 ≤ outer → outer < outerN →
      expandListH cb (env.bindVal outerG outer) elems F
        [GenItem.genFor innerLabel innerG innerInit
          (.binary .slt (.genvarRef innerG) innerBound)
          (.unary .inc (.genvarRef innerG)) innerRc [.inst inst]] = .ok (g outer) := by
    intro outer hOuter0 hOuterN
    apply expandListH_singleton_ok (h := by simp [GenItem.listInstFree, GenItem.instFree])
    rw [GenItem.expandH_genFor_ascending_flatMap
      (hInnerInit outer) (hInnerBound outer) (hInnerValue outer) hInnerFuel]
    · intro inner hInner0 hInnerN
      exact hBody outer inner hOuter0 hOuterN hInner0 hInnerN
  rw [GenItem.expandH_genFor_ascending_flatMap
    (f := g) hOuterInit hOuterBound hOuterValue hOuterFuel houter]


end LeanModels.Sv
