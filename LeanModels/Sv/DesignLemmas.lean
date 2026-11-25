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
  step for an ascending generate-for; `generated_child_family`,
  `generated_child_nested_family`, and `generated_child_at_prefix` expose the
  one- and two-level child equations under stable names for hand proofs, while
  `generated_child_family_segments` and `generated_child_nested_segments`
  retain valuation-dependent per-iteration segments before flattening.
  `generated_child_pathPrefix_two` and `generated_child_prefix_two` expose the
  valuation-dependent lexical names, and `GenItem.expandH_inst`/`instExpandH_of`
  expose one child's flattened declarations and processes.
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
* `CombHier.hierInsts_refuses_genFor` records the exact source-shaped boundary
  for a generated child family: it refuses before child lookup, so a hand
  proof can switch to `generated_child_nested_family` without pretending that
  the hierarchy summary already covers valuation-dependent instance names.

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

/-! A generated-child summary is a family of source-order segments.  Keeping
one segment per genvar value preserves the valuation-dependent names and the
child boundary; flattening is a separate, explicit operation for the ordinary
`Design2` representation. -/

structure GeneratedChildSegment where
  decls : List Decl
  processes : List Process2

namespace GeneratedChildSegment

def flatten (xs : List GeneratedChildSegment) : List Decl × List Process2 :=
  (xs.flatMap (·.decls), xs.flatMap (·.processes))

end GeneratedChildSegment

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

/-! The same equation with the per-iteration child results retained as a
valuation-dependent segment list.  This is the hand-proof representation a
hierarchy summary can consume without inventing static names or unrolling the
source loop. -/

theorem generated_child_family_segments
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
      .ok (GeneratedChildSegment.flatten
        ((intRange i0 (N - i0).toNat).map fun v =>
          let r := f v
          { decls := r.1, processes := r.2 })) := by
  rw [generated_child_family hi hbound hvalue hfuel hbody]
  simp [GeneratedChildSegment.flatten, List.flatMap_map]

/-! The segment equation does not require a singleton child body.  This is
the rule for a generated row whose iteration contains assignments and a
nested child family, such as `g_row/g_bit` in the noisy multiplier. -/

theorem generated_family_body_segments
    {cb : ChildInst} {env : IEnv} {elems : List (String × Nat)} {F : Nat}
    {label : Option String} {g : String} {initE bound : PExpr} {rc : Option Nat}
    {body : List GenItem} {i0 N : Int} {f : Int → List Decl × List Process2}
    (hi : evalInt env initE = .ok i0)
    (hbound : ∀ i : Int, bound.isInt (env.bindVal g i) = true)
    (hvalue : ∀ i : Int, evalInt (env.bindVal g i) bound = .ok N)
    (hfuel : (N - i0).toNat < F)
    (hbody : ∀ v : Int, i0 ≤ v → v < N →
      expandListH cb (env.bindVal g v) elems F body = .ok (f v)) :
    (GenItem.genFor label g initE (.binary .slt (.genvarRef g) bound)
      (.unary .inc (.genvarRef g)) rc body).expandH cb env elems F =
      .ok (GeneratedChildSegment.flatten
        ((intRange i0 (N - i0).toNat).map fun v =>
          let r := f v
          { decls := r.1, processes := r.2 })) := by
  rw [GenItem.expandH_genFor_ascending_flatMap hi hbound hvalue hfuel hbody]
  simp [GeneratedChildSegment.flatten, List.flatMap_map]

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

/-! Retain one segment per outer iteration before flattening the nested
family.  The inner family remains a source-order segment inside that outer
segment, so both generate indices stay available to a later hierarchy rule. -/

theorem generated_child_nested_segments
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
      .ok (GeneratedChildSegment.flatten
        ((intRange outerI0 (outerN - outerI0).toNat).map fun outer =>
          { decls := (intRange innerI0 (innerN - innerI0).toNat).flatMap fun inner =>
              (f outer inner).1,
            processes := (intRange innerI0 (innerN - innerI0).toNat).flatMap fun inner =>
              (f outer inner).2 })) := by
  rw [generated_child_nested_family hOuterInit hOuterBound hOuterValue hOuterFuel
    hInnerInit hInnerBound hInnerValue hInnerFuel hBody]
  simp [GeneratedChildSegment.flatten, List.flatMap_map]


/-- A nested generated child family whose leaf is already a decided child
design.  This is the hand-proof bridge from the source-shaped two-level loop
to the ordinary flattened declarations and processes; `prefix` is allowed to
depend on both genvar values, so lexical names remain valuation-dependent. -/
theorem generated_child_nested_flatten
    {cb : ChildInst} {env : IEnv} {elems : List (String × Nat)} {F : Nat}
    {outerLabel innerLabel : Option String} {outerG innerG : String}
    {outerInit outerBound innerInit innerBound : PExpr}
    {outerRc innerRc : Option Nat} {outerI0 outerN innerI0 innerN : Int}
    {inst : PInst} {child : Design2} {pref : Int → Int → String}
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
    (hPrefix : ∀ outer inner : Int,
      inst.prefix ((env.bindVal outerG outer).bindVal innerG inner) =
        .ok (pref outer inner))
    (hChild : ∀ outer inner : Int,
      cb ((env.bindVal outerG outer).bindVal innerG inner) inst = .ok child) :
    (GenItem.genFor outerLabel outerG outerInit
      (.binary .slt (.genvarRef outerG) outerBound)
      (.unary .inc (.genvarRef outerG)) outerRc
      [GenItem.genFor innerLabel innerG innerInit
        (.binary .slt (.genvarRef innerG) innerBound)
        (.unary .inc (.genvarRef innerG)) innerRc [.inst inst]]).expandH cb env elems F =
      .ok
        ((intRange outerI0 (outerN - outerI0).toNat).flatMap fun outer =>
          (intRange innerI0 (innerN - innerI0).toNat).flatMap fun inner =>
            (flattenInst ((env.bindVal outerG outer).bindVal innerG inner) elems
              (pref outer inner) inst child).1,
         (intRange outerI0 (outerN - outerI0).toNat).flatMap fun outer =>
          (intRange innerI0 (innerN - innerI0).toNat).flatMap fun inner =>
            (flattenInst ((env.bindVal outerG outer).bindVal innerG inner) elems
              (pref outer inner) inst child).2) := by
  apply generated_child_nested_family
    (f := fun outer inner =>
      flattenInst ((env.bindVal outerG outer).bindVal innerG inner) elems
        (pref outer inner) inst child)
    hOuterInit hOuterBound hOuterValue hOuterFuel hInnerInit hInnerBound hInnerValue hInnerFuel
  intro outer inner hOuter0 hOuterN hInner0 hInnerN
  apply expandListH_singleton_ok (h := by simp [GenItem.listInstFree, GenItem.instFree])
  rw [generated_child_at_prefix (hPrefix outer inner) (hChild outer inner)]
  rfl


end LeanModels.Sv

namespace LeanModels.Sv

/-- The lexical prefix of a child under two enclosing generate-for bindings.
This is the source-shaped naming equation used by generated-child hand proofs;
the indices are evaluated in the current `IEnv`, never baked into the AST. -/
theorem generated_child_pathPrefix_two
    (env : IEnv) (outerG innerG outerLabel innerLabel : String)
    (outer inner : Int) (hG : outerG ≠ innerG) :
    PInst.pathPrefix ((env.bindVal outerG outer).bindVal innerG inner)
      [{ label := outerLabel, genvar := some outerG },
       { label := innerLabel, genvar := some innerG }] =
      .ok (outerLabel ++ "[" ++ toString outer ++ "]." ++
        innerLabel ++ "[" ++ toString inner ++ "].") := by
  have hbeq : (outerG == innerG) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hG (beq_iff_eq.mp h)
  simp [PInst.pathPrefix, IEnv.bindVal, List.lookup, String.append_assoc, hbeq,
    Functor.map, Except.map]

/-- The full name of a generated child instance at a two-level generate point. -/
theorem generated_child_prefix_two
    (env : IEnv) (inst : PInst) (outerG innerG outerLabel innerLabel : String)
    (outer inner : Int) (hG : outerG ≠ innerG) :
    inst.path =
      [{ label := outerLabel, genvar := some outerG },
       { label := innerLabel, genvar := some innerG }] →
    inst.prefix ((env.bindVal outerG outer).bindVal innerG inner) =
      .ok (outerLabel ++ "[" ++ toString outer ++ "]." ++
        innerLabel ++ "[" ++ toString inner ++ "]." ++ inst.name ++ ".") := by
  intro hpath
  have hbeq : (outerG == innerG) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hG (beq_iff_eq.mp h)
  simp [PInst.prefix, hpath, PInst.pathPrefix, IEnv.bindVal, List.lookup,
    String.append_assoc, hbeq, Functor.map, Except.map]

end LeanModels.Sv
