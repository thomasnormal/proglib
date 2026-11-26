import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.CombHier
import LeanModels.Sv.CombEBase
import LeanModels.Sv.Comb2Term
import LeanModels.Sv.MemCombLemmas

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
  `generated_family_body_segments` applies the same segment representation to
  a generated body containing assignments and nested generate items.
  `generated_child_nested_with_processes` composes a process–nested-family–process
  row without lowering that source shape.
  `GeneratedChildSegment.flatten_append` and `flatten_map_pair` keep the
  final list algebra explicit for hand composition.
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
* `CombHier.generatedChildRefs` is the non-flattening hierarchy reader for a
  generate-only family: it retains symbolic loop headers, instance paths, and
  child designs, and refuses process/declaration/conditional siblings loudly.
  `CombHier.GeneratedChildRef.segmentAt` is the direct valuation-to-
  `flattenInst` bridge once a child design and prefix are available.
  `CombHier.generatedChildRefs_segmentAt_mapM_ok` composes those
  valuation-dependent segments in source order without choosing an iteration.
  `CombHier.generatedChildRefPairs_segmentAt_mapM_ok` is the heterogeneous
  variant when each retained reference carries its own child `Design2`.
  `CombHier.GeneratedNode` extends that boundary to source-ordered bodies that
  mix generated child instances with ordinary processes; `GeneratedNode.segmentAt`
  and `generatedNodes_segmentAt_flatten_ok` preserve the order while folding
  the valuation-dependent segments.
  `CombHier.GeneratedLoop.bindPath` and `GeneratedNode.segmentAtPath` make the
  one-path symbolic family contract explicit: a caller supplies genvar values,
  then reads exactly that source node, without enumerating sibling iterations.
  `CombHier.assembleGeneratedAt` is the compositional bridge into the ordinary
  `Design2` assembly path at one valuation, and
  `CombHier.assembleGeneratedAt_of_segments` exposes its declaration/process
  equations without a tactic or a generated-list unrolling.
  `CombHier.assembleGeneratedPathsAt` is the mixed-depth variant for source
  bodies whose siblings sit under different enclosing generate paths.
  `CombHier.generatedPaths_segmentAtPath_mapM_ok` is its source-order map
  equation, with one explicit valuation list per retained node.
  `walkIndices_of_evalInt_eq`, `arrayElemWindow_of_evalInt_eq`,
  `arrayElemTarget_of_evalInt_eq`, and `fitExpr2_lit_env_irrel` are the
  environment-observational equations for mixed-depth packed selects and
  literal assignments.
  `arrayElemRead_of_evalInt_eq`, `arraySelWidth_of_evalInt_eq`,
  `fitExpr2_arrayElem_of_evalInt_eq`, and `bitSelTarget_genvar_irrel` extend
  that equation to selected RHS values and constant bit-select targets.
  `CombHier.GeneratedNode.flattenSegments_append` and
  `generatedNodes_segmentAt_flatten_append_ok` compose adjacent source-order
  families without rebuilding or enumerating the surrounding generate bounds.
  `CombHier.generatedChildRefs_genFor_singleton` composes one symbolic loop
  header with a child reference without selecting an iteration.
  `CombHier.generatedChildRefs_genFor_nested_singleton` composes two nested
  symbolic headers in source order; use `GeneratedChildRef.segmentAt` only
  after supplying a valuation and a child `Design2`.
  Clocked generated-child families additionally need a valuation-aware child
  `CoreMemDesign` composition equation: it must map each generated instance's
  packed bit-select connections, preserve the child's event/process identities,
  and prove the resulting family aggregation before `SeqProfileI` can be
  formed.  Until that bridge exists, a clocked `for` generate containing child
  instances is a deliberate refusal rather than an unrolled fixed-`N` case.
* Memory-backed combinational designs are a separate boundary from `Design2`:
  the hand-proof route needs four named bridges before a generated unpacked
  array can be admitted.  The loader must preserve each generated element
  target (rather than retaining `AssignmentExpression:target`); the ordinary
  semantics then needs a cell-write equation for that target, a disjoint-cell
  commutation equation for the generated family, a `matV`/memory-view equation
  for the packed readback, and a settle/fixpoint theorem for the resulting
  `CoreMemDesign`.  These are prerequisites for a memory-backed combinational
  view, not alternate meanings of `Design2`; until the loader and those
  bridges exist, `sv_structure` must refuse the route and no correctness
  theorem is claimed.
  `MemState.read_after_cell_write` and `read_other_after_cell_write` are the
  per-cell equations; `MemState.distinct_cell_writes_read_commute` is the
  disjoint-cell order bridge; `MemState.readPacked_ofBitVec` is the packed
  readback bridge; and `CoreMemDesign.memory_settle_fixpoint` is the named
  acyclic settle/fixpoint rule.  A concrete two-cell hand-built receipt lives
  in `Examples/system-verilog/sem2/prefix_adder_unpacked_array/mem_lemmas.lean`.

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

/-! Exact natural-number geometry for packed row-major ports.  This remains
separate from `CombView.Aff`: a product of two symbolic quantities is
nonlinear and must not be reinterpreted as affine just to satisfy a tactic. -/
theorem rowMajor_lt {rows cols row col : Nat} (hrow : row < rows) (hcol : col < cols) :
    row * cols + col < rows * cols := by
  calc
    row * cols + col < row * cols + cols := Nat.add_lt_add_left hcol _
    _ = (row + 1) * cols := by simp [Nat.add_mul]
    _ ≤ rows * cols := Nat.mul_le_mul_right cols (Nat.succ_le_of_lt hrow)

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

@[simp] theorem flatten_append (xs ys : List GeneratedChildSegment) :
    flatten (xs ++ ys) =
      (xs.flatMap (·.decls) ++ ys.flatMap (·.decls),
       xs.flatMap (·.processes) ++ ys.flatMap (·.processes)) := by
  simp [flatten, List.flatMap_append]

@[simp] theorem flatten_map_pair (xs : List (List Decl × List Process2)) :
    flatten (xs.map fun x => { decls := x.1, processes := x.2 }) =
      (xs.flatMap Prod.fst, xs.flatMap Prod.snd) := by
  simp [flatten, List.flatMap_map]

end GeneratedChildSegment

namespace GeneratedChildSegment

/-- Turn one ordinary declaration/process pair into a generated-family segment. -/
def ofPair (q : List Decl × List Process2) : GeneratedChildSegment :=
  { decls := q.1, processes := q.2 }

/-- Flattening commutes with a symbolic outer family whose body is itself a
list of ordinary declaration/process pairs.  This is the list-level equation
used when a generated row has several child instances per iteration: it
groups each iteration first or concatenates all child pairs first, with the
same result and no enumeration of the family bound. -/
theorem flatten_flatMap_ofPair {α : Type} (xs : List α)
    (f : α → List (List Decl × List Process2)) :
    GeneratedChildSegment.flatten ((xs.flatMap f).map ofPair) =
      GeneratedChildSegment.flatten
        (xs.map (fun x => ofPair (GeneratedChildSegment.flatten ((f x).map ofPair)))) := by
  unfold ofPair
  rw [GeneratedChildSegment.flatten_map_pair]
  simp [GeneratedChildSegment.flatten, List.flatMap_assoc, List.flatMap_map]

end GeneratedChildSegment

namespace CombHier

/-- Flattening a symbolic outer family can be grouped per iteration. -/
theorem GeneratedNode.flattenSegments_flatMap {α : Type} (xs : List α)
    (f : α → List (List Decl × List Process2)) :
    GeneratedNode.flattenSegments (xs.flatMap f) =
      GeneratedNode.flattenSegments
        (xs.map (fun x => GeneratedNode.flattenSegments (f x))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, GeneratedNode.flattenSegments_append]
    simp [GeneratedNode.flattenSegments, ih]

end CombHier


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

/-! A common generated-row shape has a process before and after a nested child
family.  This equation keeps that shape explicit and composes the ordinary
process expansion with the nested-family result; callers still provide the
child equation, rather than a lowered or unrolled row. -/

theorem generated_child_nested_with_processes
    {cb : ChildInst} {env : IEnv} {elems : List (String × Nat)} {F : Nat}
    {outerG innerG : String} {outerLabel innerLabel : Option String}
    {outerInit outerBound innerInit innerBound : PExpr}
    {outerRc innerRc : Option Nat} {outerI0 outerN innerI0 innerN : Int}
    {left right : PProcess} {innerBody : List GenItem}
    {f : Int → List Decl × List Process2}
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
    (hInnerInst : GenItem.listInstFree innerBody = false)
    (hInner : ∀ outer : Int, outerI0 ≤ outer → outer < outerN →
      expandListH cb (env.bindVal outerG outer) elems F
        [GenItem.genFor innerLabel innerG innerInit
          (.binary .slt (.genvarRef innerG) innerBound)
          (.unary .inc (.genvarRef innerG)) innerRc innerBody] = .ok (f outer)) :
    (GenItem.genFor outerLabel outerG outerInit
      (.binary .slt (.genvarRef outerG) outerBound)
      (.unary .inc (.genvarRef outerG)) outerRc
      [GenItem.process left,
       GenItem.genFor innerLabel innerG innerInit
         (.binary .slt (.genvarRef innerG) innerBound)
         (.unary .inc (.genvarRef innerG)) innerRc innerBody,
       GenItem.process right]).expandH cb env elems F =
      .ok (GeneratedChildSegment.flatten
        ((intRange outerI0 (outerN - outerI0).toNat).map fun outer =>
          { decls := (f outer).1,
            processes := instProcess2 (env.bindVal outerG outer) elems left ::
              (f outer).2 ++ [instProcess2 (env.bindVal outerG outer) elems right] })) := by
  let g : Int → List Decl × List Process2 := fun outer =>
    ((f outer).1,
      instProcess2 (env.bindVal outerG outer) elems left ::
        (f outer).2 ++ [instProcess2 (env.bindVal outerG outer) elems right])
  have houter : ∀ outer : Int, outerI0 ≤ outer → outer < outerN →
      expandListH cb (env.bindVal outerG outer) elems F
        [GenItem.process left,
         GenItem.genFor innerLabel innerG innerInit
           (.binary .slt (.genvarRef innerG) innerBound)
           (.unary .inc (.genvarRef innerG)) innerRc innerBody,
         GenItem.process right] = .ok (g outer) := by
    intro outer hOuter0 hOuterN
    refine expandListH_cons_ok (it := .process left)
      (rest := [GenItem.genFor innerLabel innerG innerInit
        (.binary .slt (.genvarRef innerG) innerBound)
        (.unary .inc (.genvarRef innerG)) innerRc innerBody,
        GenItem.process right])
      (ds := []) (ps := [instProcess2 (env.bindVal outerG outer) elems left])
      (ds' := (f outer).1)
      (qs := (f outer).2 ++ [instProcess2 (env.bindVal outerG outer) elems right])
      (h := by simp [GenItem.listInstFree, GenItem.instFree, hInnerInst]) ?_ ?_
    · rw [GenItem.expandH_process]
    · have htmp := expandListH_cons_ok
          (it := .genFor innerLabel innerG innerInit
            (.binary .slt (.genvarRef innerG) innerBound)
            (.unary .inc (.genvarRef innerG)) innerRc innerBody)
          (rest := [GenItem.process right])
          (ds := (f outer).1) (ps := (f outer).2)
          (ds' := [])
          (qs := [instProcess2 (env.bindVal outerG outer) elems right])
          (h := by simp [GenItem.listInstFree, GenItem.instFree, hInnerInst])
          (by
            have hgen :
                (GenItem.genFor innerLabel innerG innerInit
                  (.binary .slt (.genvarRef innerG) innerBound)
                  (.unary .inc (.genvarRef innerG)) innerRc innerBody).instFree = false := by
              simp [GenItem.instFree, hInnerInst]
            have hlist : GenItem.listInstFree
                [GenItem.genFor innerLabel innerG innerInit
                  (.binary .slt (.genvarRef innerG) innerBound)
                  (.unary .inc (.genvarRef innerG)) innerRc innerBody] = false := by
              simp [GenItem.listInstFree, hgen]
            simpa [expandListH, hlist] using (hInner outer hOuter0 hOuterN))
          (by
            simp [expandListH, expandList2, GenItem.listInstFree, GenItem.expandH_process])
      simpa only [List.append_nil] using htmp
  rw [GenItem.expandH_genFor_ascending_flatMap
    (f := g) hOuterInit hOuterBound hOuterValue hOuterFuel houter]
  simp [GeneratedChildSegment.flatten, g, List.flatMap_map]

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

/-- Element-select geometry is independent of unrelated constant bindings.
This is the environment-observational equation needed when a process under an
outer generate loop is read beside a child under an additional inner loop:
the dimensions are the same and every selected index evaluates the same. -/
theorem walkIndices_of_evalInt_eq
    (env env' : IEnv) (ds : List (Int × Int)) (is : List PExpr)
    (h : ∀ e, e ∈ is → evalInt env e = evalInt env' e) :
    walkIndices env ds is = walkIndices env' ds is := by
  induction ds generalizing is with
  | nil =>
      cases is <;> rfl
  | cons d ds ih =>
      cases is with
      | nil => rfl
      | cons e es =>
          simp only [walkIndices]
          rw [show evalInt env e = evalInt env' e from h e (by simp)]
          rw [ih (is := es) (fun e' he' => h e' (by simp [he']))]

/-- Packed element-select geometry is stable under an irrelevant environment
extension, provided the declaration's dimension lookup and all index values
are stable. -/
theorem arrayElemWindow_of_evalInt_eq
    (env env' : IEnv) (n : String) (is : List PExpr)
    (hdims : env.dims.lookup n = env'.dims.lookup n)
    (h : ∀ e, e ∈ is → evalInt env e = evalInt env' e) :
    arrayElemWindow env n is = arrayElemWindow env' n is := by
  unfold arrayElemWindow arrayDims
  cases hL : env.dims.lookup n with
  | none =>
      have hL' : env'.dims.lookup n = none := by rw [← hdims, hL]
      simp [hL, hL']
      rfl
  | some ds =>
      have hL' : env'.dims.lookup n = some ds := by rw [← hdims, hL]
      simp only [hL, hL', Except.bind, Except.pure, pure]
      change (do
        let x ← walkIndices env ds is
        Except.ok (x.1, dimsStride x.2.2, x.2.1)) =
        (do
        let x ← walkIndices env' ds is
        Except.ok (x.1, dimsStride x.2.2, x.2.1))
      rw [walkIndices_of_evalInt_eq env env' ds is h]

/-- Target lowering preserves the same irrelevant-environment equation as the
underlying element geometry. -/
theorem arrayElemTarget_of_evalInt_eq
    (env env' : IEnv) (n : String) (is : List PExpr)
    (hdims : env.dims.lookup n = env'.dims.lookup n)
    (h : ∀ e, e ∈ is → evalInt env e = evalInt env' e) :
    arrayElemTarget env n is = arrayElemTarget env' n is := by
  unfold arrayElemTarget
  rw [arrayElemWindow_of_evalInt_eq env env' n is hdims h]

/-- Value-position element selects have the same environment-observational
equation as their target geometry. -/
theorem arrayElemRead_of_evalInt_eq
    (env env' : IEnv) (n : String) (is : List PExpr)
    (hdims : env.dims.lookup n = env'.dims.lookup n)
    (h : ∀ e, e ∈ is → evalInt env e = evalInt env' e) :
    arrayElemRead env n is = arrayElemRead env' n is := by
  unfold arrayElemRead
  rw [arrayElemWindow_of_evalInt_eq env env' n is hdims h]

/-- The self-width of an element select is stable under the same hypotheses.
This is the width equation used by `fitExpr2` for a selected RHS. -/
theorem arraySelWidth_of_evalInt_eq
    (env env' : IEnv) (n : String) (is : List PExpr)
    (hdims : env.dims.lookup n = env'.dims.lookup n)
    (h : ∀ e, e ∈ is → evalInt env e = evalInt env' e) :
    arraySelWidth env (.arrayElem n is) = arraySelWidth env' (.arrayElem n is) := by
  unfold arraySelWidth
  change (match arrayElemWindow env n is with
    | .ok (_, w, _) => some w
    | .error _ => none) =
    (match arrayElemWindow env' n is with
    | .ok (_, w, _) => some w
    | .error _ => none)
  rw [arrayElemWindow_of_evalInt_eq env env' n is hdims h]

/-- `fitExpr2` preserves the environment-observational equation for a packed
element-select, including its context-width decision. -/
theorem fitExpr2_arrayElem_of_evalInt_eq
    (env env' : IEnv) (elems : List (String × Nat)) (ctx : Option Nat)
    (n : String) (is : List PExpr)
    (hdims : env.dims.lookup n = env'.dims.lookup n)
    (h : ∀ e, e ∈ is → evalInt env e = evalInt env' e) :
    fitExpr2 env elems ctx (.arrayElem n is) =
      fitExpr2 env' elems ctx (.arrayElem n is) := by
  unfold fitExpr2
  simp only [instExpr2]
  cases ctx with
  | none =>
      rw [arrayElemRead_of_evalInt_eq env env' n is hdims h]
  | some tw =>
      simp only [rigidExpr]
      simp only [selfWidth2]
      rw [arraySelWidth_of_evalInt_eq env env' n is hdims h]
      rw [arrayElemRead_of_evalInt_eq env env' n is hdims h]

/-- A sized literal's `fitExpr2` result does not inspect the instantiation
environment.  This closes the RHS side of mixed-depth continuous assignments
after their target geometry has been related by `arrayElemTarget_of_evalInt_eq`.
-/
theorem fitExpr2_lit_env_irrel
    (env env' : IEnv) (elems : List (String × Nat)) (ctx : Option Nat)
    (v : LVec) :
    fitExpr2 env elems ctx (.lit v) = fitExpr2 env' elems ctx (.lit v) := by
  unfold fitExpr2
  simp [rigidExpr, selfWidth2]

/-- A constant bit-select target whose genvar has the same binding in two
environments lowers identically.  This is the source-shaped companion to the
packed element-select equation above. -/
theorem bitSelTarget_genvar_irrel
    (env env' : IEnv) (elems : List (String × Nat)) (n g : String) (v : Int)
    (h : env.vals.lookup g = some v) (h' : env'.vals.lookup g = some v) :
    instLhs2 env elems (.bitSel n (.genvarRef g)) =
      instLhs2 env' elems (.bitSel n (.genvarRef g)) := by
  unfold instLhs2 instLhsLeaf2 instIndex2
  simp [h, h', evalInt, IEnv.bindVal, List.lookup, selfWidth2, instExpr2]

end LeanModels.Sv
