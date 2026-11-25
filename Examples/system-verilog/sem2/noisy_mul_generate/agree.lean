import LeanModels.Sv.Ingest2
import LeanModels.Sv.DesignLemmas
import LeanModels.Sv.CombHier
import LeanModels.Sv.CombProcTactic
open LeanModels.Sv
open LeanModels.Sv.Kernel
namespace Examples.«system-verilog».sem2.noisy_mul_generate
load_design_sv2 noisyMul from "Examples/system-verilog/sem2/noisy_mul_generate/noisy_mul_generate.sv.json"
#guard (noisyMul.sem 2).decls.size > 0
#guard (noisyMul.sem 3).decls.size > (noisyMul.sem 2).decls.size
#guard (noisyMul.sem 2).processes.size > 0
#guard match CombHier.summaryH noisyMul.pdesign noisyMul.plib with
  | .error _ => true
  | .ok _ => false
#guard match CombHier.hierInsts noisyMul.pdesign noisyMul.plib with
  | .error e => e.startsWith "an instance sits inside the generate loop"
  | .ok _ => false

/-! The tactic route names the same source-shaped boundary for every symbolic
parameter value.  This is a regression receipt for the refusal: it must not
fall through to a fixed-parameter expansion or a timeout. -/
/--
error: sv_structure: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: an instance sits inside the generate loop `g_pp` (genvar `i`): v1 of the hierarchy summary reads module-level instances only (one instance per loop iteration would make the child's sites a generate family whose names carry the loop index, which the summary does not build yet); the structure of such a design can be proved by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) : CombDesign (noisyMul.sem N) := by
  sv_structure
end Examples.«system-verilog».sem2.noisy_mul_generate
#check generated_child_family
#check generated_child_family_segments
#check generated_family_body_segments
#check generated_child_nested_with_processes
#check generated_child_at_prefix
#check generated_child_nested_family
#check generated_child_nested_segments
#check CombHier.hierInsts_refuses_genFor

namespace Examples.«system-verilog».sem2.noisy_mul_generate

def andInst : PInst :=
  { name := "u_and", module := "and2f",
    path := [{ label := "g_pp", genvar := some "i" },
      { label := "g_pp_j", genvar := some "j" }],
    conns :=
      [.input "a" (some (.bitSel (.ident "a") (.genvarRef "j"))) false,
       .input "b" (some (.bitSel (.ident "b") (.genvarRef "i"))) false,
       .input "f" (some (.arrayElem "f" [.genvarRef "i", .genvarRef "j"])) false,
       .output "y" (some (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]))] }

def ppGen : GenItem :=
  .genFor (some "g_pp") "i" (.int 0)
    (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 4)
    [.genFor (some "g_pp_j") "j" (.int 0)
      (.binary .slt (.genvarRef "j") (.paramRef "N" none))
      (.unary .inc (.genvarRef "j")) (some 4) [.inst andInst]]

def rowGen : GenItem := noisyMul.pdesign.generates[1]!

def rowBody : List GenItem :=
  match rowGen with
  | .genFor _ _ _ _ _ _ body => body
  | _ => []

/-! The hierarchy tactic refuses this source-shaped design at the exact first
generated child site.  Keep the refusal as a named hand-proof receipt: the
compositional equations below are usable, but no static flat twin is claimed.
-/
theorem noisy_hierarchy_refusal :
    CombHier.hierInsts noisyMul.pdesign noisyMul.plib =
      .error (CombHier.itemRefusal ppGen) := by
  rfl

theorem noisy_fault_row_index_affine_refusal :
    CombView.affOf? (.binary .mul (.genvarRef "i") (.paramRef "N" none)) = none := by
  rfl

theorem noisy_fault_row_index_affine_supported :
    CombView.affOf?
        (.binary (.m0 .sub)
          (.binary (.m0 .add) (.paramRef "N" none)
            (.binary (.m0 .mul) (.int 3) (.genvarRef "i"))) (.int 3)) =
      some { terms := [("N", 1), ("i", 3)], c := -3, qs := [], xs := [] } := by
  rfl

theorem noisy_bit_index_affine_supported :
    CombView.affOf? (.binary (.m0 .add) (.genvarRef "j") (.int 1)) =
      some { terms := [("j", 1)], c := 1, qs := [], xs := [] } := by
  rfl

theorem andInst_prefix (env : IEnv) (i j : Int) :
    andInst.prefix ((env.bindVal "i" i).bindVal "j" j) =
      .ok ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") := by
  simpa [andInst, String.append_assoc] using
    (generated_child_prefix_two env andInst "i" "j" "g_pp" "g_pp_j" i j
      (by decide) rfl)

end Examples.«system-verilog».sem2.noisy_mul_generate


namespace Examples.«system-verilog».sem2.noisy_mul_generate

/-- The source-shaped nested `g_pp`/`g_pp_j` expansion is the row-major family
of the per-leaf expansion.  The theorem keeps both symbolic bounds and does
not choose a child implementation; callers supply the ordinary leaf equation.
This is the hand-proof entry point for the generated-child multiplier. -/
theorem noisy_pp_expand_family
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (hFuel : N.toNat < F)
    (f : Int → Int → List Decl × List Process2)
    (hOuterBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hOuterValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N)
    (hBody : ∀ i j : Int, 0 ≤ i → i < N → 0 ≤ j → j < N →
      expandListH cb ((env.bindVal "i" i).bindVal "j" j) elems F [.inst andInst] =
        .ok (f i j)) :
    ppGen.expandH cb env elems F =
      .ok
        (List.flatMap
          (fun i => List.flatMap (fun j => (f i j).1)
            (intRange 0 N.toNat)) (intRange 0 N.toNat),
         List.flatMap
          (fun i => List.flatMap (fun j => (f i j).2)
            (intRange 0 N.toNat)) (intRange 0 N.toNat)) := by
  simpa [ppGen] using
    (generated_child_nested_family
      (cb := cb) (env := env) (elems := elems) (F := F)
      (outerLabel := some "g_pp") (innerLabel := some "g_pp_j")
      (outerG := "i") (innerG := "j")
      (outerInit := .int 0)
      (outerBound := .paramRef "N" none)
      (outerRc := some 4)
      (outerI0 := 0) (outerN := N)
      (innerInit := .int 0)
      (innerBound := .paramRef "N" none)
      (innerRc := some 4)
      (innerI0 := 0) (innerN := N)
      (inst := andInst) (f := f)
      (by simp) hOuterBound hOuterValue (by simpa using hFuel)
      (by intro i; simp)
      hInnerBound hInnerValue (by simpa using hFuel)
      (by simpa using hBody))

end Examples.«system-verilog».sem2.noisy_mul_generate

namespace Examples.«system-verilog».sem2.noisy_mul_generate

/-! The same source-shaped family with its valuation-dependent outer segments
retained until the final flattening step.  This is the concrete receipt for
the new hierarchy-summary representation; no generated name is made static. -/
theorem noisy_pp_expand_segments
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (hFuel : N.toNat < F)
    (f : Int → Int → List Decl × List Process2)
    (hOuterBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hOuterValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N)
    (hBody : ∀ i j : Int, 0 ≤ i → i < N → 0 ≤ j → j < N →
      expandListH cb ((env.bindVal "i" i).bindVal "j" j) elems F [.inst andInst] =
        .ok (f i j)) :
    ppGen.expandH cb env elems F =
      .ok (GeneratedChildSegment.flatten
        ((intRange 0 N.toNat).map fun i =>
          { decls := (intRange 0 N.toNat).flatMap fun j => (f i j).1,
            processes := (intRange 0 N.toNat).flatMap fun j => (f i j).2 })) := by
  simpa [ppGen] using
    (generated_child_nested_segments
      (cb := cb) (env := env) (elems := elems) (F := F)
      (outerLabel := some "g_pp") (innerLabel := some "g_pp_j")
      (outerG := "i") (innerG := "j")
      (outerInit := .int 0)
      (outerBound := .paramRef "N" none)
      (outerRc := some 4) (outerI0 := 0) (outerN := N)
      (innerInit := .int 0)
      (innerBound := .paramRef "N" none)
      (innerRc := some 4) (innerI0 := 0) (innerN := N)
      (inst := andInst) (f := f)
      (by simp) hOuterBound hOuterValue (by simpa using hFuel)
      (by intro i; simp) hInnerBound hInnerValue (by simpa using hFuel) hBody)

end Examples.«system-verilog».sem2.noisy_mul_generate

namespace Examples.«system-verilog».sem2.noisy_mul_generate

theorem noisy_pp_expand_actual_segments
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (hFuel : N.toNat < F) (child : Design2)
    (hOuterBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hOuterValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N)
    (hChild : ∀ i j : Int,
      cb ((env.bindVal "i" i).bindVal "j" j) andInst = .ok child) :
    ppGen.expandH cb env elems F =
      .ok (GeneratedChildSegment.flatten
        ((intRange 0 N.toNat).map fun i =>
          { decls := (intRange 0 N.toNat).flatMap fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst child).1,
            processes := (intRange 0 N.toNat).flatMap fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst child).2 })) := by
  apply noisy_pp_expand_segments cb env elems F N hFuel
    (fun i j => flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
      ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") andInst child)
    hOuterBound hOuterValue hInnerBound hInnerValue
  intro i j hi0 hiN hj0 hjN
  apply expandListH_singleton_ok (h := by simp [GenItem.instFree])
  rw [GenItem.expandH_inst]
  exact instExpandH_of
    (andInst_prefix env i j)
    (hChild i j)

end Examples.«system-verilog».sem2.noisy_mul_generate

namespace Examples.«system-verilog».sem2.noisy_mul_generate

/-- The nested `u_and` family expands to the ordinary flattened child at the
valuation-dependent lexical name `g_pp[i].g_pp_j[j].u_and.`. -/
theorem noisy_pp_expand_flatten
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (hFuel : N.toNat < F)
    (child : Design2)
    (hOuterBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hOuterValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N)
    (hChild : ∀ i j : Int,
      cb ((env.bindVal "i" i).bindVal "j" j) andInst = .ok child) :
    ppGen.expandH cb env elems F =
      .ok
        (List.flatMap
          (fun i => List.flatMap
            (fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst child).1)
            (intRange 0 N.toNat)) (intRange 0 N.toNat),
         List.flatMap
          (fun i => List.flatMap
            (fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst child).2)
            (intRange 0 N.toNat)) (intRange 0 N.toNat)) := by
  simpa [ppGen] using
    (generated_child_nested_flatten
      (cb := cb) (env := env) (elems := elems) (F := F)
      (outerLabel := some "g_pp") (innerLabel := some "g_pp_j")
      (outerG := "i") (innerG := "j")
      (outerInit := .int 0)
      (outerBound := .paramRef "N" none)
      (outerRc := some 4)
      (outerI0 := 0) (outerN := N)
      (innerInit := .int 0)
      (innerBound := .paramRef "N" none)
      (innerRc := some 4)
      (innerI0 := 0) (innerN := N)
      (inst := andInst) (child := child)
      (pref := fun i j =>
        "g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
      (by simp) hOuterBound hOuterValue (by simpa using hFuel)
      (by intro i; simp)
      hInnerBound hInnerValue (by simpa using hFuel)
      (by intro i j; exact andInst_prefix env i j)
      hChild)

end Examples.«system-verilog».sem2.noisy_mul_generate

namespace Examples.«system-verilog».sem2.noisy_mul_generate

def andDesign : Design2 :=
  { name := "and2f"
    decls := #[{ name := "a", width := 1, isInput := true },
               { name := "b", width := 1, isInput := true },
               { name := "f", width := 1, isInput := true },
               { name := "y", width := 1, isOutput := true }]
    processes :=
      #[.assign (.ident "y")
          (.binary .xor (.binary .and (.ident "a") (.ident "b")) (.ident "f"))] }

def andDef : PDesign :=
  { name := "and2f", params := [], localParams := [], enums := []
    decls := [{ name := "a", type := .packed [] (some 1), isInput := true },
              { name := "b", type := .packed [] (some 1), isInput := true },
              { name := "f", type := .packed [] (some 1), isInput := true },
              { name := "y", type := .packed [] (some 1), isOutput := true }]
    processes :=
      [.assign "y"
        (.binary (.m0 .xor) (.binary (.m0 .and) (.ident "a") (.ident "b")) (.ident "f"))]
    generates := [] }

theorem noisy_andDef : noisyMul.plib.head? = some andDef := by
  rfl

def ppLoops : List CombHier.GeneratedLoop :=
  [{ label := some "g_pp", genvar := "i", initE := .int 0,
     bound := .paramRef "N" none, step := .unary .inc (.genvarRef "i"), rc := some 4 },
   { label := some "g_pp_j", genvar := "j", initE := .int 0,
     bound := .paramRef "N" none, step := .unary .inc (.genvarRef "j"), rc := some 4 }]

theorem noisy_generated_child_ref :
    CombHier.generatedChildRefs noisyMul.plib ppLoops [.inst andInst] =
      .ok [{ loops := ppLoops, inst := andInst, child := andDef }] := by
  apply CombHier.generatedChildRefs_singleton
  · simp [ppLoops]
  · rfl



end Examples.«system-verilog».sem2.noisy_mul_generate

namespace Examples.«system-verilog».sem2.noisy_mul_generate

def andEnv : IEnv := { int32 := true, dims := dimTable { int32 := true } andDef.decls }

theorem and_paramEnvH : andDef.paramEnvH { int32 := true } [] = .ok andEnv := by
  rfl

theorem noisy_generated_child_segment :
    CombHier.GeneratedChildRef.segmentAt
        { loops := ppLoops, inst := andInst, child := andDef }
        andDesign ((andEnv.bindVal "i" 0).bindVal "j" 0) [] =
      .ok (flattenInst ((andEnv.bindVal "i" 0).bindVal "j" 0) []
        "g_pp[0].g_pp_j[0].u_and." andInst andDesign) := by
  apply CombHier.GeneratedChildRef.segmentAt_ok
  exact andInst_prefix andEnv 0 0


theorem and_decls : buildDecls andEnv andDef.decls = .ok andDesign.decls.toList := by
  simp [andDef, andDesign, andEnv, buildDecls, instDecl, PType.width_packed_nil]

def andElems : List (String × Nat) := [("a", 1), ("b", 1), ("f", 1), ("y", 1)]

theorem and_elems : buildElems andEnv andDef.decls = .ok andElems := by
  simp [andDef, andElems, andEnv, buildElems]

theorem noisy_and_child (env : IEnv) (F : Nat) (clocks : List String) :
    PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks env andInst = .ok andDesign := by
  rw [show noisyMul.plib = andDef :: noisyMul.plib.tail from by rfl]
  simp only [PDesign.childRec, childInstOf]
  have hg : PInst.given env andDef andInst = .ok [] := by
    simp [PInst.given, andDef, andInst]
    rfl
  have hp : andDef.atPoint [] = .ok (andDef, []) := rfl
  have hfind : (andDef :: noisyMul.plib.tail).find? (fun x => x.name == andInst.module) = some andDef := by
    rfl
  rw [hfind]
  simp only [hg, hp]
  have hasm : andDef.assembleH andEnv andDesign.decls.toList [] andElems [] = andDesign := by
    simp only [PDesign.assembleH, andDesign, andDef, List.append_nil, List.map_nil]
    sv2_inst_simp [andElems, andEnv]
  have hok : driversOk andDef.declNames andDef.inputNames andDesign.processes.toList = true := by
    decide
  rw [PDesign.instantiateRec_of_ok (depth := 0) (idecls := []) (gens := []) rfl
    and_paramEnvH and_decls and_elems (by simp [andDef]), hasm]
  simp only [Res.ok_bind, PDesign.driverGuard, Design2.driverGuard_of_ok hok]
  simp [Design2.clockGuard, clockGuardProc, Process2.clock?, andDesign]

end Examples.«system-verilog».sem2.noisy_mul_generate

namespace Examples.«system-verilog».sem2.noisy_mul_generate

/-- The actual child-recursion function for `noisy_mul` satisfies the nested
`u_and` expansion equation, once the parent environment has established the
symbolic `N` bounds. -/
theorem noisy_pp_expand_actual
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (clocks : List String) (hFuel : N.toNat < F)
    (hOuterBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hOuterValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N) :
    ppGen.expandH (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
      env elems F =
      .ok
        (List.flatMap
          (fun i => List.flatMap
            (fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst andDesign).1)
            (intRange 0 N.toNat)) (intRange 0 N.toNat),
         List.flatMap
          (fun i => List.flatMap
            (fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst andDesign).2)
            (intRange 0 N.toNat)) (intRange 0 N.toNat)) := by
  apply noisy_pp_expand_flatten
    (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
    env elems F N hFuel andDesign hOuterBound hOuterValue hInnerBound hInnerValue
  intro i j
  exact noisy_and_child _ F clocks

end Examples.«system-verilog».sem2.noisy_mul_generate

namespace Examples.«system-verilog».sem2.noisy_mul_generate

theorem noisy_row_shape_test :
    rowGen = GenItem.genFor (some "g_row") "i" (.int 1)
      (.binary .slt (.genvarRef "i") (.paramRef "N" none))
      (.unary .inc (.genvarRef "i")) (some 3) rowBody := by
  simp [rowGen, rowBody, noisyMul.pdesign]

theorem noisy_row_expand_segments
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (hFuel : (N - 1).toNat < F)
    (f : Int → List Decl × List Process2)
    (hBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hBody : ∀ i : Int, 1 ≤ i → i < N →
      expandListH cb (env.bindVal "i" i) elems F rowBody = .ok (f i)) :
    rowGen.expandH cb env elems F =
      .ok (GeneratedChildSegment.flatten
        ((intRange 1 (N - 1).toNat).map fun i =>
          let r := f i
          { decls := r.1, processes := r.2 })) := by
  simpa [rowGen, rowBody, noisyMul.pdesign] using
    (generated_family_body_segments
      (cb := cb) (env := env) (elems := elems) (F := F)
      (label := some "g_row") (g := "i")
      (initE := .int 1) (bound := .paramRef "N" none) (rc := some 3)
      (body := rowBody) (i0 := 1) (N := N) (f := f)
      (by simp) hBound hValue hFuel hBody)

end Examples.«system-verilog».sem2.noisy_mul_generate
