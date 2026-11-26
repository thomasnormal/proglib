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

def outGen : GenItem := noisyMul.pdesign.generates[2]!

def outBody : List GenItem :=
  match outGen with
  | .genFor _ _ _ _ _ _ body => body
  | _ => []

def outProc : PProcess :=
  .assignL (.bitSel "p" (.genvarRef "i"))
    (.arrayElem "s" [.genvarRef "i", .int 0])

theorem noisy_out_body_shape : outBody = [.process outProc] := by
  rfl

theorem noisy_out_body_expand
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (i : Int) :
    expandListH cb (env.bindVal "i" i) elems F outBody =
      .ok ([], [instProcess2 (env.bindVal "i" i) elems outProc]) := by
  rw [noisy_out_body_shape]
  simp [expandListH, expandList2, GenItem.listInstFree, GenItem.expand2_process,
    GenItem.expandH_process]

theorem noisy_out_expand_family
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (hFuel : N.toNat < F)
    (f : Int → List Decl × List Process2)
    (hBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hBody : ∀ i : Int, 0 ≤ i → i < N →
      expandListH cb (env.bindVal "i" i) elems F outBody = .ok (f i)) :
    outGen.expandH cb env elems F =
      .ok (GeneratedChildSegment.flatten
        ((intRange 0 N.toNat).map fun i =>
          { decls := (f i).1, processes := (f i).2 })) := by
  simpa [outGen, outBody, noisyMul.pdesign] using
    (generated_family_body_segments
      (cb := cb) (env := env) (elems := elems) (F := F)
      (label := some "g_out") (g := "i")
      (initE := .int 0) (bound := .paramRef "N" none) (rc := some 4)
      (body := outBody) (i0 := 0) (N := N) (f := f)
      (by simp) hBound hValue (by simpa using hFuel) hBody)

theorem noisy_out_expand_actual
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (clocks : List String) (hFuel : N.toNat < F)
    (hBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N) :
    outGen.expandH
        (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
        env elems F =
      .ok (GeneratedChildSegment.flatten
        ((intRange 0 N.toNat).map fun i =>
          { decls := [],
            processes := [instProcess2 (env.bindVal "i" i) elems outProc] })) := by
  apply noisy_out_expand_family
    (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
    env elems F N hFuel
    (fun i => ([], [instProcess2 (env.bindVal "i" i) elems outProc]))
    hBound hValue
  intro i hi0 hiN
  exact noisy_out_body_expand
    (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
    env elems F i

theorem noisy_out_expand_list_actual
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (hFuel : N.toNat < F)
    (hBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N) :
    expandListH cb env elems F [outGen] =
      .ok ([], (intRange 0 N.toNat).flatMap fun i =>
        [instProcess2 (env.bindVal "i" i) elems outProc]) := by
  rw [expandListH_of_instFree (by decide)]
  have hgen :
      outGen.expand2 env elems F =
        .ok ((intRange 0 N.toNat).flatMap fun i =>
          [instProcess2 (env.bindVal "i" i) elems outProc]) := by
    simpa [outGen, outBody, noisyMul.pdesign, noisy_out_body_shape, outProc] using
      (GenItem.expand2_genFor_ascending_processes
        (env := env) (elems := elems) (F := F)
        (label := some "g_out") (g := "i")
        (initE := .int 0) (e := .paramRef "N" none) (rc := some 4)
        (ps := [outProc]) (i0 := 0) (N := N)
        (by simp) hBound hValue (by simpa using hFuel))
  rw [expandList2_singleton_ok hgen]
  simp

theorem noisy_top_generates_shape : noisyMul.pdesign.generates = [ppGen, rowGen, outGen] := by
  rfl

theorem noisy_top_generated_expand
    {cb : ChildInst} {env : IEnv} {elems : List (String × Nat)} {F : Nat}
    {pp row out : List Decl × List Process2}
    (hpp : ppGen.expandH cb env elems F = .ok pp)
    (hrow : rowGen.expandH cb env elems F = .ok row)
    (hout : expandListH cb env elems F [outGen] = .ok out) :
    expandListH cb env elems F noisyMul.pdesign.generates =
      .ok (pp.1 ++ row.1 ++ out.1, pp.2 ++ row.2 ++ out.2) := by
  rw [noisy_top_generates_shape]
  have htail :
      expandListH cb env elems F [rowGen, outGen] =
        .ok (row.1 ++ out.1, row.2 ++ out.2) := by
    exact expandListH_cons_ok (it := rowGen) (rest := [outGen])
      (ds := row.1) (ps := row.2) (ds' := out.1) (qs := out.2)
      (h := by decide) hrow hout
  simpa [List.append_assoc] using
    (expandListH_cons_ok (it := ppGen) (rest := [rowGen, outGen])
      (ds := pp.1) (ps := pp.2)
      (ds' := row.1 ++ out.1) (qs := row.2 ++ out.2)
      (h := by decide) hpp htail)


/-! The hierarchy tactic refuses this source-shaped design at the exact first
generated child site.  Keep the refusal as a named hand-proof receipt: the
compositional equations below are usable, but no static flat twin is claimed.
-/
theorem noisy_hierarchy_refusal :
    CombHier.hierInsts noisyMul.pdesign noisyMul.plib =
      .error (CombHier.itemRefusal ppGen) := by
  rfl

set_option maxRecDepth 100000 in
theorem noisy_summary_refusal :
    CombHier.summaryH noisyMul.pdesign noisyMul.plib =
      .error
        "an instance sits inside the generate loop `g_pp` (genvar `i`): v1 of the hierarchy summary reads module-level instances only (one instance per loop iteration would make the child's sites a generate family whose names carry the loop index, which the summary does not build yet); the structure of such a design can be proved by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof)" := by
  rfl

theorem noisy_fault_row_index_affine_refusal :
    CombView.affOf? (.binary .mul (.genvarRef "i") (.paramRef "N" none)) = none := by
  rfl

theorem noisy_fault_row_major_index_in_range
    {N i j : Nat} (hi : i < N) (hj : j < N) :
    i * N + j < N * N := by
  exact rowMajor_lt hi hj

theorem noisy_fault_full_adder_index_in_range
    {N i j q : Nat} (hN : 1 ≤ N) (hi : 1 ≤ i) (hiN : i < N)
    (hj : j < N) (hq : q < 3) :
    (N + 3 * (i - 1) + q) * N + j < (4 * N - 3) * N := by
  apply rowMajor_lt (rows := 4 * N - 3) (cols := N)
  · omega
  · exact hj

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

def xorDesign : Design2 :=
  { name := "xor2f"
    decls := #[{ name := "a", width := 1, isInput := true },
               { name := "b", width := 1, isInput := true },
               { name := "f", width := 1, isInput := true },
               { name := "y", width := 1, isOutput := true }]
    processes :=
      #[.assign (.ident "y")
          (.binary .xor (.binary .xor (.ident "a") (.ident "b")) (.ident "f"))] }

def majDesign : Design2 :=
  { name := "maj3f"
    decls := #[{ name := "a", width := 1, isInput := true },
               { name := "b", width := 1, isInput := true },
               { name := "c", width := 1, isInput := true },
               { name := "f", width := 1, isInput := true },
               { name := "y", width := 1, isOutput := true }]
    processes :=
      #[.assign (.ident "y")
          (.binary .xor
            (.binary .or
              (.binary .or
                (.binary .and (.ident "a") (.ident "b"))
                (.binary .and (.ident "a") (.ident "c")))
              (.binary .and (.ident "b") (.ident "c")))
            (.ident "f"))] }

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

def xorDef : PDesign :=
  { name := "xor2f", params := [], localParams := [], enums := []
    decls := [{ name := "a", type := .packed [] (some 1), isInput := true },
              { name := "b", type := .packed [] (some 1), isInput := true },
              { name := "f", type := .packed [] (some 1), isInput := true },
              { name := "y", type := .packed [] (some 1), isOutput := true }]
    processes :=
      [.assign "y"
        (.binary (.m0 .xor) (.binary (.m0 .xor) (.ident "a") (.ident "b")) (.ident "f"))]
    generates := [] }

def majDef : PDesign :=
  { name := "maj3f", params := [], localParams := [], enums := []
    decls := [{ name := "a", type := .packed [] (some 1), isInput := true },
              { name := "b", type := .packed [] (some 1), isInput := true },
              { name := "c", type := .packed [] (some 1), isInput := true },
              { name := "f", type := .packed [] (some 1), isInput := true },
              { name := "y", type := .packed [] (some 1), isOutput := true }]
    processes :=
      [.assign "y"
        (.binary (.m0 .xor)
          (.binary (.m0 .or)
            (.binary (.m0 .or)
              (.binary (.m0 .and) (.ident "a") (.ident "b"))
              (.binary (.m0 .and) (.ident "a") (.ident "c")))
            (.binary (.m0 .and) (.ident "b") (.ident "c")))
          (.ident "f"))]
    generates := [] }

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

theorem noisy_generated_child_nested_ref :
    CombHier.generatedChildRefs noisyMul.plib []
      [.genFor (some "g_pp") "i" (.int 0) (.paramRef "N" none)
        (.unary .inc (.genvarRef "i")) (some 4)
        [.genFor (some "g_pp_j") "j" (.int 0) (.paramRef "N" none)
          (.unary .inc (.genvarRef "j")) (some 4) [.inst andInst]]] =
      .ok [{ loops := ppLoops, inst := andInst, child := andDef }] := by
  simpa [ppLoops] using
    (CombHier.generatedChildRefs_genFor_nested_singleton
      (lib := noisyMul.plib) (loops := [])
      (outerLabel := some "g_pp") (outerG := "i")
      (outerInit := .int 0) (outerBound := .paramRef "N" none)
      (outerStep := .unary .inc (.genvarRef "i")) (outerRc := some 4)
      (innerLabel := some "g_pp_j") (innerG := "j")
      (innerInit := .int 0) (innerBound := .paramRef "N" none)
      (innerStep := .unary .inc (.genvarRef "j")) (innerRc := some 4)
      (i := andInst) (c := andDef) (by simp) (by rfl))



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

def xorEnv : IEnv := { int32 := true, dims := dimTable { int32 := true } xorDef.decls }

theorem xor_paramEnvH : xorDef.paramEnvH { int32 := true } [] = .ok xorEnv := by
  rfl

def xorElems : List (String × Nat) := [("a", 1), ("b", 1), ("f", 1), ("y", 1)]

theorem xor_decls : buildDecls xorEnv xorDef.decls = .ok xorDesign.decls.toList := by
  simp [xorDef, xorDesign, xorEnv, buildDecls, instDecl, PType.width_packed_nil]

theorem xor_elems : buildElems xorEnv xorDef.decls = .ok xorElems := by
  simp [xorDef, xorElems, xorEnv, buildElems]


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

def rowLeft : PProcess :=
  .assignL (.arrayElem "c" [.genvarRef "i", .int 0]) (.lit ⟨#[.l0]⟩)

def rowRight : PProcess :=
  .assignL (.arrayElem "s" [.genvarRef "i", .paramRef "N" none])
    (.arrayElem "c" [.genvarRef "i", .paramRef "N" none])

def rowInnerBody : List GenItem :=
  match rowBody with
  | .process _ :: .genFor _ _ _ _ _ _ body :: .process _ :: [] => body
  | _ => []

def xorInst : PInst :=
  { name := "u_t", module := "xor2f",
    path := [{ label := "g_row", genvar := some "i" }, { label := "g_bit", genvar := some "j" }],
    conns :=
      [.input "a" (some (.arrayElem "s" [.binary (.m0 .sub) (.genvarRef "i") (.int 1),
        .binary (.m0 .add) (.genvarRef "j") (.int 1)])) false,
       .input "b" (some (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"])) false,
       .input "f" (some (.arrayElem "f" [.binary (.m0 .sub)
         (.binary (.m0 .add) (.paramRef "N" none) (.binary .mul (.int 3) (.genvarRef "i"))) (.int 3),
         (.genvarRef "j")])) false,
       .output "y" (some (.arrayElem "t" [.genvarRef "i", .genvarRef "j"]))] }

def majInst : PInst :=
  { name := "u_c", module := "maj3f",
    path := [{ label := "g_row", genvar := some "i" }, { label := "g_bit", genvar := some "j" }],
    conns :=
      [.input "a" (some (.arrayElem "s" [.binary (.m0 .sub) (.genvarRef "i") (.int 1),
        .binary (.m0 .add) (.genvarRef "j") (.int 1)])) false,
       .input "b" (some (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"])) false,
       .input "c" (some (.arrayElem "c" [.genvarRef "i", .genvarRef "j"])) false,
       .input "f" (some (.arrayElem "f" [.binary (.m0 .sub)
         (.binary (.m0 .add) (.paramRef "N" none) (.binary .mul (.int 3) (.genvarRef "i"))) (.int 1),
         (.genvarRef "j")])) false,
       .output "y" (some (.arrayElem "c" [.genvarRef "i", .binary (.m0 .add) (.genvarRef "j") (.int 1)]))] }

def xorSInst : PInst :=
  { name := "u_s", module := "xor2f", path := xorInst.path,
    conns :=
      [.input "a" (some (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])) false,
       .input "b" (some (.arrayElem "c" [.genvarRef "i", .genvarRef "j"])) false,
       .input "f" (some (.arrayElem "f" [.binary (.m0 .sub)
         (.binary (.m0 .add) (.paramRef "N" none) (.binary .mul (.int 3) (.genvarRef "i"))) (.int 2),
         (.genvarRef "j")])) false,
       .output "y" (some (.arrayElem "s" [.genvarRef "i", .genvarRef "j"]))] }

theorem noisy_row_body_shape :
    rowBody = [GenItem.process rowLeft,
      .genFor (some "g_bit") "j" (.int 0)
        (.binary .slt (.genvarRef "j") (.paramRef "N" none))
        (.unary .inc (.genvarRef "j")) (some 4) rowInnerBody,
      GenItem.process rowRight] := by
  rfl

def rowLoop : CombHier.GeneratedLoop :=
  { label := some "g_row", genvar := "i", initE := .int 1,
    bound := .paramRef "N" none, step := .unary .inc (.genvarRef "i"), rc := some 3 }

def outLoop : CombHier.GeneratedLoop :=
  { label := some "g_out", genvar := "i", initE := .int 0,
    bound := .paramRef "N" none, step := .unary .inc (.genvarRef "i"), rc := some 4 }

theorem noisy_row_inner_shape :
    rowInnerBody = [.inst xorInst, .inst xorSInst,
      .inst majInst] := by
  rfl

theorem noisy_row_inner_instFree : GenItem.listInstFree rowInnerBody = false := by
  rw [noisy_row_inner_shape]
  decide

theorem noisy_xor_child (env : IEnv) (F : Nat) (clocks : List String) :
    PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks env xorInst = .ok xorDesign := by
  rw [show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  simp only [PDesign.childRec, childInstOf]
  have hg : PInst.given env xorDef xorInst = .ok [] := by
    simp [PInst.given, xorDef]
    rfl
  have hp : xorDef.atPoint [] = .ok (xorDef, []) := rfl
  have hfind : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == xorInst.module) = some xorDef := by
    simp [andDef, xorInst, xorDef]
  rw [hfind]
  simp only [hg, hp]
  have hasm : xorDef.assembleH xorEnv xorDesign.decls.toList [] xorElems [] = xorDesign := by
    simp only [PDesign.assembleH, xorDesign, xorDef, List.append_nil, List.map_nil]
    sv2_inst_simp [xorElems, xorEnv]
  have hok : driversOk xorDef.declNames xorDef.inputNames xorDesign.processes.toList = true := by
    decide
  rw [PDesign.instantiateRec_of_ok (depth := 0) (idecls := []) (gens := []) rfl
    xor_paramEnvH xor_decls xor_elems (by simp [xorDef]), hasm]
  simp only [Res.ok_bind, PDesign.driverGuard, Design2.driverGuard_of_ok hok]
  simp [Design2.clockGuard, clockGuardProc, Process2.clock?, xorDesign]

theorem xorS_prefix (env : IEnv) (i j : Int) :
    xorSInst.prefix ((env.bindVal "i" i).bindVal "j" j) =
      .ok ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") := by
  simpa [xorSInst, String.append_assoc] using
    (generated_child_prefix_two env xorSInst "i" "j" "g_row" "g_bit" i j (by decide) rfl)

theorem xorInst_prefix (env : IEnv) (i j : Int) :
    xorInst.prefix ((env.bindVal "i" i).bindVal "j" j) =
      .ok ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") := by
  simpa [xorInst, String.append_assoc] using
    (generated_child_prefix_two env xorInst "i" "j" "g_row" "g_bit" i j (by decide) rfl)

theorem majInst_prefix (env : IEnv) (i j : Int) :
    majInst.prefix ((env.bindVal "i" i).bindVal "j" j) =
      .ok ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") := by
  simpa [majInst, String.append_assoc] using
    (generated_child_prefix_two env majInst "i" "j" "g_row" "g_bit" i j (by decide) rfl)

theorem noisy_xorS_child (env : IEnv) (F : Nat) (clocks : List String) :
    PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks env xorSInst = .ok xorDesign := by
  rw [show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  simp only [PDesign.childRec, childInstOf]
  have hg : PInst.given env xorDef xorSInst = .ok [] := by
    simp [PInst.given, xorDef]
    rfl
  have hp : xorDef.atPoint [] = .ok (xorDef, []) := rfl
  have hfind : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == xorSInst.module) = some xorDef := by
    simp [andDef, xorSInst, xorDef]
  rw [hfind]
  simp only [hg, hp]
  have hasm : xorDef.assembleH xorEnv xorDesign.decls.toList [] xorElems [] = xorDesign := by
    simp only [PDesign.assembleH, xorDesign, xorDef, List.append_nil, List.map_nil]
    sv2_inst_simp [xorElems, xorEnv]
  have hok : driversOk xorDef.declNames xorDef.inputNames xorDesign.processes.toList = true := by
    decide
  rw [PDesign.instantiateRec_of_ok (depth := 0) (idecls := []) (gens := []) rfl
    xor_paramEnvH xor_decls xor_elems (by simp [xorDef]), hasm]
  simp only [Res.ok_bind, PDesign.driverGuard, Design2.driverGuard_of_ok hok]
  simp [Design2.clockGuard, clockGuardProc, Process2.clock?, xorDesign]

theorem noisy_row_inner_expand
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (i j : Int) (childT childS childC : Design2)
    (hT : cb ((env.bindVal "i" i).bindVal "j" j) xorInst = .ok childT)
    (hS : cb ((env.bindVal "i" i).bindVal "j" j) xorSInst = .ok childS)
    (hC : cb ((env.bindVal "i" i).bindVal "j" j) majInst = .ok childC) :
    expandListH cb ((env.bindVal "i" i).bindVal "j" j) elems F rowInnerBody =
      .ok
        ((flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst childT).1 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst childS).1 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst childC).1,
         (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst childT).2 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst childS).2 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst childC).2) := by
  have h1 : (GenItem.inst xorInst).expandH cb ((env.bindVal "i" i).bindVal "j" j) elems F =
      .ok (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
        ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst childT) := by
    rw [GenItem.expandH_inst]
    exact instExpandH_of (xorInst_prefix env i j) hT
  have h2 : (GenItem.inst xorSInst).expandH cb ((env.bindVal "i" i).bindVal "j" j) elems F =
      .ok (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
        ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst childS) := by
    rw [GenItem.expandH_inst]
    exact instExpandH_of (xorS_prefix env i j) hS
  have h3 : (GenItem.inst majInst).expandH cb ((env.bindVal "i" i).bindVal "j" j) elems F =
      .ok (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
        ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst childC) := by
    rw [GenItem.expandH_inst]
    exact instExpandH_of (majInst_prefix env i j) hC
  rw [noisy_row_inner_shape]
  have hr : expandListH cb ((env.bindVal "i" i).bindVal "j" j) elems F
      [.inst xorSInst, .inst majInst] =
      .ok ((flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst childS).1 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst childC).1,
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst childS).2 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst childC).2) := by
    exact expandListH_cons_ok (it := .inst xorSInst) (rest := [.inst majInst])
      (ds := (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
        ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst childS).1)
      (ps := (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
        ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst childS).2)
      (h := by simp [GenItem.listInstFree, GenItem.instFree]) h2
      (expandListH_singleton_ok (it := .inst majInst) (h := by simp [GenItem.instFree]) h3)
  simpa [List.append_assoc] using
    (expandListH_cons_ok (it := .inst xorInst) (rest := [.inst xorSInst, .inst majInst])
      (ds := (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
        ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst childT).1)
      (ps := (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
        ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst childT).2)
      (h := by simp [GenItem.listInstFree, GenItem.instFree]) h1 hr)


def majEnv : IEnv := { int32 := true, dims := dimTable { int32 := true } majDef.decls }

theorem maj_paramEnvH : majDef.paramEnvH { int32 := true } [] = .ok majEnv := by
  rfl

def majElems : List (String × Nat) :=
  [("a", 1), ("b", 1), ("c", 1), ("f", 1), ("y", 1)]

theorem maj_decls : buildDecls majEnv majDef.decls = .ok majDesign.decls.toList := by
  simp [majDef, majDesign, majEnv, buildDecls, instDecl, PType.width_packed_nil]

theorem maj_elems : buildElems majEnv majDef.decls = .ok majElems := by
  simp [majDef, majElems, majEnv, buildElems]

theorem noisy_maj_child (env : IEnv) (F : Nat) (clocks : List String) :
    PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks env majInst = .ok majDesign := by
  rw [show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  simp only [PDesign.childRec, childInstOf]
  have hg : PInst.given env majDef majInst = .ok [] := by
    simp [PInst.given, majDef]
    rfl
  have hp : majDef.atPoint [] = .ok (majDef, []) := rfl
  have hfind : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == majInst.module) = some majDef := by
    simp [andDef, xorDef, majDef, majInst]
  rw [hfind]
  simp only [hg, hp]
  have hasm : majDef.assembleH majEnv majDesign.decls.toList [] majElems [] = majDesign := by
    simp only [PDesign.assembleH, majDesign, majDef, List.append_nil, List.map_nil]
    sv2_inst_simp [majElems, majEnv]
  have hok : driversOk majDef.declNames majDef.inputNames majDesign.processes.toList = true := by
    decide
  rw [PDesign.instantiateRec_of_ok (depth := 0) (idecls := []) (gens := []) rfl
    maj_paramEnvH maj_decls maj_elems (by simp [majDef]), hasm]
  simp only [Res.ok_bind, PDesign.driverGuard, Design2.driverGuard_of_ok hok]
  simp [Design2.clockGuard, clockGuardProc, Process2.clock?, majDesign]

def rowInnerLoops : List CombHier.GeneratedLoop :=
  [{ label := some "g_row", genvar := "i", initE := .int 1,
     bound := .paramRef "N" none, step := .unary .inc (.genvarRef "i"), rc := some 3 },
   { label := some "g_bit", genvar := "j", initE := .int 0,
     bound := .paramRef "N" none, step := .unary .inc (.genvarRef "j"), rc := some 4 }]

theorem noisy_generated_process_child_order :
    CombHier.generatedNodes noisyMul.plib []
        [.genFor (some "g_row") "i" (.int 1) (.paramRef "N" none)
          (.unary .inc (.genvarRef "i")) (some 3)
          [.process rowLeft, .inst xorInst]] =
      .ok [
        .process [rowLoop] rowLeft,
        .child { loops := [rowLoop], inst := xorInst, child := xorDef }] := by
  rw [show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  have hx : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == xorInst.module) = some xorDef := by
    simp [andDef, xorInst, xorDef]
  simpa [rowLoop] using
    (CombHier.generatedNodes_genFor_process_child_order
      (lib := [andDef, xorDef, majDef])
      (label := some "g_row") (g := "i")
      (initE := .int 1) (bound := .paramRef "N" none)
      (step := .unary .inc (.genvarRef "i")) (rc := some 3)
      (p := rowLeft) (i := xorInst) (c := xorDef) hx)

def ppSourceLoops : List CombHier.GeneratedLoop :=
  [{ label := some "g_pp", genvar := "i", initE := .int 0,
     bound := .binary .slt (.genvarRef "i") (.paramRef "N" none),
     step := .unary .inc (.genvarRef "i"), rc := some 4 },
   { label := some "g_pp_j", genvar := "j", initE := .int 0,
     bound := .binary .slt (.genvarRef "j") (.paramRef "N" none),
     step := .unary .inc (.genvarRef "j"), rc := some 4 }]

def rowSourceLoop : CombHier.GeneratedLoop :=
  { label := some "g_row", genvar := "i", initE := .int 1,
    bound := .binary .slt (.genvarRef "i") (.paramRef "N" none),
    step := .unary .inc (.genvarRef "i"), rc := some 3 }

def bitSourceLoop : CombHier.GeneratedLoop :=
  { label := some "g_bit", genvar := "j", initE := .int 0,
    bound := .binary .slt (.genvarRef "j") (.paramRef "N" none),
    step := .unary .inc (.genvarRef "j"), rc := some 4 }

def outSourceLoop : CombHier.GeneratedLoop :=
  { label := some "g_out", genvar := "i", initE := .int 0,
    bound := .binary .slt (.genvarRef "i") (.paramRef "N" none),
    step := .unary .inc (.genvarRef "i"), rc := some 4 }

def rowSourceLoops : List CombHier.GeneratedLoop := [rowSourceLoop, bitSourceLoop]

def noisyTopSourceNodes : List CombHier.GeneratedNode :=
  [.child { loops := ppSourceLoops, inst := andInst, child := andDef },
   .process [rowSourceLoop] rowLeft,
   .child { loops := rowSourceLoops, inst := xorInst, child := xorDef },
   .child { loops := rowSourceLoops, inst := xorSInst, child := xorDef },
   .child { loops := rowSourceLoops, inst := majInst, child := majDef },
   .process [rowSourceLoop] rowRight,
   .process [outSourceLoop] outProc]

theorem noisy_generated_source_order :
    CombHier.generatedNodes noisyMul.plib [] noisyMul.pdesign.generates =
      .ok noisyTopSourceNodes := by
  rw [noisy_top_generates_shape, noisy_row_shape_test, noisy_row_body_shape,
    noisy_row_inner_shape, show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  have ha : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == andInst.module) = some andDef := by
    simp [andDef, andInst]
  have hx : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == xorInst.module) = some xorDef := by
    simp [andDef, xorInst, xorDef]
  have hs : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == xorSInst.module) = some xorDef := by
    simp [andDef, xorSInst, xorDef]
  have hm : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == majInst.module) = some majDef := by
    simp [andDef, xorDef, majInst, majDef]
  simp [CombHier.generatedNodes, ppGen, rowGen, outGen, rowBody, rowInnerBody,
    noisyMul.pdesign, ppLoops, rowLoop, rowInnerLoops, outLoop, ppSourceLoops,
    rowSourceLoop, bitSourceLoop, outSourceLoop, rowSourceLoops, outProc, noisyTopSourceNodes,
    ha, hx, hs, hm, Except.bind, Except.pure, pure, Functor.map, Except.map,
    bind, List.append_assoc]

theorem noisy_generated_row_inner_refs :
    CombHier.generatedChildRefs noisyMul.plib []
      [.genFor (some "g_row") "i" (.int 1) (.paramRef "N" none)
        (.unary .inc (.genvarRef "i")) (some 3)
        [.genFor (some "g_bit") "j" (.int 0) (.paramRef "N" none)
          (.unary .inc (.genvarRef "j")) (some 4) rowInnerBody]] =
      .ok [{ loops := rowInnerLoops, inst := xorInst, child := xorDef },
           { loops := rowInnerLoops, inst := xorSInst, child := xorDef },
           { loops := rowInnerLoops, inst := majInst, child := majDef }] := by
  rw [noisy_row_inner_shape]
  rw [show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  have hx : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == xorInst.module) = some xorDef := by
    simp [andDef, xorInst, xorDef]
  have hs : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == xorSInst.module) = some xorDef := by
    simp [andDef, xorSInst, xorDef]
  have hm : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == majInst.module) = some majDef := by
    simp [andDef, xorDef, majDef, majInst]
  simp [rowInnerLoops, CombHier.generatedChildRefs, hx, hs, hm, Except.bind, Except.pure, pure, Functor.map, Except.map]
  rfl

def noisyGeneratedRowInnerPairs :
    List (CombHier.GeneratedChildRef × Design2) :=
  [({ loops := rowInnerLoops, inst := xorInst, child := xorDef }, xorDesign),
   ({ loops := rowInnerLoops, inst := xorSInst, child := xorDef }, xorDesign),
   ({ loops := rowInnerLoops, inst := majInst, child := majDef }, majDesign)]

def noisyGeneratedRowInnerPairSegment
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    CombHier.GeneratedChildRef × Design2 → List Decl × List Process2
  | (r, _) =>
      if r.inst.name == xorInst.name then
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign
      else if r.inst.name == xorSInst.name then
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign
      else
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign

theorem noisy_generated_row_inner_segments
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    noisyGeneratedRowInnerPairs.mapM
      (fun r => r.1.segmentAt r.2
        ((env.bindVal "i" i).bindVal "j" j) elems) =
      .ok (noisyGeneratedRowInnerPairs.map
        (noisyGeneratedRowInnerPairSegment env elems i j)) := by
  apply (CombHier.generatedChildRefPairs_segmentAt_mapM_ok
    (rs := noisyGeneratedRowInnerPairs)
    (env := fun _ => (env.bindVal "i" i).bindVal "j" j)
    (elems := elems)
    (seg := noisyGeneratedRowInnerPairSegment env elems i j))
  intro r hr
  have hst : xorSInst.name ≠ xorInst.name := by decide
  have hmt : majInst.name ≠ xorInst.name := by decide
  have hms : majInst.name ≠ xorSInst.name := by decide
  simp only [noisyGeneratedRowInnerPairs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · simpa [noisyGeneratedRowInnerPairSegment] using
      (CombHier.GeneratedChildRef.segmentAt_ok (xorInst_prefix env i j))
  rcases hr with rfl | hr
  · simpa [noisyGeneratedRowInnerPairSegment, hst, hmt] using
      (CombHier.GeneratedChildRef.segmentAt_ok (xorS_prefix env i j))
  rcases hr with rfl | hr
  · simpa [noisyGeneratedRowInnerPairSegment, hmt, hms] using
      (CombHier.GeneratedChildRef.segmentAt_ok (majInst_prefix env i j))
  simp at hr

theorem noisy_row_expand_process_family
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (hFuel : (N - 1).toNat < F)
    (f : Int → List Decl × List Process2)
    (hBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerInit : ∀ i : Int, evalInt (env.bindVal "i" i) (.int 0) = .ok 0)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N)
    (hInnerFuel : N.toNat < F)
    (hInnerInst : GenItem.listInstFree rowInnerBody = false)
    (hInner : ∀ i : Int, 1 ≤ i → i < N →
      expandListH cb (env.bindVal "i" i) elems F
        [.genFor (some "g_bit") "j" (.int 0)
          (.binary .slt (.genvarRef "j") (.paramRef "N" none))
          (.unary .inc (.genvarRef "j")) (some 4) rowInnerBody] =
        .ok (f i)) :
    rowGen.expandH cb env elems F =
      .ok (GeneratedChildSegment.flatten
        ((intRange 1 (N - 1).toNat).map fun i =>
          { decls := (f i).1,
            processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
              (f i).2 ++ [instProcess2 (env.bindVal "i" i) elems rowRight] })) := by
  simpa [rowGen, rowBody, rowInnerBody, rowLeft, rowRight, noisyMul.pdesign] using
    (generated_child_nested_with_processes
      (cb := cb) (env := env) (elems := elems) (F := F)
      (outerG := "i") (innerG := "j")
      (outerLabel := some "g_row") (innerLabel := some "g_bit")
      (outerInit := .int 1) (outerBound := .paramRef "N" none)
      (innerInit := .int 0) (innerBound := .paramRef "N" none)
      (outerRc := some 3) (innerRc := some 4)
      (outerI0 := 1) (outerN := N) (innerI0 := 0) (innerN := N)
      (left := rowLeft) (right := rowRight) (innerBody := rowInnerBody)
      (f := f)
      (by simp) hBound hValue hFuel
      hInnerInit hInnerBound hInnerValue (by simpa using hInnerFuel) hInnerInst hInner)

theorem noisy_row_inner_expand_actual
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (i j N : Int) (clocks : List String) (hFuel : N.toNat < F)
    (hPrefix : 1 ≤ i) :
    expandListH (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
      ((env.bindVal "i" i).bindVal "j" j) elems F rowInnerBody =
      .ok ((flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).1 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).1 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).1,
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).2 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).2 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).2) := by
  apply noisy_row_inner_expand
  · exact noisy_xor_child _ F clocks
  · exact noisy_xorS_child _ F clocks
  · exact noisy_maj_child _ F clocks


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

namespace Examples.«system-verilog».sem2.noisy_mul_generate

theorem noisy_bit_expand_segments
    (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N i : Int) (hFuel : N.toNat < F)
    (f : Int → List Decl × List Process2)
    (hBound : ∀ j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hValue : ∀ j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N)
    (hBody : ∀ j : Int, 0 ≤ j → j < N →
      expandListH cb ((env.bindVal "i" i).bindVal "j" j) elems F rowInnerBody =
        .ok (f j)) :
    expandListH cb (env.bindVal "i" i) elems F
      [.genFor (some "g_bit") "j" (.int 0)
        (.binary .slt (.genvarRef "j") (.paramRef "N" none))
        (.unary .inc (.genvarRef "j")) (some 4) rowInnerBody] =
      .ok (GeneratedChildSegment.flatten
        ((intRange 0 N.toNat).map fun j =>
          { decls := (f j).1, processes := (f j).2 })) := by
  apply expandListH_singleton_ok
    (it := .genFor (some "g_bit") "j" (.int 0)
      (.binary .slt (.genvarRef "j") (.paramRef "N" none))
      (.unary .inc (.genvarRef "j")) (some 4) rowInnerBody)
    (h := by simp [noisy_row_inner_instFree, GenItem.listInstFree, GenItem.instFree])
  simpa [GeneratedChildSegment.flatten, List.flatMap_map] using
    (generated_family_body_segments
      (cb := cb) (env := env.bindVal "i" i) (elems := elems) (F := F)
      (label := some "g_bit") (g := "j") (initE := .int 0)
      (bound := .paramRef "N" none) (rc := some 4) (body := rowInnerBody)
      (i0 := 0) (N := N) (f := f)
      (by simp) hBound hValue (by simpa using hFuel)
      hBody)

theorem noisy_row_inner_family_actual
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (i N : Int) (clocks : List String) (hFuel : N.toNat < F)
    (hPrefix : 1 ≤ i)
    (hBound : ∀ j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hValue : ∀ j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N) :
    expandListH (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
      (env.bindVal "i" i) elems F
      [.genFor (some "g_bit") "j" (.int 0)
        (.binary .slt (.genvarRef "j") (.paramRef "N" none))
        (.unary .inc (.genvarRef "j")) (some 4) rowInnerBody] =
      .ok (GeneratedChildSegment.flatten
        ((intRange 0 N.toNat).map fun j =>
          { decls :=
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).1 ++
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).1 ++
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).1,
            processes :=
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).2 ++
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).2 ++
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).2 })) := by
  apply noisy_bit_expand_segments
    (cb := PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
    (env := env) (elems := elems) (F := F) (N := N) (i := i)
    (hFuel := hFuel)
    (f := fun j =>
      ((flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).1 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).1 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).1,
       (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).2 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).2 ++
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).2))
    hBound hValue
    (by
      intro j hj0 hjN
      simpa using
        (noisy_row_inner_expand_actual env elems F i j N clocks hFuel hPrefix))

def noisy_row_inner_segment
    (env : IEnv) (elems : List (String × Nat)) (i N : Int) :
    List Decl × List Process2 :=
  GeneratedChildSegment.flatten
    ((intRange 0 N.toNat).map fun j =>
      { decls :=
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).1 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).1 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).1,
        processes :=
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).2 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).2 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).2 })

theorem noisy_row_expand_process_family_exact
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (clocks : List String) (hFuel : (N - 1).toNat < F)
    (hBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N)
    (hInnerFuel : N.toNat < F) :
    rowGen.expandH (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
        env elems F =
      .ok (GeneratedChildSegment.flatten
        ((intRange 1 (N - 1).toNat).map fun i =>
          { decls := (noisy_row_inner_segment env elems i N).1,
            processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
              (noisy_row_inner_segment env elems i N).2 ++
              [instProcess2 (env.bindVal "i" i) elems rowRight] })) := by
  apply noisy_row_expand_process_family
    (cb := PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
    (env := env) (elems := elems) (F := F) (N := N) (hFuel := hFuel)
    (f := fun i => noisy_row_inner_segment env elems i N)
    hBound hValue (by intro i; simp) hInnerBound hInnerValue hInnerFuel
    noisy_row_inner_instFree
  intro i hi hN
  simpa [noisy_row_inner_segment] using
    (noisy_row_inner_family_actual env elems F i N clocks hInnerFuel hi
      (fun j => hInnerBound i j) (fun j => hInnerValue i j))

theorem noisy_top_expand_actual
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (clocks : List String)
    (hFuel : N.toNat < F)
    (hRowFuel : (N - 1).toNat < F)
    (hBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N) :
    expandListH
        (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
        env elems F noisyMul.pdesign.generates =
      .ok
        ((List.flatMap
          (fun i => List.flatMap
            (fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst andDesign).1)
            (intRange 0 N.toNat)) (intRange 0 N.toNat)) ++
          (GeneratedChildSegment.flatten
            ((intRange 1 (N - 1).toNat).map fun i =>
              { decls := (noisy_row_inner_segment env elems i N).1,
                processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
                  (noisy_row_inner_segment env elems i N).2 ++
                  [instProcess2 (env.bindVal "i" i) elems rowRight] })).1 ++
          [],
         (List.flatMap
          (fun i => List.flatMap
            (fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst andDesign).2)
            (intRange 0 N.toNat)) (intRange 0 N.toNat)) ++
          (GeneratedChildSegment.flatten
            ((intRange 1 (N - 1).toNat).map fun i =>
              { decls := (noisy_row_inner_segment env elems i N).1,
                processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
                  (noisy_row_inner_segment env elems i N).2 ++
                  [instProcess2 (env.bindVal "i" i) elems rowRight] })).2 ++
          (intRange 0 N.toNat).flatMap fun i =>
            [instProcess2 (env.bindVal "i" i) elems outProc]) := by
  refine noisy_top_generated_expand
    (pp :=
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
        (intRange 0 N.toNat)) (intRange 0 N.toNat)))
    (row :=
      ((GeneratedChildSegment.flatten
        ((intRange 1 (N - 1).toNat).map fun i =>
          { decls := (noisy_row_inner_segment env elems i N).1,
            processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
              (noisy_row_inner_segment env elems i N).2 ++
              [instProcess2 (env.bindVal "i" i) elems rowRight] })).1,
       (GeneratedChildSegment.flatten
        ((intRange 1 (N - 1).toNat).map fun i =>
          { decls := (noisy_row_inner_segment env elems i N).1,
            processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
              (noisy_row_inner_segment env elems i N).2 ++
              [instProcess2 (env.bindVal "i" i) elems rowRight] })).2))
    (out := ([], (intRange 0 N.toNat).flatMap fun i =>
      [instProcess2 (env.bindVal "i" i) elems outProc]))
    ?_ ?_ ?_
  · exact noisy_pp_expand_actual env elems F N clocks hFuel
      hBound hValue hInnerBound hInnerValue
  · exact noisy_row_expand_process_family_exact env elems F N clocks hRowFuel
      hBound hValue hInnerBound hInnerValue hFuel
  · exact noisy_out_expand_list_actual
      (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
      env elems F N hFuel hBound hValue

def noisyTopGeneratedRefs : List CombHier.GeneratedChildRef :=
  [{ loops := ppLoops, inst := andInst, child := andDef },
   { loops := rowInnerLoops, inst := xorInst, child := xorDef },
   { loops := rowInnerLoops, inst := xorSInst, child := xorDef },
   { loops := rowInnerLoops, inst := majInst, child := majDef }]

theorem noisy_top_generated_refs :
    CombHier.generatedChildRefs noisyMul.plib [] noisyMul.pdesign.generates =
      .error "generated child family contains a process sibling; use the process-aware family rule" := by
  rw [noisy_top_generates_shape]
  rw [noisy_row_shape_test]
  rw [show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  have ha : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == andInst.module) = some andDef := by
    simp [andDef, andInst]
  simp [CombHier.generatedChildRefs, ppGen, rowGen, outGen, rowBody,
    noisyMul.pdesign, ha, Except.bind, Except.pure, pure, Functor.map, Except.map]
  rfl

def noisyTopGeneratedPairs : List (CombHier.GeneratedChildRef × Design2) :=
  [({ loops := ppLoops, inst := andInst, child := andDef }, andDesign),
   ({ loops := rowInnerLoops, inst := xorInst, child := xorDef }, xorDesign),
   ({ loops := rowInnerLoops, inst := xorSInst, child := xorDef }, xorDesign),
   ({ loops := rowInnerLoops, inst := majInst, child := majDef }, majDesign)]

def noisyTopGeneratedPairSegment
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    CombHier.GeneratedChildRef × Design2 → List Decl × List Process2
  | (r, _) =>
      if r.inst.name == andInst.name then
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") andInst andDesign
      else if r.inst.name == xorInst.name then
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign
      else if r.inst.name == xorSInst.name then
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign
      else
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign

theorem noisy_top_generated_segments
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    noisyTopGeneratedPairs.mapM
      (fun r => r.1.segmentAt r.2
        ((env.bindVal "i" i).bindVal "j" j) elems) =
      .ok (noisyTopGeneratedPairs.map
        (noisyTopGeneratedPairSegment env elems i j)) := by
  apply (CombHier.generatedChildRefPairs_segmentAt_mapM_ok
    (rs := noisyTopGeneratedPairs)
    (env := fun _ => (env.bindVal "i" i).bindVal "j" j)
    (elems := elems)
    (seg := noisyTopGeneratedPairSegment env elems i j))
  intro r hr
  have hat : andInst.name ≠ xorInst.name := by decide
  have hta : xorInst.name ≠ andInst.name := by decide
  have has : andInst.name ≠ xorSInst.name := by decide
  have hsa : xorSInst.name ≠ andInst.name := by decide
  have hst : xorSInst.name ≠ xorInst.name := by decide
  have hmt : majInst.name ≠ xorInst.name := by decide
  have hms : majInst.name ≠ xorSInst.name := by decide
  have hma : majInst.name ≠ andInst.name := by decide
  simp only [noisyTopGeneratedPairs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · simpa [noisyTopGeneratedPairSegment] using
      (CombHier.GeneratedChildRef.segmentAt_ok (andInst_prefix env i j))
  rcases hr with rfl | hr
  · simpa [noisyTopGeneratedPairSegment, hta, hat, hmt] using
      (CombHier.GeneratedChildRef.segmentAt_ok (xorInst_prefix env i j))
  rcases hr with rfl | hr
  · simpa [noisyTopGeneratedPairSegment, hsa, has, hst, hms] using
      (CombHier.GeneratedChildRef.segmentAt_ok (xorS_prefix env i j))
  rcases hr with rfl | hr
  · simpa [noisyTopGeneratedPairSegment, hma, hmt, hms] using
      (CombHier.GeneratedChildRef.segmentAt_ok (majInst_prefix env i j))
  simp at hr

theorem noisy_top_generated_pairs_fst :
    noisyTopGeneratedPairs.map Prod.fst = noisyTopGeneratedRefs := by
  rfl

theorem noisy_top_generated_segments_flatten_map
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    GeneratedChildSegment.flatten
        (noisyTopGeneratedPairs.map fun r =>
          let p := noisyTopGeneratedPairSegment env elems i j r
          { decls := p.1, processes := p.2 }) =
      (noisyTopGeneratedPairs.flatMap fun r =>
        (noisyTopGeneratedPairSegment env elems i j r).1,
       noisyTopGeneratedPairs.flatMap fun r =>
        (noisyTopGeneratedPairSegment env elems i j r).2) := by
  simpa [List.map_map, List.flatMap_map, Function.comp_def] using
    (GeneratedChildSegment.flatten_map_pair
      (noisyTopGeneratedPairs.map fun r => noisyTopGeneratedPairSegment env elems i j r))

theorem noisy_top_child_instance_names_nodup :
    (noisyTopGeneratedRefs.map (fun r => r.inst.name)).Nodup := by
  decide

theorem noisy_top_generated_segments_explicit
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    noisyTopGeneratedPairs.mapM
      (fun r => r.1.segmentAt r.2
        ((env.bindVal "i" i).bindVal "j" j) elems) =
      .ok [
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") andInst andDesign,
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign,
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign,
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign] := by
  rw [noisy_top_generated_segments]
  rfl

def noisyTopGeneratedNodes : List CombHier.GeneratedNode :=
  noisyTopGeneratedRefs.map CombHier.GeneratedNode.child

def noisyTopNodeChild (r : CombHier.GeneratedChildRef) : Except String Design2 :=
  if r.inst.name == andInst.name then
    .ok andDesign
  else if r.inst.name == xorInst.name then
    .ok xorDesign
  else if r.inst.name == xorSInst.name then
    .ok xorDesign
  else
    .ok majDesign

def noisyTopNodeDesign (r : CombHier.GeneratedChildRef) : Design2 :=
  if r.inst.name == andInst.name then
    andDesign
  else if r.inst.name == xorInst.name then
    xorDesign
  else if r.inst.name == xorSInst.name then
    xorDesign
  else
    majDesign

def noisyTopNodeSegment
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    CombHier.GeneratedNode → List Decl × List Process2
  | .child r =>
      noisyTopGeneratedPairSegment env elems i j (r, noisyTopNodeDesign r)
  | .process _ p => ([], [instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems p])

theorem noisy_top_generated_node_segments
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    noisyTopGeneratedNodes.mapM
      (fun n => n.segmentAt noisyTopNodeChild
        ((env.bindVal "i" i).bindVal "j" j) elems) =
      .ok (noisyTopGeneratedNodes.map (noisyTopNodeSegment env elems i j)) := by
  apply (CombHier.generatedNodes_segmentAt_mapM_ok
    (ns := noisyTopGeneratedNodes)
    (child := noisyTopNodeChild)
    (env := (env.bindVal "i" i).bindVal "j" j)
    (elems := elems)
    (seg := noisyTopNodeSegment env elems i j))
  intro n hn
  simp only [noisyTopGeneratedNodes, List.mem_map] at hn
  obtain ⟨r, hr, rfl⟩ := hn
  simp only [noisyTopGeneratedRefs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [noisyTopNodeChild, andInst]
    · simpa [noisyTopNodeSegment, noisyTopGeneratedPairSegment, noisyTopNodeChild]
        using andInst_prefix env i j
  rcases hr with rfl | hr
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [noisyTopNodeChild, xorInst, andInst]
    · simpa [noisyTopNodeSegment, noisyTopGeneratedPairSegment, noisyTopNodeChild]
        using xorInst_prefix env i j
  rcases hr with rfl | hr
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [noisyTopNodeChild, xorSInst, andInst, xorInst]
    · simpa [noisyTopNodeSegment, noisyTopGeneratedPairSegment, noisyTopNodeChild]
        using xorS_prefix env i j
  rcases hr with rfl | hr
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [noisyTopNodeChild, majInst, andInst, xorInst, xorSInst]
    · simpa [noisyTopNodeSegment, noisyTopGeneratedPairSegment, noisyTopNodeChild]
        using majInst_prefix env i j
  simp at hr

theorem noisy_top_generated_node_flatten
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    Except.map CombHier.GeneratedNode.flattenSegments
      (noisyTopGeneratedNodes.mapM
        (fun n => n.segmentAt noisyTopNodeChild
          ((env.bindVal "i" i).bindVal "j" j) elems)) =
      .ok (CombHier.GeneratedNode.flattenSegments
        (noisyTopGeneratedNodes.map (noisyTopNodeSegment env elems i j))) := by
  rw [noisy_top_generated_node_segments]
  rfl

theorem noisy_generated_node_process_segment
    (env : IEnv) (elems : List (String × Nat)) (i : Int) :
    CombHier.GeneratedNode.segmentAt noisyTopNodeChild
        (env.bindVal "i" i) elems (.process [outLoop] outProc) =
      .ok ([], [instProcess2 (env.bindVal "i" i) elems outProc]) := by
  rw [CombHier.GeneratedNode.segmentAt_process]

def noisyTopSourceNodeSegment
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    CombHier.GeneratedNode → List Decl × List Process2 :=
  noisyTopNodeSegment env elems i j

def noisyTopSourcePaths (i j : Int) :
    List (CombHier.GeneratedNode × List Int) :=
  [(.child { loops := ppSourceLoops, inst := andInst, child := andDef }, [i, j]),
   (.process [rowSourceLoop] rowLeft, [i]),
   (.child { loops := rowSourceLoops, inst := xorInst, child := xorDef }, [i, j]),
   (.child { loops := rowSourceLoops, inst := xorSInst, child := xorDef }, [i, j]),
   (.child { loops := rowSourceLoops, inst := majInst, child := majDef }, [i, j]),
   (.process [rowSourceLoop] rowRight, [i]),
   (.process [outSourceLoop] outProc, [i])]

theorem noisy_top_source_paths_shape (i j : Int) :
    noisyTopSourcePaths i j = noisyTopSourceNodes.map (fun n =>
      (n, match n with
      | .process loops _ => if loops.length = 1 then [i] else [i, j]
      | .child ref => if ref.loops.length = 1 then [i] else [i, j])) := by
  rfl

theorem noisy_row_targets_bind_extra
    (env : IEnv) (i j : Int) :
    arrayElemTarget (env.bindVal "i" i) "c"
        [.genvarRef "i", .int 0] =
      arrayElemTarget ((env.bindVal "i" i).bindVal "j" j) "c"
        [.genvarRef "i", .int 0] ∧
    arrayElemTarget (env.bindVal "i" i) "s"
        [.genvarRef "i", .paramRef "N" none] =
      arrayElemTarget ((env.bindVal "i" i).bindVal "j" j) "s"
        [.genvarRef "i", .paramRef "N" none] := by
  constructor
  · apply arrayElemTarget_of_evalInt_eq
    · rfl
    · intro e he
      simp only [List.mem_cons, List.mem_singleton] at he
      rcases he with rfl | rfl | h
      · simp [evalInt, IEnv.bindVal, List.lookup]
      · rfl
      · simp at h
  · apply arrayElemTarget_of_evalInt_eq
    · rfl
    · intro e he
      simp only [List.mem_cons, List.mem_singleton] at he
      rcases he with rfl | rfl | h
      · simp [evalInt, IEnv.bindVal, List.lookup]
      · rfl
      · simp at h

theorem noisy_row_lhs_bind_extra
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    instLhs2 (env.bindVal "i" i) elems
        (.arrayElem "c" [.genvarRef "i", .int 0]) =
      instLhs2 ((env.bindVal "i" i).bindVal "j" j) elems
        (.arrayElem "c" [.genvarRef "i", .int 0]) ∧
    instLhs2 (env.bindVal "i" i) elems
        (.arrayElem "s" [.genvarRef "i", .paramRef "N" none]) =
      instLhs2 ((env.bindVal "i" i).bindVal "j" j) elems
        (.arrayElem "s" [.genvarRef "i", .paramRef "N" none]) := by
  simpa [instLhs2, instLhsLeaf2] using noisy_row_targets_bind_extra env i j

theorem noisy_row_left_process_bind_extra
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    instProcess2 (env.bindVal "i" i) elems rowLeft =
      instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems rowLeft := by
  simp only [instProcess2, rowLeft]
  rw [(noisy_row_lhs_bind_extra env elems i j).1]
  generalize h : instLhs2 ((env.bindVal "i" i).bindVal "j" j) elems
      (.arrayElem "c" [.genvarRef "i", .int 0]) = r
  cases r with
  | error e => simp [h]
  | ok p =>
      simp [h]
      exact fitExpr2_lit_env_irrel (env.bindVal "i" i)
        ((env.bindVal "i" i).bindVal "j" j) elems (some p.2) ⟨#[Logic.l0]⟩

theorem noisy_row_right_process_bind_extra
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    instProcess2 (env.bindVal "i" i) elems rowRight =
      instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems rowRight := by
  simp only [instProcess2, rowRight]
  rw [(noisy_row_lhs_bind_extra env elems i j).2]
  generalize h : instLhs2 ((env.bindVal "i" i).bindVal "j" j) elems
      (.arrayElem "s" [.genvarRef "i", .paramRef "N" none]) = r
  cases r with
  | error e => simp [h]
  | ok p =>
      simp [h]
      exact fitExpr2_arrayElem_of_evalInt_eq
        (env.bindVal "i" i) ((env.bindVal "i" i).bindVal "j" j)
        elems (some p.2) "c" [.genvarRef "i", .paramRef "N" none]
        (by rfl) (by
          intro e he
          simp only [List.mem_cons, List.mem_singleton] at he
          rcases he with rfl | rfl | h
          · simp [evalInt, IEnv.bindVal, List.lookup]
          · rfl
          · simp at h)

theorem noisy_out_process_bind_extra
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    instProcess2 (env.bindVal "i" i) elems outProc =
      instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems outProc := by
  simp only [instProcess2, outProc]
  rw [bitSelTarget_genvar_irrel (env.bindVal "i" i) ((env.bindVal "i" i).bindVal "j" j) elems "p" "i" i (by simp) (by simp [IEnv.bindVal, List.lookup])]
  generalize h : instLhs2 ((env.bindVal "i" i).bindVal "j" j) elems
      (.bitSel "p" (.genvarRef "i")) = r
  cases r with
  | error e => simp [h]
  | ok p =>
      simp [h]
      exact fitExpr2_arrayElem_of_evalInt_eq
        (env.bindVal "i" i) ((env.bindVal "i" i).bindVal "j" j)
        elems (some p.2) "s" [.genvarRef "i", .int 0]
        (by rfl) (by
          intro e he
          simp only [List.mem_cons, List.mem_singleton] at he
          rcases he with rfl | rfl | h
          · simp [evalInt, IEnv.bindVal, List.lookup]
          · rfl
          · simp at h)

def noisyTopSourcePathSegment
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    CombHier.GeneratedNode × List Int → List Decl × List Process2
  | (node, _) => noisyTopSourceNodeSegment env elems i j node

theorem noisy_generated_source_paths_segments
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    (noisyTopSourcePaths i j).mapM
        (fun p => p.1.segmentAtPath noisyTopNodeChild env p.2 elems) =
      .ok ((noisyTopSourcePaths i j).map
        (noisyTopSourcePathSegment env elems i j)) := by
  apply CombHier.generatedPaths_segmentAtPath_mapM_ok
  intro p hp
  simp only [noisyTopSourcePaths, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply CombHier.GeneratedNode.segmentAtPath_of_bind
    · rfl
    · apply CombHier.GeneratedNode.segmentAt_child
      · simp [noisyTopNodeChild, andInst]
      · simpa [noisyTopNodeSegment, noisyTopGeneratedPairSegment] using
          andInst_prefix env i j
  · apply CombHier.GeneratedNode.segmentAtPath_of_bind
    · rfl
    · simp only [CombHier.GeneratedNode.segmentAt_process, noisyTopSourcePathSegment, noisyTopSourceNodeSegment, noisyTopNodeSegment, rowSourceLoop]
      exact congrArg (fun p => Except.ok ([], [p])) (noisy_row_left_process_bind_extra env elems i j)
  · apply CombHier.GeneratedNode.segmentAtPath_of_bind
    · rfl
    · apply CombHier.GeneratedNode.segmentAt_child
      · simp [noisyTopNodeChild, xorInst, andInst]
      · simpa [rowSourceLoop, bitSourceLoop, noisyTopNodeSegment, noisyTopGeneratedPairSegment] using
          xorInst_prefix env i j
  · apply CombHier.GeneratedNode.segmentAtPath_of_bind
    · rfl
    · apply CombHier.GeneratedNode.segmentAt_child
      · simp [noisyTopNodeChild, xorSInst, andInst, xorInst]
      · simpa [rowSourceLoop, bitSourceLoop, noisyTopNodeSegment, noisyTopGeneratedPairSegment] using
          xorS_prefix env i j
  · apply CombHier.GeneratedNode.segmentAtPath_of_bind
    · rfl
    · apply CombHier.GeneratedNode.segmentAt_child
      · simp [noisyTopNodeChild, majInst, andInst, xorInst, xorSInst]
      · simpa [rowSourceLoop, bitSourceLoop, noisyTopNodeSegment, noisyTopGeneratedPairSegment] using
          majInst_prefix env i j
  · apply CombHier.GeneratedNode.segmentAtPath_of_bind
    · rfl
    · simp only [CombHier.GeneratedNode.segmentAt_process, noisyTopSourcePathSegment, noisyTopSourceNodeSegment, noisyTopNodeSegment, rowSourceLoop]
      exact congrArg (fun p => Except.ok ([], [p])) (noisy_row_right_process_bind_extra env elems i j)
  · apply CombHier.GeneratedNode.segmentAtPath_of_bind
    · rfl
    · simp only [CombHier.GeneratedNode.segmentAt_process, noisyTopSourcePathSegment, noisyTopSourceNodeSegment, noisyTopNodeSegment, outSourceLoop]
      exact congrArg (fun p => Except.ok ([], [p])) (noisy_out_process_bind_extra env elems i j)

theorem noisy_generated_source_paths_assemble
    (env : IEnv) (elems : List (String × Nat)) (i j : Int)
    (decls idecls : List Decl) :
    CombHier.assembleGeneratedPathsAt noisyMul.pdesign env decls idecls elems
        (noisyTopSourcePaths i j) noisyTopNodeChild =
      .ok (noisyMul.pdesign.assembleH env decls
        (idecls ++
          (CombHier.GeneratedNode.flattenSegments
            ((noisyTopSourcePaths i j).map
              (noisyTopSourcePathSegment env elems i j))).1)
        elems
        (CombHier.GeneratedNode.flattenSegments
          ((noisyTopSourcePaths i j).map
            (noisyTopSourcePathSegment env elems i j))).2) := by
  apply CombHier.assembleGeneratedPathsAt_of_ok
  exact noisy_generated_source_paths_segments env elems i j

theorem noisy_generated_source_segments
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    noisyTopSourceNodes.mapM
      (fun n => n.segmentAt noisyTopNodeChild
        ((env.bindVal "i" i).bindVal "j" j) elems) =
      .ok (noisyTopSourceNodes.map (noisyTopSourceNodeSegment env elems i j)) := by
  apply (CombHier.generatedNodes_segmentAt_mapM_ok
    (ns := noisyTopSourceNodes)
    (child := noisyTopNodeChild)
    (env := (env.bindVal "i" i).bindVal "j" j)
    (elems := elems)
    (seg := noisyTopSourceNodeSegment env elems i j))
  intro n hn
  simp only [noisyTopSourceNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [noisyTopNodeChild, andInst]
    · simpa [noisyTopSourceNodeSegment, noisyTopNodeSegment,
        noisyTopGeneratedPairSegment, noisyTopNodeChild] using andInst_prefix env i j
  · rw [CombHier.GeneratedNode.segmentAt_process]
    rfl
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [noisyTopNodeChild, xorInst, andInst]
    · simpa [noisyTopSourceNodeSegment, noisyTopNodeSegment,
        noisyTopGeneratedPairSegment, noisyTopNodeChild] using xorInst_prefix env i j
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [noisyTopNodeChild, xorSInst, andInst, xorInst]
    · simpa [noisyTopSourceNodeSegment, noisyTopNodeSegment,
        noisyTopGeneratedPairSegment, noisyTopNodeChild] using xorS_prefix env i j
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [noisyTopNodeChild, majInst, andInst, xorInst, xorSInst]
    · simpa [noisyTopSourceNodeSegment, noisyTopNodeSegment,
        noisyTopGeneratedPairSegment, noisyTopNodeChild] using majInst_prefix env i j
  · rw [CombHier.GeneratedNode.segmentAt_process]
    rfl
  · rw [CombHier.GeneratedNode.segmentAt_process]
    rfl

theorem noisy_generated_source_flatten
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    Except.map CombHier.GeneratedNode.flattenSegments
      (noisyTopSourceNodes.mapM
        (fun n => n.segmentAt noisyTopNodeChild
          ((env.bindVal "i" i).bindVal "j" j) elems)) =
      .ok (CombHier.GeneratedNode.flattenSegments
        (noisyTopSourceNodes.map (noisyTopSourceNodeSegment env elems i j))) := by
  rw [noisy_generated_source_segments]
  rfl

/-! The source-order receipt now enters the ordinary `Design2` assembly path.
This is deliberately one valuation of the retained symbolic nodes: the
generate bounds remain in `noisyTopSourceNodes`, while the assembly theorem
only consumes the valuation-dependent child environments and prefixes. -/
theorem noisy_generated_source_assemble
    (env : IEnv) (elems : List (String × Nat)) (i j : Int)
    (decls idecls : List Decl) :
    CombHier.assembleGeneratedAt noisyMul.pdesign
        ((env.bindVal "i" i).bindVal "j" j) decls idecls elems
        noisyTopSourceNodes noisyTopNodeChild =
      .ok (noisyMul.pdesign.assembleH
        ((env.bindVal "i" i).bindVal "j" j) decls
        (idecls ++
          (CombHier.GeneratedNode.flattenSegments
            (noisyTopSourceNodes.map (noisyTopSourceNodeSegment env elems i j))).1)
        elems
        (CombHier.GeneratedNode.flattenSegments
          (noisyTopSourceNodes.map (noisyTopSourceNodeSegment env elems i j))).2) := by
  apply CombHier.assembleGeneratedAt_of_ok
  exact noisy_generated_source_segments env elems i j

theorem noisy_generated_source_realization
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    CombHier.GeneratedFamilyRealization env elems (noisyTopSourcePaths i j)
      noisyTopNodeChild
      (CombHier.GeneratedNode.flattenSegments
        ((noisyTopSourcePaths i j).map
          (noisyTopSourcePathSegment env elems i j))) := by
  refine ⟨(noisyTopSourcePaths i j).map
      (noisyTopSourcePathSegment env elems i j),
    noisy_generated_source_paths_segments env elems i j, rfl⟩



def noisyPpPaths (N i : Int) : List (CombHier.GeneratedNode × List Int) :=
  (intRange 0 N.toNat).map fun j =>
    (.child { loops := ppSourceLoops, inst := andInst, child := andDef }, [i, j])

def noisyRowChildPaths (N i : Int) : List (CombHier.GeneratedNode × List Int) :=
  (intRange 0 N.toNat).flatMap fun j =>
    [ (.child { loops := rowSourceLoops, inst := xorInst, child := xorDef }, [i, j]),
      (.child { loops := rowSourceLoops, inst := xorSInst, child := xorDef }, [i, j]),
      (.child { loops := rowSourceLoops, inst := majInst, child := majDef }, [i, j]) ]

def noisyRowPaths (N i : Int) : List (CombHier.GeneratedNode × List Int) :=
  (.process [rowSourceLoop] rowLeft, [i]) ::
    noisyRowChildPaths N i ++ [(.process [rowSourceLoop] rowRight, [i])]

def noisyOutPaths (N : Int) : List (CombHier.GeneratedNode × List Int) :=
  (intRange 0 N.toNat).map fun i => (.process [outSourceLoop] outProc, [i])

def noisyFullFamilyPaths (N : Int) : List (CombHier.GeneratedNode × List Int) :=
  (intRange 0 N.toNat).flatMap (noisyPpPaths N) ++
    (intRange 1 (N - 1).toNat).flatMap (noisyRowPaths N) ++ noisyOutPaths N

def noisyFullFamilySegment
    (env : IEnv) (elems : List (String × Nat)) :
    CombHier.GeneratedNode × List Int → List Decl × List Process2
  | (.child r, [i, j]) => noisyTopNodeSegment env elems i j (.child r)
  | (.process _ p, [i]) => ([], [instProcess2 (env.bindVal "i" i) elems p])
  | _ => ([], [])


theorem noisyPpPath_segment_ok
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    ((.child { loops := ppSourceLoops, inst := andInst, child := andDef }, [i, j]) :
      CombHier.GeneratedNode × List Int).1.segmentAtPath noisyTopNodeChild env [i, j] elems =
      .ok (noisyFullFamilySegment env elems
        (.child { loops := ppSourceLoops, inst := andInst, child := andDef }, [i, j])) := by
  apply CombHier.GeneratedNode.segmentAtPath_of_bind
  · rfl
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [noisyTopNodeChild, andInst]
    · simpa [noisyFullFamilySegment, noisyTopNodeSegment,
        noisyTopGeneratedPairSegment, noisyTopNodeChild] using
        andInst_prefix env i j

theorem noisyRowPath_segment_ok
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    ((.child { loops := rowSourceLoops, inst := xorInst, child := xorDef }, [i, j]) :
      CombHier.GeneratedNode × List Int).1.segmentAtPath noisyTopNodeChild env [i, j] elems =
      .ok (noisyFullFamilySegment env elems
        (.child { loops := rowSourceLoops, inst := xorInst, child := xorDef }, [i, j])) := by
  apply CombHier.GeneratedNode.segmentAtPath_of_bind
  · rfl
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [rowSourceLoop, bitSourceLoop, noisyTopNodeChild, xorInst, andInst]
    · simpa [rowSourceLoop, bitSourceLoop, noisyFullFamilySegment,
        noisyTopNodeSegment, noisyTopGeneratedPairSegment] using
        xorInst_prefix env i j

theorem noisyRowPath_segment_ok_xorS
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    ((.child { loops := rowSourceLoops, inst := xorSInst, child := xorDef }, [i, j]) :
      CombHier.GeneratedNode × List Int).1.segmentAtPath noisyTopNodeChild env [i, j] elems =
      .ok (noisyFullFamilySegment env elems
        (.child { loops := rowSourceLoops, inst := xorSInst, child := xorDef }, [i, j])) := by
  apply CombHier.GeneratedNode.segmentAtPath_of_bind
  · rfl
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [rowSourceLoop, bitSourceLoop, noisyTopNodeChild, xorSInst, andInst, xorInst]
    · simpa [rowSourceLoop, bitSourceLoop, noisyFullFamilySegment,
        noisyTopNodeSegment, noisyTopGeneratedPairSegment] using
        xorS_prefix env i j

theorem noisyRowPath_segment_ok_maj
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) :
    ((.child { loops := rowSourceLoops, inst := majInst, child := majDef }, [i, j]) :
      CombHier.GeneratedNode × List Int).1.segmentAtPath noisyTopNodeChild env [i, j] elems =
      .ok (noisyFullFamilySegment env elems
        (.child { loops := rowSourceLoops, inst := majInst, child := majDef }, [i, j])) := by
  apply CombHier.GeneratedNode.segmentAtPath_of_bind
  · rfl
  · apply CombHier.GeneratedNode.segmentAt_child
    · simp [rowSourceLoop, bitSourceLoop, noisyTopNodeChild, majInst, andInst, xorInst, xorSInst]
    · simpa [rowSourceLoop, bitSourceLoop, noisyFullFamilySegment,
        noisyTopNodeSegment, noisyTopGeneratedPairSegment] using
        majInst_prefix env i j

theorem noisyRowPath_segment_ok_left
    (env : IEnv) (elems : List (String × Nat)) (i : Int) :
    ((.process [rowSourceLoop] rowLeft, [i]) :
      CombHier.GeneratedNode × List Int).1.segmentAtPath noisyTopNodeChild env [i] elems =
      .ok (noisyFullFamilySegment env elems
        (.process [rowSourceLoop] rowLeft, [i])) := by
  simp [CombHier.GeneratedNode.segmentAtPath, CombHier.GeneratedNode.loops, CombHier.GeneratedLoop.bindPath, noisyFullFamilySegment, rowSourceLoop]
  rfl

theorem noisyRowPath_segment_ok_right
    (env : IEnv) (elems : List (String × Nat)) (i : Int) :
    ((.process [rowSourceLoop] rowRight, [i]) :
      CombHier.GeneratedNode × List Int).1.segmentAtPath noisyTopNodeChild env [i] elems =
      .ok (noisyFullFamilySegment env elems
        (.process [rowSourceLoop] rowRight, [i])) := by
  simp [CombHier.GeneratedNode.segmentAtPath, CombHier.GeneratedNode.loops, CombHier.GeneratedLoop.bindPath, noisyFullFamilySegment, rowSourceLoop]
  rfl

theorem noisyOutPath_segment_ok
    (env : IEnv) (elems : List (String × Nat)) (i : Int) :
    ((.process [outSourceLoop] outProc, [i]) :
      CombHier.GeneratedNode × List Int).1.segmentAtPath noisyTopNodeChild env [i] elems =
      .ok (noisyFullFamilySegment env elems
        (.process [outSourceLoop] outProc, [i])) := by
  simp [CombHier.GeneratedNode.segmentAtPath, CombHier.GeneratedNode.loops, CombHier.GeneratedLoop.bindPath, noisyFullFamilySegment, outSourceLoop]
  rfl

theorem mapM_flatMap_ok {α β γ : Type} {f : β → Except String γ}
    {g : α → List β} {s : β → γ} {xs : List α}
    (h : ∀ a, (g a).mapM f = .ok ((g a).map s)) :
    (xs.flatMap g).mapM f = .ok ((xs.flatMap g).map s) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [List.flatMap_cons]
      rw [CombHier.mapM_append_ok_of_ok (h a) ih]
      simp only [List.map_append]

theorem noisyPpPaths_segments
    (env : IEnv) (elems : List (String × Nat)) (N i : Int) :
    (noisyPpPaths N i).mapM
        (fun p => p.1.segmentAtPath noisyTopNodeChild env p.2 elems) =
      .ok ((noisyPpPaths N i).map (noisyFullFamilySegment env elems)) := by
  apply CombHier.generatedPaths_segmentAtPath_mapM_ok
  intro p hp
  simp [noisyPpPaths] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  exact noisyPpPath_segment_ok env elems i j

theorem noisyRowChildPaths_segments
    (env : IEnv) (elems : List (String × Nat)) (N i : Int) :
    (noisyRowChildPaths N i).mapM
        (fun p => p.1.segmentAtPath noisyTopNodeChild env p.2 elems) =
      .ok ((noisyRowChildPaths N i).map (noisyFullFamilySegment env elems)) := by
  apply CombHier.generatedPaths_segmentAtPath_mapM_ok
  intro p hp
  simp [noisyRowChildPaths] at hp
  rcases hp with ⟨j, hj, h⟩
  rcases h with rfl | rfl | rfl
  · exact noisyRowPath_segment_ok env elems i j
  · exact noisyRowPath_segment_ok_xorS env elems i j
  · exact noisyRowPath_segment_ok_maj env elems i j

theorem noisyRowPaths_segments
    (env : IEnv) (elems : List (String × Nat)) (N i : Int) :
    (noisyRowPaths N i).mapM
        (fun p => p.1.segmentAtPath noisyTopNodeChild env p.2 elems) =
      .ok ((noisyRowPaths N i).map (noisyFullFamilySegment env elems)) := by
  unfold noisyRowPaths
  have hleft :
      ([((.process [rowSourceLoop] rowLeft, [i]) :
          CombHier.GeneratedNode × List Int)]).mapM
          (fun p => p.1.segmentAtPath noisyTopNodeChild env p.2 elems) =
        .ok ([((.process [rowSourceLoop] rowLeft, [i]) :
          CombHier.GeneratedNode × List Int)].map (noisyFullFamilySegment env elems)) := by
    rw [List.mapM_cons, List.mapM_nil, noisyRowPath_segment_ok_left]
    rfl
  have hright :
      ([((.process [rowSourceLoop] rowRight, [i]) :
          CombHier.GeneratedNode × List Int)]).mapM
          (fun p => p.1.segmentAtPath noisyTopNodeChild env p.2 elems) =
        .ok ([((.process [rowSourceLoop] rowRight, [i]) :
          CombHier.GeneratedNode × List Int)].map (noisyFullFamilySegment env elems)) := by
    rw [List.mapM_cons, List.mapM_nil, noisyRowPath_segment_ok_right]
    rfl
  have htail := CombHier.mapM_append_ok_of_ok
    (noisyRowChildPaths_segments env elems N i) hright
  simpa [List.map_append] using
    (CombHier.mapM_append_ok_of_ok hleft htail)

theorem noisyOutPaths_segments
    (env : IEnv) (elems : List (String × Nat)) (N : Int) :
    (noisyOutPaths N).mapM
        (fun p => p.1.segmentAtPath noisyTopNodeChild env p.2 elems) =
      .ok ((noisyOutPaths N).map (noisyFullFamilySegment env elems)) := by
  apply CombHier.generatedPaths_segmentAtPath_mapM_ok
  intro p hp
  simp [noisyOutPaths] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact noisyOutPath_segment_ok env elems i

theorem noisyFullFamily_segments
    (env : IEnv) (elems : List (String × Nat)) (N : Int) :
    (noisyFullFamilyPaths N).mapM
        (fun p => p.1.segmentAtPath noisyTopNodeChild env p.2 elems) =
      .ok ((noisyFullFamilyPaths N).map (noisyFullFamilySegment env elems)) := by
  unfold noisyFullFamilyPaths
  have hpp := mapM_flatMap_ok (xs := intRange 0 N.toNat)
      (fun i => noisyPpPaths_segments env elems N i)
  have hrow := mapM_flatMap_ok (xs := intRange 1 (N - 1).toNat)
      (fun i => noisyRowPaths_segments env elems N i)
  have hout := noisyOutPaths_segments env elems N
  simpa only [List.map_append, List.append_assoc] using
    (CombHier.mapM_append_ok_of_ok hpp
      (CombHier.mapM_append_ok_of_ok hrow hout))

theorem noisyRowPaths_flatten
    (env : IEnv) (elems : List (String × Nat)) (N i : Int) :
    CombHier.GeneratedNode.flattenSegments
        ((noisyRowPaths N i).map (noisyFullFamilySegment env elems)) =
      ((noisyRowChildPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).1),
       [instProcess2 (env.bindVal "i" i) elems rowLeft] ++
         (noisyRowChildPaths N i).flatMap
           (fun p => (noisyFullFamilySegment env elems p).2) ++
         [instProcess2 (env.bindVal "i" i) elems rowRight]) := by
  rw [CombHier.GeneratedNode.flattenSegments_map]
  simp [noisyRowPaths, noisyFullFamilySegment, List.flatMap_cons,
    List.flatMap_append, List.flatMap_map, List.append_assoc]

theorem noisyPpPaths_flatten
    (env : IEnv) (elems : List (String × Nat)) (N i : Int) :
    CombHier.GeneratedNode.flattenSegments
        ((noisyPpPaths N i).map (noisyFullFamilySegment env elems)) =
      ((noisyPpPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).1),
       (noisyPpPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).2)) := by
  rw [CombHier.GeneratedNode.flattenSegments_map]
  simp [noisyPpPaths, noisyFullFamilySegment, List.flatMap_map]

theorem noisyOutPaths_flatten
    (env : IEnv) (elems : List (String × Nat)) (N : Int) :
    CombHier.GeneratedNode.flattenSegments
        ((noisyOutPaths N).map (noisyFullFamilySegment env elems)) =
      ((noisyOutPaths N).flatMap
          (fun p => (noisyFullFamilySegment env elems p).1),
       (noisyOutPaths N).flatMap
          (fun p => (noisyFullFamilySegment env elems p).2)) := by
  rw [CombHier.GeneratedNode.flattenSegments_map]
  simp [noisyOutPaths, noisyFullFamilySegment, List.flatMap_map]

theorem noisyRowChildPaths_flatten
    (env : IEnv) (elems : List (String × Nat)) (N i : Int) :
    CombHier.GeneratedNode.flattenSegments
        ((noisyRowChildPaths N i).map (noisyFullFamilySegment env elems)) =
      noisy_row_inner_segment env elems i N := by
  rw [CombHier.GeneratedNode.flattenSegments_map]
  unfold noisy_row_inner_segment
  simp only [GeneratedChildSegment.flatten, noisyRowChildPaths, noisyFullFamilySegment,
    List.flatMap_map, List.map_map]
  rw [List.flatMap_assoc, List.flatMap_assoc]
  simp [List.flatMap, List.append_assoc, noisyTopNodeSegment,
    noisyTopGeneratedPairSegment, noisyTopNodeDesign, noisyTopNodeChild,
    xorInst, xorSInst, majInst, andInst]


theorem noisy_top_expand_family_actual
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (clocks : List String)
    (hFuel : N.toNat < F) (hRowFuel : (N - 1).toNat < F)
    (hBound : ∀ i : Int, PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int, evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int, PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int, evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N) :
    expandListH (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
      env elems F noisyMul.pdesign.generates =
      .ok (CombHier.GeneratedNode.flattenSegments
        ((noisyFullFamilyPaths N).map (noisyFullFamilySegment env elems))) := by
  rw [noisy_top_expand_actual env elems F N clocks hFuel hRowFuel hBound hValue hInnerBound hInnerValue]
  have hseg : ∀ (i j : Int),
      noisyFullFamilySegment env elems
          (.child { loops := ppSourceLoops, inst := andInst, child := andDef }, [i, j]) =
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") andInst andDesign := by
    intro i j
    simp [noisyFullFamilySegment, noisyTopNodeSegment, noisyTopGeneratedPairSegment, andInst]
  have hpp :
      ((List.flatMap
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
            (intRange 0 N.toNat)) (intRange 0 N.toNat))) =
      CombHier.GeneratedNode.flattenSegments
        (List.flatMap (fun i =>
          (noisyPpPaths N i).map (noisyFullFamilySegment env elems))
          (intRange 0 N.toNat)) := by
    simp only [CombHier.GeneratedNode.flattenSegments_map]
    simp only [noisyPpPaths, List.map_map, Function.comp_apply]
    simp [hseg, Function.comp_def, List.flatMap_map, List.flatMap_assoc]
  have hchild_each : ∀ i : Int,
      CombHier.GeneratedNode.flattenSegments
          ((noisyRowChildPaths N i).map (noisyFullFamilySegment env elems)) =
        noisy_row_inner_segment env elems i N := by
    intro i
    exact noisyRowChildPaths_flatten env elems N i
  have hchild_fst : ∀ i : Int,
      (noisyRowChildPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).1) =
        (noisy_row_inner_segment env elems i N).1 := by
    intro i
    have h := congrArg Prod.fst (hchild_each i)
    simpa [CombHier.GeneratedNode.flattenSegments_map, List.flatMap_map] using h
  have hchild_snd : ∀ i : Int,
      (noisyRowChildPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).2) =
        (noisy_row_inner_segment env elems i N).2 := by
    intro i
    have h := congrArg Prod.snd (hchild_each i)
    simpa [CombHier.GeneratedNode.flattenSegments_map, List.flatMap_map] using h
  have hrow_each : ∀ i : Int,
      CombHier.GeneratedNode.flattenSegments
          ((noisyRowPaths N i).map (noisyFullFamilySegment env elems)) =
        ((noisy_row_inner_segment env elems i N).1,
         [instProcess2 (env.bindVal "i" i) elems rowLeft] ++
           (noisy_row_inner_segment env elems i N).2 ++
           [instProcess2 (env.bindVal "i" i) elems rowRight]) := by
    intro i
    rw [noisyRowPaths_flatten, hchild_fst i, hchild_snd i]
  have hrow :
      GeneratedChildSegment.flatten
        ((intRange 1 (N - 1).toNat).map fun i =>
          { decls := (noisy_row_inner_segment env elems i N).1,
            processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
              (noisy_row_inner_segment env elems i N).2 ++
              [instProcess2 (env.bindVal "i" i) elems rowRight] }) =
      CombHier.GeneratedNode.flattenSegments
        (List.flatMap (fun i => (noisyRowPaths N i).map (noisyFullFamilySegment env elems))
          (intRange 1 (N - 1).toNat)) := by
    rw [CombHier.GeneratedNode.flattenSegments_flatMap]
    have hmap :
        (intRange 1 (N - 1).toNat).map
            (fun i => CombHier.GeneratedNode.flattenSegments
              ((noisyRowPaths N i).map (noisyFullFamilySegment env elems))) =
          (intRange 1 (N - 1).toNat).map (fun i =>
            ((noisy_row_inner_segment env elems i N).1,
             [instProcess2 (env.bindVal "i" i) elems rowLeft] ++
               (noisy_row_inner_segment env elems i N).2 ++
               [instProcess2 (env.bindVal "i" i) elems rowRight])) := by
      apply List.map_congr_left
      intro i hi
      exact hrow_each i
    rw [hmap]
    simp [GeneratedChildSegment.flatten, CombHier.GeneratedNode.flattenSegments_map,
      List.flatMap_map, List.flatMap_assoc, List.append_assoc]
  have hout :
      ([], (intRange 0 N.toNat).flatMap fun i =>
        [instProcess2 (env.bindVal "i" i) elems outProc]) =
      CombHier.GeneratedNode.flattenSegments
        ((noisyOutPaths N).map (noisyFullFamilySegment env elems)) := by
    simp only [CombHier.GeneratedNode.flattenSegments_map]
    simp [noisyOutPaths, noisyFullFamilySegment, List.flatMap_map]
  have hpp_fst :
      (List.flatMap (fun i => List.flatMap (fun j =>
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") andInst andDesign).1)
        (intRange 0 N.toNat)) (intRange 0 N.toNat)) =
      (CombHier.GeneratedNode.flattenSegments
        (List.flatMap (fun i => (noisyPpPaths N i).map (noisyFullFamilySegment env elems))
          (intRange 0 N.toNat))).1 := by
    simpa using congrArg Prod.fst hpp
  have hpp_snd :
      (List.flatMap (fun i => List.flatMap (fun j =>
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") andInst andDesign).2)
        (intRange 0 N.toNat)) (intRange 0 N.toNat)) =
      (CombHier.GeneratedNode.flattenSegments
        (List.flatMap (fun i => (noisyPpPaths N i).map (noisyFullFamilySegment env elems))
          (intRange 0 N.toNat))).2 := by
    simpa using congrArg Prod.snd hpp
  have hrow_fst := congrArg Prod.fst hrow
  have hrow_snd := congrArg Prod.snd hrow
  have hout_snd := congrArg Prod.snd hout
  have hout_snd' :
      (intRange 0 N.toNat).flatMap (fun i =>
        [instProcess2 (env.bindVal "i" i) elems outProc]) =
      (CombHier.GeneratedNode.flattenSegments
        ((noisyOutPaths N).map (noisyFullFamilySegment env elems))).2 := by
    simpa using hout_snd
  have hout_full_decl :
      (CombHier.GeneratedNode.flattenSegments
        ((noisyOutPaths N).map (noisyFullFamilySegment env elems))).1 = [] := by
    rw [CombHier.GeneratedNode.flattenSegments_map]
    simp [noisyOutPaths, noisyFullFamilySegment, Function.comp_def,
      List.flatMap_map]
  unfold noisyFullFamilyPaths
  simp only [List.map_append, CombHier.GeneratedNode.flattenSegments_append,
    List.map_flatMap]
  rw [hpp_fst, hrow_fst, hpp_snd, hrow_snd, hout_snd', hout_full_decl]


theorem noisy_generated_family_expansion
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (clocks : List String)
    (hFuel : N.toNat < F)
    (hRowFuel : (N - 1).toNat < F)
    (hBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N) :
    CombHier.GeneratedFamilyExpansion
      (PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks)
      env elems F noisyMul.pdesign (noisyFullFamilyPaths N) noisyTopNodeChild
      (CombHier.GeneratedNode.flattenSegments
        ((noisyFullFamilyPaths N).map (noisyFullFamilySegment env elems))) := by
  refine ⟨noisy_top_expand_family_actual env elems F N clocks hFuel hRowFuel
    hBound hValue hInnerBound hInnerValue, ?_⟩
  refine ⟨(noisyFullFamilyPaths N).map (noisyFullFamilySegment env elems),
    noisyFullFamily_segments env elems N, rfl⟩

theorem noisy_and_child_depth (depth : Nat) (env : IEnv) (F : Nat) (clocks : List String) :
    PDesign.childRec (depth + 1) noisyMul.plib { int32 := true } F clocks env andInst =
      PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks env andInst := by
  rw [show noisyMul.plib = [andDef, xorDef, majDef] from by rfl]
  simp only [PDesign.childRec, childInstOf]
  have hg : PInst.given env andDef andInst = .ok [] := by
    simp [PInst.given, andDef, andInst]
    rfl
  have hp : andDef.atPoint [] = .ok (andDef, []) := rfl
  have hfind : [andDef, xorDef, majDef].find? (fun x => x.name == andInst.module) = some andDef := by
    rfl
  rw [hfind]
  simp only [hg, hp]
  have hrecD := PDesign.instantiateRec_flat depth [andDef, xorDef, majDef] { int32 := true }
    andDef [] F (by decide)
  have hrec0 := PDesign.instantiateRec_flat 0 [andDef, xorDef, majDef] { int32 := true }
    andDef [] F (by decide)
  rw [hrecD, hrec0]

theorem noisy_xor_child_depth (depth : Nat) (env : IEnv) (F : Nat) (clocks : List String) :
    PDesign.childRec (depth + 1) noisyMul.plib { int32 := true } F clocks env xorInst =
      PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks env xorInst := by
  rw [show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  simp only [PDesign.childRec, childInstOf]
  have hg : PInst.given env xorDef xorInst = .ok [] := by
    simp [PInst.given, xorDef]
    rfl
  have hp : xorDef.atPoint [] = .ok (xorDef, []) := rfl
  have hfind : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == xorInst.module) = some xorDef := by
    simp [andDef, xorInst, xorDef]
  rw [hfind]
  simp only [hg, hp]
  have hrecD := PDesign.instantiateRec_flat depth [andDef, xorDef, majDef] { int32 := true }
    xorDef [] F (by decide)
  have hrec0 := PDesign.instantiateRec_flat 0 [andDef, xorDef, majDef] { int32 := true }
    xorDef [] F (by decide)
  rw [hrecD, hrec0]

theorem noisy_xorS_child_depth (depth : Nat) (env : IEnv) (F : Nat) (clocks : List String) :
    PDesign.childRec (depth + 1) noisyMul.plib { int32 := true } F clocks env xorSInst =
      PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks env xorSInst := by
  rw [show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  simp only [PDesign.childRec, childInstOf]
  have hg : PInst.given env xorDef xorSInst = .ok [] := by
    simp [PInst.given, xorDef]
    rfl
  have hp : xorDef.atPoint [] = .ok (xorDef, []) := rfl
  have hfind : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == xorSInst.module) = some xorDef := by
    simp [andDef, xorSInst, xorDef]
  rw [hfind]
  simp only [hg, hp]
  have hrecD := PDesign.instantiateRec_flat depth [andDef, xorDef, majDef] { int32 := true }
    xorDef [] F (by decide)
  have hrec0 := PDesign.instantiateRec_flat 0 [andDef, xorDef, majDef] { int32 := true }
    xorDef [] F (by decide)
  rw [hrecD, hrec0]

theorem noisy_maj_child_depth (depth : Nat) (env : IEnv) (F : Nat) (clocks : List String) :
    PDesign.childRec (depth + 1) noisyMul.plib { int32 := true } F clocks env majInst =
      PDesign.childRec 1 noisyMul.plib { int32 := true } F clocks env majInst := by
  rw [show noisyMul.plib = andDef :: xorDef :: majDef :: [] from by rfl]
  simp only [PDesign.childRec, childInstOf]
  have hg : PInst.given env majDef majInst = .ok [] := by
    simp [PInst.given, majDef]
    rfl
  have hp : majDef.atPoint [] = .ok (majDef, []) := rfl
  have hfind : (andDef :: xorDef :: majDef :: []).find?
      (fun x => x.name == majInst.module) = some majDef := by
    simp [andDef, xorDef, majDef, majInst]
  rw [hfind]
  simp only [hg, hp]
  have hrecD := PDesign.instantiateRec_flat depth [andDef, xorDef, majDef] { int32 := true }
    majDef [] F (by decide)
  have hrec0 := PDesign.instantiateRec_flat 0 [andDef, xorDef, majDef] { int32 := true }
    majDef [] F (by decide)
  rw [hrecD, hrec0]

theorem noisy_top_expand_actual_depth3
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (clocks : List String)
    (hFuel : N.toNat < F)
    (hRowFuel : (N - 1).toNat < F)
    (hBound : ∀ i : Int,
      PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N) :
    expandListH
        (PDesign.childRec 3 noisyMul.plib { int32 := true } F clocks)
        env elems F noisyMul.pdesign.generates =
      .ok
        ((List.flatMap
          (fun i => List.flatMap
            (fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst andDesign).1)
            (intRange 0 N.toNat)) (intRange 0 N.toNat)) ++
          (GeneratedChildSegment.flatten
            ((intRange 1 (N - 1).toNat).map fun i =>
              { decls := (noisy_row_inner_segment env elems i N).1,
                processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
                  (noisy_row_inner_segment env elems i N).2 ++
                  [instProcess2 (env.bindVal "i" i) elems rowRight] })).1 ++
          [],
         (List.flatMap
          (fun i => List.flatMap
            (fun j =>
              (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
                ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.")
                andInst andDesign).2)
            (intRange 0 N.toNat)) (intRange 0 N.toNat)) ++
          (GeneratedChildSegment.flatten
            ((intRange 1 (N - 1).toNat).map fun i =>
              { decls := (noisy_row_inner_segment env elems i N).1,
                processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
                  (noisy_row_inner_segment env elems i N).2 ++
                  [instProcess2 (env.bindVal "i" i) elems rowRight] })).2 ++
          (intRange 0 N.toNat).flatMap fun i =>
            [instProcess2 (env.bindVal "i" i) elems outProc]) := by
  refine noisy_top_generated_expand
    (pp :=
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
        (intRange 0 N.toNat)) (intRange 0 N.toNat)))
    (row :=
      ((GeneratedChildSegment.flatten
        ((intRange 1 (N - 1).toNat).map fun i =>
          { decls := (noisy_row_inner_segment env elems i N).1,
            processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
              (noisy_row_inner_segment env elems i N).2 ++
              [instProcess2 (env.bindVal "i" i) elems rowRight] })).1,
       (GeneratedChildSegment.flatten
        ((intRange 1 (N - 1).toNat).map fun i =>
          { decls := (noisy_row_inner_segment env elems i N).1,
            processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
              (noisy_row_inner_segment env elems i N).2 ++
              [instProcess2 (env.bindVal "i" i) elems rowRight] })).2))
    (out := ([], (intRange 0 N.toNat).flatMap fun i =>
      [instProcess2 (env.bindVal "i" i) elems outProc]))
    ?_ ?_ ?_
  · have h := noisy_pp_expand_actual_segments
      (PDesign.childRec 3 noisyMul.plib { int32 := true } F clocks)
      env elems F N hFuel andDesign hBound hValue hInnerBound hInnerValue
      (by
        intro i j
        rw [noisy_and_child_depth 2, noisy_and_child])
    simpa [GeneratedChildSegment.flatten, List.flatMap_map] using h
  · apply noisy_row_expand_process_family
      (cb := PDesign.childRec 3 noisyMul.plib { int32 := true } F clocks)
      (env := env) (elems := elems) (F := F) (N := N) (hFuel := hRowFuel)
      (f := fun i => noisy_row_inner_segment env elems i N)
      hBound hValue (by intro i; simp) hInnerBound hInnerValue hFuel
      noisy_row_inner_instFree
    intro i hi hN
    apply noisy_bit_expand_segments
      (cb := PDesign.childRec 3 noisyMul.plib { int32 := true } F clocks)
      (env := env) (elems := elems) (F := F) (N := N) (i := i)
      (hFuel := hFuel)
      (f := fun j =>
        ((flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).1 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).1 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).1,
         (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t.") xorInst xorDesign).2 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s.") xorSInst xorDesign).2 ++
          (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
            ("g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c.") majInst majDesign).2))
      (by intro j; exact hInnerBound i j)
      (by intro j; exact hInnerValue i j)
    intro j hj0 hjN
    apply noisy_row_inner_expand
      (PDesign.childRec 3 noisyMul.plib { int32 := true } F clocks)
      env (elems := elems) (F := F) i j xorDesign xorDesign majDesign
    · rw [noisy_xor_child_depth 2, noisy_xor_child]
    · rw [noisy_xorS_child_depth 2, noisy_xorS_child]
    · rw [noisy_maj_child_depth 2, noisy_maj_child]
  · exact noisy_out_expand_list_actual
      (PDesign.childRec 3 noisyMul.plib { int32 := true } F clocks)
      env elems F N hFuel hBound hValue

theorem noisy_top_expand_family_actual_depth3
    (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (N : Int) (clocks : List String)
    (hFuel : N.toNat < F) (hRowFuel : (N - 1).toNat < F)
    (hBound : ∀ i : Int, PExpr.isInt (env.bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int, evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int, PExpr.isInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int, evalInt ((env.bindVal "i" i).bindVal "j" j) (.paramRef "N" none) = .ok N) :
    expandListH (PDesign.childRec 3 noisyMul.plib { int32 := true } F clocks)
      env elems F noisyMul.pdesign.generates =
      .ok (CombHier.GeneratedNode.flattenSegments
        ((noisyFullFamilyPaths N).map (noisyFullFamilySegment env elems))) := by
  rw [noisy_top_expand_actual_depth3 env elems F N clocks hFuel hRowFuel hBound hValue hInnerBound hInnerValue]
  have hseg : ∀ (i j : Int),
      noisyFullFamilySegment env elems
          (.child { loops := ppSourceLoops, inst := andInst, child := andDef }, [i, j]) =
        flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") andInst andDesign := by
    intro i j
    simp [noisyFullFamilySegment, noisyTopNodeSegment, noisyTopGeneratedPairSegment, andInst]
  have hpp :
      ((List.flatMap
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
            (intRange 0 N.toNat)) (intRange 0 N.toNat))) =
      CombHier.GeneratedNode.flattenSegments
        (List.flatMap (fun i =>
          (noisyPpPaths N i).map (noisyFullFamilySegment env elems))
          (intRange 0 N.toNat)) := by
    simp only [CombHier.GeneratedNode.flattenSegments_map]
    simp only [noisyPpPaths, List.map_map, Function.comp_apply]
    simp [hseg, Function.comp_def, List.flatMap_map, List.flatMap_assoc]
  have hchild_each : ∀ i : Int,
      CombHier.GeneratedNode.flattenSegments
          ((noisyRowChildPaths N i).map (noisyFullFamilySegment env elems)) =
        noisy_row_inner_segment env elems i N := by
    intro i
    exact noisyRowChildPaths_flatten env elems N i
  have hchild_fst : ∀ i : Int,
      (noisyRowChildPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).1) =
        (noisy_row_inner_segment env elems i N).1 := by
    intro i
    have h := congrArg Prod.fst (hchild_each i)
    simpa [CombHier.GeneratedNode.flattenSegments_map, List.flatMap_map] using h
  have hchild_snd : ∀ i : Int,
      (noisyRowChildPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).2) =
        (noisy_row_inner_segment env elems i N).2 := by
    intro i
    have h := congrArg Prod.snd (hchild_each i)
    simpa [CombHier.GeneratedNode.flattenSegments_map, List.flatMap_map] using h
  have hrow_each : ∀ i : Int,
      CombHier.GeneratedNode.flattenSegments
          ((noisyRowPaths N i).map (noisyFullFamilySegment env elems)) =
        ((noisy_row_inner_segment env elems i N).1,
         [instProcess2 (env.bindVal "i" i) elems rowLeft] ++
           (noisy_row_inner_segment env elems i N).2 ++
           [instProcess2 (env.bindVal "i" i) elems rowRight]) := by
    intro i
    rw [noisyRowPaths_flatten, hchild_fst i, hchild_snd i]
  have hrow :
      GeneratedChildSegment.flatten
        ((intRange 1 (N - 1).toNat).map fun i =>
          { decls := (noisy_row_inner_segment env elems i N).1,
            processes := instProcess2 (env.bindVal "i" i) elems rowLeft ::
              (noisy_row_inner_segment env elems i N).2 ++
              [instProcess2 (env.bindVal "i" i) elems rowRight] }) =
      CombHier.GeneratedNode.flattenSegments
        (List.flatMap (fun i => (noisyRowPaths N i).map (noisyFullFamilySegment env elems))
          (intRange 1 (N - 1).toNat)) := by
    rw [CombHier.GeneratedNode.flattenSegments_flatMap]
    have hmap :
        (intRange 1 (N - 1).toNat).map
            (fun i => CombHier.GeneratedNode.flattenSegments
              ((noisyRowPaths N i).map (noisyFullFamilySegment env elems))) =
          (intRange 1 (N - 1).toNat).map (fun i =>
            ((noisy_row_inner_segment env elems i N).1,
             [instProcess2 (env.bindVal "i" i) elems rowLeft] ++
               (noisy_row_inner_segment env elems i N).2 ++
               [instProcess2 (env.bindVal "i" i) elems rowRight])) := by
      apply List.map_congr_left
      intro i hi
      exact hrow_each i
    rw [hmap]
    simp [GeneratedChildSegment.flatten, CombHier.GeneratedNode.flattenSegments_map,
      List.flatMap_map, List.flatMap_assoc, List.append_assoc]
  have hout :
      ([], (intRange 0 N.toNat).flatMap fun i =>
        [instProcess2 (env.bindVal "i" i) elems outProc]) =
      CombHier.GeneratedNode.flattenSegments
        ((noisyOutPaths N).map (noisyFullFamilySegment env elems)) := by
    simp only [CombHier.GeneratedNode.flattenSegments_map]
    simp [noisyOutPaths, noisyFullFamilySegment, List.flatMap_map]
  have hpp_fst :
      (List.flatMap (fun i => List.flatMap (fun j =>
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") andInst andDesign).1)
        (intRange 0 N.toNat)) (intRange 0 N.toNat)) =
      (CombHier.GeneratedNode.flattenSegments
        (List.flatMap (fun i => (noisyPpPaths N i).map (noisyFullFamilySegment env elems))
          (intRange 0 N.toNat))).1 := by
    simpa using congrArg Prod.fst hpp
  have hpp_snd :
      (List.flatMap (fun i => List.flatMap (fun j =>
        (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems
          ("g_pp[" ++ toString i ++ "].g_pp_j[" ++ toString j ++ "].u_and.") andInst andDesign).2)
        (intRange 0 N.toNat)) (intRange 0 N.toNat)) =
      (CombHier.GeneratedNode.flattenSegments
        (List.flatMap (fun i => (noisyPpPaths N i).map (noisyFullFamilySegment env elems))
          (intRange 0 N.toNat))).2 := by
    simpa using congrArg Prod.snd hpp
  have hrow_fst := congrArg Prod.fst hrow
  have hrow_snd := congrArg Prod.snd hrow
  have hout_snd := congrArg Prod.snd hout
  have hout_snd' :
      (intRange 0 N.toNat).flatMap (fun i =>
        [instProcess2 (env.bindVal "i" i) elems outProc]) =
      (CombHier.GeneratedNode.flattenSegments
        ((noisyOutPaths N).map (noisyFullFamilySegment env elems))).2 := by
    simpa using hout_snd
  have hout_full_decl :
      (CombHier.GeneratedNode.flattenSegments
        ((noisyOutPaths N).map (noisyFullFamilySegment env elems))).1 = [] := by
    rw [CombHier.GeneratedNode.flattenSegments_map]
    simp [noisyOutPaths, noisyFullFamilySegment, Function.comp_def,
      List.flatMap_map]
  unfold noisyFullFamilyPaths
  simp only [List.map_append, CombHier.GeneratedNode.flattenSegments_append,
    List.map_flatMap]
  rw [hpp_fst, hrow_fst, hpp_snd, hrow_snd, hout_snd', hout_full_decl]


theorem noisy_instantiateH_of_family
    {N : Int} {env : IEnv} {decls : List Decl} {elems : List (String × Nat)}
    {idecls : List Decl} {gens : List Process2}
    (h1 : noisyMul.pdesign.paramEnvH { int32 := true } [N] = .ok env)
    (h2 : buildDecls env noisyMul.pdesign.decls = .ok decls)
    (h3 : buildElems env noisyMul.pdesign.decls = .ok elems)
    (hFuel : N.toNat < PDesign.surfaceFuel [N])
    (hRowFuel : (N - 1).toNat < PDesign.surfaceFuel [N])
    (hBound : ∀ i : Int,
      PExpr.isInt ((env.withDecls decls).bindVal "i" i) (.paramRef "N" none) = true)
    (hValue : ∀ i : Int,
      evalInt ((env.withDecls decls).bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hInnerBound : ∀ i j : Int,
      PExpr.isInt (((env.withDecls decls).bindVal "i" i).bindVal "j" j)
        (.paramRef "N" none) = true)
    (hInnerValue : ∀ i j : Int,
      evalInt (((env.withDecls decls).bindVal "i" i).bindVal "j" j)
        (.paramRef "N" none) = .ok N)
    (hFlat : CombHier.GeneratedNode.flattenSegments
        ((noisyFullFamilyPaths N).map (noisyFullFamilySegment (env.withDecls decls) elems)) =
      (idecls, gens))
    (hok : driversOk noisyMul.pdesign.declNames noisyMul.pdesign.inputNames
      (noisyMul.pdesign.assembleH env decls idecls elems gens).processes.toList = true) :
    noisyMul.pdesign.instantiateH noisyMul.plib [N] (PDesign.surfaceFuel [N]) =
      .ok (noisyMul.pdesign.assembleH env decls idecls elems gens) := by
  apply CombHier.PDesign.instantiateH_of_expansion
  · rfl
  · exact h1
  · exact h2
  · exact h3
  · have hlen : noisyMul.plib.length = 3 := by rfl
    simpa [hFlat, hlen] using
      (noisy_top_expand_family_actual_depth3 (env.withDecls decls) elems
        (PDesign.surfaceFuel [N]) N (Decl.inputNames decls)
        hFuel hRowFuel hBound hValue hInnerBound hInnerValue)
  · exact hok

def noisyScope (N : Int) : IEnv :=
  { int32 := true, nvals := [("N", (canonInt 32 true N, 32, true))],
    pwidths := [("N", 32)] }

def noisyEnv (N : Int) : IEnv :=
  { noisyScope N with dims := dimTableFast (noisyScope N) noisyMul.pdesign.decls }

def noisyDeclsRaw (N : Int) : List Decl :=
  [{ name := "a", width := (canonInt 32 true N - 1).natAbs + 1, isInput := true },
   { name := "b", width := (canonInt 32 true N - 1).natAbs + 1, isInput := true },
   { name := "f", width := ((4 * canonInt 32 true N - 4).natAbs + 1) *
       ((canonInt 32 true N - 1).natAbs + 1), isInput := true },
   { name := "p", width := (2 * canonInt 32 true N - 1).natAbs + 1, isOutput := true },
   { name := "pp", width := ((canonInt 32 true N - 1).natAbs + 1) *
       ((canonInt 32 true N - 1).natAbs + 1) },
   { name := "s", width := ((canonInt 32 true N - 1).natAbs + 1) *
       ((canonInt 32 true N).natAbs + 1) },
   { name := "c", width := ((canonInt 32 true N - 1).natAbs + 1) *
       ((canonInt 32 true N).natAbs + 1) },
   { name := "t", width := ((canonInt 32 true N - 1).natAbs + 1) *
       ((canonInt 32 true N - 1).natAbs + 1) }]

def noisyElems (N : Int) : List (String × Nat) :=
  [("a", 1), ("b", 1), ("f", (canonInt 32 true N - 1).natAbs + 1), ("p", 1),
   ("pp", (canonInt 32 true N - 1).natAbs + 1),
   ("s", (canonInt 32 true N).natAbs + 1), ("c", (canonInt 32 true N).natAbs + 1),
   ("t", (canonInt 32 true N - 1).natAbs + 1)]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem noisy_paramEnvH (N : Int) :
    noisyMul.pdesign.paramEnvH { int32 := true } [N] = .ok (noisyEnv N) := by
  rfl

theorem noisy_decls (N : Int) :
    buildDecls (noisyEnv N) noisyMul.pdesign.decls = .ok (noisyDeclsRaw N) := by
  set_option maxHeartbeats 1000000 in
  simp [noisyMul.pdesign, buildDecls, instDecl, PType.width_packed_cons,
    PType.width_packed_nil, PDim.width, evalInt, noisyEnv, noisyScope,
    noisyDeclsRaw, List.lookup, Gen2.except_ok_bind]

set_option maxHeartbeats 10000000 in
theorem noisy_dims_pp (N : Int) (hCanon : canonInt 32 true N = N) :
    (noisyEnv N).dims.lookup "pp" = some [(N - 1, 0), (N - 1, 0)] := by
  have hsum := @CombView.dimTableFast_summary (fun _ => N)
      noisyMul.pdesign.decls _ (by rfl) (noisyScope N) (by
        intro dt hdt n hn
        simp [CombView.declsOf?, CombView.declOf?, CombView.dimOf?, CombView.affOf?] at hdt
        rcases hdt with hdt | hdt | hdt | hdt | hdt | hdt | hdt | hdt <;>
          subst dt <;>
          simp_all [CombView.DeclT.affNames, CombView.Aff.names, CombView.Aff.var,
            CombView.Aff.const, CombView.Aff.sub, CombView.Aff.scale, CombView.Aff.add,
            CombView.Aff.neg, CombView.Aff.negTerms, CombView.Aff.scaleTerms,
            CombView.Aff.scaleQs, CombView.Aff.scaleXs, CombView.Aff.xsNames,
            CombView.Aff.negQs, CombView.Aff.negXs, CombView.XAt.names,
            noisyScope, IEnv.intVal?, hCanon]) "pp"
  simpa [noisyEnv, noisyScope, hCanon, CombView.DeclT.vals, CombView.Aff.eval,
    CombView.Aff.evalTerms, CombView.Aff.evalQs, CombView.Aff.evalXs,
    CombView.Aff.sub, CombView.Aff.add, CombView.Aff.neg, CombView.Aff.negTerms,
    CombView.Aff.negQs, CombView.Aff.negXs, CombView.Aff.var, CombView.Aff.const,
    List.map, List.append, Int.sub_eq_add_neg] using hsum

set_option maxHeartbeats 10000000 in
theorem noisy_dims_t (N : Int) (hCanon : canonInt 32 true N = N) :
    (noisyEnv N).dims.lookup "t" = some [(N - 1, 0), (N - 1, 0)] := by
  have hsum := @CombView.dimTableFast_summary (fun _ => N)
      noisyMul.pdesign.decls _ (by rfl) (noisyScope N) (by
        intro dt hdt n hn
        simp [CombView.declsOf?, CombView.declOf?, CombView.dimOf?, CombView.affOf?] at hdt
        rcases hdt with hdt | hdt | hdt | hdt | hdt | hdt | hdt | hdt <;>
          subst dt <;>
          simp_all [CombView.DeclT.affNames, CombView.Aff.names, CombView.Aff.var,
            CombView.Aff.const, CombView.Aff.sub, CombView.Aff.scale, CombView.Aff.add,
            CombView.Aff.neg, CombView.Aff.negTerms, CombView.Aff.scaleTerms,
            CombView.Aff.scaleQs, CombView.Aff.scaleXs, CombView.Aff.xsNames,
            CombView.Aff.negQs, CombView.Aff.negXs, CombView.XAt.names,
            noisyScope, IEnv.intVal?, hCanon]) "t"
  simpa [noisyEnv, noisyScope, hCanon, CombView.DeclT.vals, CombView.Aff.eval,
    CombView.Aff.evalTerms, CombView.Aff.evalQs, CombView.Aff.evalXs,
    CombView.Aff.sub, CombView.Aff.add, CombView.Aff.neg, CombView.Aff.negTerms,
    CombView.Aff.negQs, CombView.Aff.negXs, CombView.Aff.var, CombView.Aff.const,
    List.map, List.append, Int.sub_eq_add_neg] using hsum

set_option maxHeartbeats 10000000 in
theorem noisy_dims_s (N : Int) (hCanon : canonInt 32 true N = N) :
    (noisyEnv N).dims.lookup "s" = some [(N - 1, 0), (N, 0)] := by
  have hsum := @CombView.dimTableFast_summary (fun _ => N)
      noisyMul.pdesign.decls _ (by rfl) (noisyScope N) (by
        intro dt hdt n hn
        simp [CombView.declsOf?, CombView.declOf?, CombView.dimOf?, CombView.affOf?] at hdt
        rcases hdt with hdt | hdt | hdt | hdt | hdt | hdt | hdt | hdt <;>
          subst dt <;>
          simp_all [CombView.DeclT.affNames, CombView.Aff.names, CombView.Aff.var,
            CombView.Aff.const, CombView.Aff.sub, CombView.Aff.scale, CombView.Aff.add,
            CombView.Aff.neg, CombView.Aff.negTerms, CombView.Aff.scaleTerms,
            CombView.Aff.scaleQs, CombView.Aff.scaleXs, CombView.Aff.xsNames,
            CombView.Aff.negQs, CombView.Aff.negXs, CombView.XAt.names,
            noisyScope, IEnv.intVal?, hCanon]) "s"
  simpa [noisyEnv, noisyScope, hCanon, CombView.DeclT.vals, CombView.Aff.eval,
    CombView.Aff.evalTerms, CombView.Aff.evalQs, CombView.Aff.evalXs,
    CombView.Aff.sub, CombView.Aff.add, CombView.Aff.neg, CombView.Aff.negTerms,
    CombView.Aff.negQs, CombView.Aff.negXs, CombView.Aff.var, CombView.Aff.const,
    List.map, List.append, Int.sub_eq_add_neg] using hsum

set_option maxHeartbeats 10000000 in
theorem noisy_dims_c (N : Int) (hCanon : canonInt 32 true N = N) :
    (noisyEnv N).dims.lookup "c" = some [(N - 1, 0), (N, 0)] := by
  have hsum := @CombView.dimTableFast_summary (fun _ => N)
      noisyMul.pdesign.decls _ (by rfl) (noisyScope N) (by
        intro dt hdt n hn
        simp [CombView.declsOf?, CombView.declOf?, CombView.dimOf?, CombView.affOf?] at hdt
        rcases hdt with hdt | hdt | hdt | hdt | hdt | hdt | hdt | hdt <;>
          subst dt <;>
          simp_all [CombView.DeclT.affNames, CombView.Aff.names, CombView.Aff.var,
            CombView.Aff.const, CombView.Aff.sub, CombView.Aff.scale, CombView.Aff.add,
            CombView.Aff.neg, CombView.Aff.negTerms, CombView.Aff.scaleTerms,
            CombView.Aff.scaleQs, CombView.Aff.scaleXs, CombView.Aff.xsNames,
            CombView.Aff.negQs, CombView.Aff.negXs, CombView.XAt.names,
            noisyScope, IEnv.intVal?, hCanon]) "c"
  simpa [noisyEnv, noisyScope, hCanon, CombView.DeclT.vals, CombView.Aff.eval,
    CombView.Aff.evalTerms, CombView.Aff.evalQs, CombView.Aff.evalXs,
    CombView.Aff.sub, CombView.Aff.add, CombView.Aff.neg, CombView.Aff.negTerms,
    CombView.Aff.negQs, CombView.Aff.negXs, CombView.Aff.var, CombView.Aff.const,
    List.map, List.append, Int.sub_eq_add_neg] using hsum

theorem noisy_elems (N : Int) :
    buildElems (noisyEnv N) noisyMul.pdesign.decls = .ok (noisyElems N) := by
  set_option maxHeartbeats 1000000 in
  simp [noisyMul.pdesign, buildElems, PType.width_packed_cons,
    PType.width_packed_nil, PType.elemWidth, PDim.width,
    evalInt, noisyEnv, noisyScope,
    noisyElems, List.lookup, Gen2.except_ok_bind, Except.bind, Except.map, Except.pure,
    pure, bind]

theorem noisy_env_N_lookup (N : Int)
    (hCanon : canonInt 32 true N = N) :
    (noisyEnv N).nvals.lookup "N" = some (N, 32, true) := by
  simp [noisyEnv, noisyScope, hCanon, List.lookup]

theorem noisy_canonN (N : Nat) (hR : (N : Int) < 2147483648) :
    canonInt 32 true (N : Int) = N := by
  exact CombView.canonInt32_of_range ⟨by omega, hR⟩

theorem noisy_surfaceFuel_outer (N : Nat) :
    (N : Int).toNat < PDesign.surfaceFuel [(N : Int)] := by
  simp [PDesign.surfaceFuel]
  have hmul : N + 2 ≤ (N + 2) * (N + 2) := by
    exact Nat.le_mul_of_pos_left (N + 2) (by omega)
  omega

theorem noisy_surfaceFuel_row (N : Nat) :
    ((N : Int) - 1).toNat < PDesign.surfaceFuel [(N : Int)] := by
  simp [PDesign.surfaceFuel]
  have hmul : N + 2 ≤ (N + 2) * (N + 2) := by
    exact Nat.le_mul_of_pos_left (N + 2) (by omega)
  omega

theorem noisy_bound (N i : Int)
    (hCanon : canonInt 32 true N = N) :
    PExpr.isInt (((noisyEnv N).withDecls (noisyDeclsRaw N)).bindVal "i" i)
      (.paramRef "N" none) = true := by
  simp [PExpr.isInt, IEnv.bindVal, noisyEnv, noisyScope, noisyDeclsRaw,
    List.lookup, hCanon]

theorem noisy_value (N i : Int)
    (hCanon : canonInt 32 true N = N) :
    evalInt (((noisyEnv N).withDecls (noisyDeclsRaw N)).bindVal "i" i)
      (.paramRef "N" none) = .ok N := by
  simp [evalInt, IEnv.bindVal, noisyEnv, noisyScope, noisyDeclsRaw,
    List.lookup, hCanon]

theorem noisy_inner_bound (N i j : Int)
    (hCanon : canonInt 32 true N = N) :
    PExpr.isInt ((((noisyEnv N).withDecls (noisyDeclsRaw N)).bindVal "i" i).bindVal "j" j)
      (.paramRef "N" none) = true := by
  simp [PExpr.isInt, IEnv.bindVal, noisyEnv, noisyScope, noisyDeclsRaw,
    List.lookup, hCanon]

theorem noisy_inner_value (N i j : Int)
    (hCanon : canonInt 32 true N = N) :
    evalInt ((((noisyEnv N).withDecls (noisyDeclsRaw N)).bindVal "i" i).bindVal "j" j)
      (.paramRef "N" none) = .ok N := by
  simp [evalInt, IEnv.bindVal, noisyEnv, noisyScope, noisyDeclsRaw,
    List.lookup, hCanon]

theorem noisy_instantiateH_of_generated_expansion
    {N : Int} {env : IEnv} {decls : List Decl} {elems : List (String × Nat)}
    {idecls : List Decl} {gens : List Process2}
    (h1 : noisyMul.pdesign.paramEnvH { int32 := true } [N] = .ok env)
    (h2 : buildDecls env noisyMul.pdesign.decls = .ok decls)
    (h3 : buildElems env noisyMul.pdesign.decls = .ok elems)
    (hexpand : CombHier.GeneratedFamilyExpansion
      (PDesign.childRec 3 noisyMul.plib { int32 := true }
        (PDesign.surfaceFuel [N]) (Decl.inputNames decls))
      (env.withDecls decls) elems (PDesign.surfaceFuel [N]) noisyMul.pdesign
      (noisyFullFamilyPaths N) noisyTopNodeChild (idecls, gens))
    (hok : driversOk noisyMul.pdesign.declNames noisyMul.pdesign.inputNames
      (noisyMul.pdesign.assembleH env decls idecls elems gens).processes.toList = true) :
    noisyMul.pdesign.instantiateH noisyMul.plib [N] (PDesign.surfaceFuel [N]) =
      .ok (noisyMul.pdesign.assembleH env decls idecls elems gens) := by
  apply CombHier.PDesign.instantiateH_of_expansion
  · rfl
  · exact h1
  · exact h2
  · exact h3
  · exact hexpand.1
  · exact hok

def noisyStaticProcs (env : IEnv) (decls : List Decl)
    (elems : List (String × Nat)) : List Process2 :=
  noisyMul.pdesign.processes.map (instProcess2 (env.withDecls decls) elems)

theorem noisy_instProcess2_assignL_procWrites (env : IEnv)
    (elems : List (String × Nat)) (lhs : PLhs) (v : PExpr) :
    Process2.procWrites (instProcess2 env elems (.assignL lhs v)) = [] := by
  simp only [instProcess2]
  split <;> rfl

theorem noisy_static_procWrites (env : IEnv) (decls : List Decl)
    (elems : List (String × Nat)) :
    (noisyStaticProcs env decls elems).flatMap Process2.procWrites = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  simp only [noisyStaticProcs, noisyMul.pdesign, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact noisy_instProcess2_assignL_procWrites _ _ _ _
  · exact noisy_instProcess2_assignL_procWrites _ _ _ _
  · exact noisy_instProcess2_assignL_procWrites _ _ _ _
  · exact noisy_instProcess2_assignL_procWrites _ _ _ _

theorem noisy_and_conn_procWrites (env : IEnv) (elems : List (String × Nat))
    (pfx : String) :
    (andDesign.decls.toList.flatMap (connProcs env elems pfx andInst.conns)).flatMap
      Process2.procWrites = [] := by
  rw [List.flatMap_assoc]
  apply List.flatMap_eq_nil_iff.mpr
  intro dc hdc
  simp only [andDesign] at hdc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdc
  rcases hdc with rfl | rfl | rfl | rfl
  · simp [andInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [andInst, andDesign, portInOk, PExpr.portSafe, portOut]
  · simp [andInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [andInst, andDesign, portInOk, PExpr.portSafe, portOut]
  · simp [andInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [andInst, andDesign, portInOk, PExpr.portSafe, portOut]
  · cases hq : instLhs2 env elems (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]) with
    | error e =>
        simp [andInst, connProcs, PConn.port, List.find?, Process2.procWrites,
          Process2.procWins, portInOk, PExpr.portSafe, portOut, hq]
    | ok p =>
        simp [andInst, connProcs, PConn.port, List.find?, Process2.procWrites,
          Process2.procWins, portInOk, PExpr.portSafe, portOut, hq]



theorem noisy_xor_conn_procWrites (env : IEnv) (elems : List (String × Nat))
    (pfx : String) :
    (xorDesign.decls.toList.flatMap (connProcs env elems pfx xorInst.conns)).flatMap
      Process2.procWrites = [] := by
  rw [List.flatMap_assoc]
  apply List.flatMap_eq_nil_iff.mpr
  intro dc hdc
  simp only [xorDesign] at hdc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdc
  rcases hdc with rfl | rfl | rfl | rfl
  · simp [xorInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [xorInst, xorDesign, portInOk, PExpr.portSafe, portOut]
  · simp [xorInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [xorInst, xorDesign, portInOk, PExpr.portSafe, portOut]
  · simp [xorInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [xorInst, xorDesign, portInOk, PExpr.portSafe, portOut]
  · cases hq : instLhs2 env elems (.arrayElem "t" [.genvarRef "i", .genvarRef "j"]) with
    | error e =>
        simp [xorInst, connProcs, PConn.port, List.find?, Process2.procWrites,
          Process2.procWins, portInOk, PExpr.portSafe, portOut, hq]
    | ok p =>
        simp [xorInst, connProcs, PConn.port, List.find?, Process2.procWrites,
          Process2.procWins, portInOk, PExpr.portSafe, portOut, hq]

theorem noisy_maj_conn_procWrites (env : IEnv) (elems : List (String × Nat))
    (pfx : String) :
    (majDesign.decls.toList.flatMap (connProcs env elems pfx majInst.conns)).flatMap
      Process2.procWrites = [] := by
  rw [List.flatMap_assoc]
  apply List.flatMap_eq_nil_iff.mpr
  intro dc hdc
  simp only [majDesign] at hdc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdc
  rcases hdc with rfl | rfl | rfl | rfl | rfl
  · simp [majInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [majInst, majDesign, portInOk, PExpr.portSafe, portOut]
  · simp [majInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [majInst, majDesign, portInOk, PExpr.portSafe, portOut]
  · simp [majInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [majInst, majDesign, portInOk, PExpr.portSafe, portOut]
  · simp [majInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [majInst, majDesign, portInOk, PExpr.portSafe, portOut]
  · cases hq : instLhs2 env elems
        (.arrayElem "c" [.genvarRef "i", .binary (.m0 .add) (.genvarRef "j") (.int 1)]) with
    | error e =>
        simp [majInst, connProcs, PConn.port, List.find?, Process2.procWrites,
          Process2.procWins, portInOk, PExpr.portSafe, portOut, hq]
    | ok p =>
        simp [majInst, connProcs, PConn.port, List.find?, Process2.procWrites,
          Process2.procWins, portInOk, PExpr.portSafe, portOut, hq]


theorem noisy_instBodyProc_assign_procWrites (pfx : String) (i : PInst)
    (ports : List Decl) (bare : List (String × String)) (t : Lhs2) (e : Expr2) :
    Process2.procWrites (instBodyProc pfx i ports bare (.assign t e)) = [] := by
  simp [instBodyProc, Process2.clock?, Process2.rename, Process2.procWrites, Process2.procWins]

theorem noisy_flatten_child_procWrites
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (i : PInst) (c : Design2)
    (hstray : (i.conns.filterMap
      (strayConn c (c.decls.toList.filter fun dc => dc.isInput || dc.isOutput))).flatMap
      Process2.procWrites = [])
    (hconn : ((c.decls.toList.filter fun dc => dc.isInput || dc.isOutput).flatMap
      (connProcs env elems pfx i.conns)).flatMap Process2.procWrites = [])
    (hchild : ∀ p ∈ c.processes.toList,
      ∃ t e, p = .assign t e) :
    (flattenInst env elems pfx i c).2.flatMap Process2.procWrites = [] := by
  simp only [flattenInst, List.flatMap_append, hstray, hconn, List.nil_append, List.append_nil]
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨t, e, rfl⟩ := hchild q hq
  exact noisy_instBodyProc_assign_procWrites pfx i
    (c.decls.toList.filter fun dc => dc.isInput || dc.isOutput)
    (bareInputs env (c.decls.toList.filter fun dc => dc.isInput || dc.isOutput) i.conns) t e



theorem noisy_stray_conn_procWrites (c : Design2) (ports : List Decl)
    (conns : List PConn) :
    (conns.filterMap (strayConn c ports)).flatMap Process2.procWrites = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  simp only [List.mem_filterMap] at hp
  obtain ⟨cn, hcn, hpc⟩ := hp
  cases cn <;> simp [strayConn] at hpc
  all_goals cases p <;> simp_all [Process2.procWrites, Process2.procWins]

theorem noisy_xorS_conn_procWrites (env : IEnv) (elems : List (String × Nat))
    (pfx : String) :
    (xorDesign.decls.toList.flatMap (connProcs env elems pfx xorSInst.conns)).flatMap
      Process2.procWrites = [] := by
  rw [List.flatMap_assoc]
  apply List.flatMap_eq_nil_iff.mpr
  intro dc hdc
  simp only [xorDesign] at hdc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdc
  rcases hdc with rfl | rfl | rfl | rfl
  · simp [xorSInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [xorSInst, xorDesign, portInOk, PExpr.portSafe, portOut]
  · simp [xorSInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [xorSInst, xorDesign, portInOk, PExpr.portSafe, portOut]
  · simp [xorSInst, connProcs, PConn.port, List.find?, Process2.procWrites, Process2.procWins,
      portInOk, PExpr.portSafe, portOut]
    try sv2_inst_simp [xorSInst, xorDesign, portInOk, PExpr.portSafe, portOut]
  · cases hq : instLhs2 env elems (.arrayElem "s" [.genvarRef "i", .genvarRef "j"]) with
    | error e =>
        simp [xorSInst, connProcs, PConn.port, List.find?, Process2.procWrites,
          Process2.procWins, portInOk, PExpr.portSafe, portOut, hq]
    | ok p =>
        simp [xorSInst, connProcs, PConn.port, List.find?, Process2.procWrites,
          Process2.procWins, portInOk, PExpr.portSafe, portOut, hq]

theorem noisy_and_flatten_procWrites (env : IEnv) (elems : List (String × Nat))
    (pfx : String) :
    (flattenInst env elems pfx andInst andDesign).2.flatMap Process2.procWrites = [] := by
  apply noisy_flatten_child_procWrites env elems pfx andInst andDesign
  · exact noisy_stray_conn_procWrites andDesign
      (andDesign.decls.toList.filter fun dc => dc.isInput || dc.isOutput) andInst.conns
  · simpa [andDesign] using noisy_and_conn_procWrites env elems pfx
  · intro p hp
    simp only [andDesign, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact ⟨_, _, rfl⟩

theorem noisy_xor_flatten_procWrites (env : IEnv) (elems : List (String × Nat))
    (pfx : String) :
    (flattenInst env elems pfx xorInst xorDesign).2.flatMap Process2.procWrites = [] := by
  apply noisy_flatten_child_procWrites env elems pfx xorInst xorDesign
  · exact noisy_stray_conn_procWrites xorDesign
      (xorDesign.decls.toList.filter fun dc => dc.isInput || dc.isOutput) xorInst.conns
  · simpa [xorDesign] using noisy_xor_conn_procWrites env elems pfx
  · intro p hp
    simp only [xorDesign, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact ⟨_, _, rfl⟩

theorem noisy_xorS_flatten_procWrites (env : IEnv) (elems : List (String × Nat))
    (pfx : String) :
    (flattenInst env elems pfx xorSInst xorDesign).2.flatMap Process2.procWrites = [] := by
  apply noisy_flatten_child_procWrites env elems pfx xorSInst xorDesign
  · exact noisy_stray_conn_procWrites xorDesign
      (xorDesign.decls.toList.filter fun dc => dc.isInput || dc.isOutput) xorSInst.conns
  · simpa [xorDesign] using noisy_xorS_conn_procWrites env elems pfx
  · intro p hp
    simp only [xorDesign, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact ⟨_, _, rfl⟩

theorem noisy_maj_flatten_procWrites (env : IEnv) (elems : List (String × Nat))
    (pfx : String) :
    (flattenInst env elems pfx majInst majDesign).2.flatMap Process2.procWrites = [] := by
  apply noisy_flatten_child_procWrites env elems pfx majInst majDesign
  · exact noisy_stray_conn_procWrites majDesign
      (majDesign.decls.toList.filter fun dc => dc.isInput || dc.isOutput) majInst.conns
  · simpa [majDesign] using noisy_maj_conn_procWrites env elems pfx
  · intro p hp
    simp only [majDesign, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact ⟨_, _, rfl⟩




theorem noisy_arrayElemTarget_sq_of_range
    {env : IEnv} {elems : List (String × Nat)} {n : String}
    {N i j : Nat} {ie je : PExpr}
    (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (hd : env.dims.lookup n = some [((N : Int) - 1, 0), ((N : Int) - 1, 0)])
    (hie : evalInt env ie = .ok (i : Int))
    (hje : evalInt env je = .ok (j : Int)) :
    instLhs2 env elems (.arrayElem n [ie, je]) =
      .ok (.slice n (i * N + j) 1, 1) := by
  rw [instLhs2_arrayElem, arrayElemTarget_of_inRange
    (arrayElemWindow_desc0_2 hd (by omega) (by omega) hie (by omega) (by omega)
      hje (by omega) (by omega))]
  have hNint : (N : Int) - 1 + 1 = (N : Int) := by omega
  rw [hNint, ← Int.natCast_mul, ← Int.natCast_add, Int.toNat_natCast]


theorem noisy_arrayElemTarget_rect_of_range
    {env : IEnv} {elems : List (String × Nat)} {n : String}
    {N i j : Nat} {ie je : PExpr}
    (hN : 1 ≤ N) (hi : i < N) (hj : j ≤ N)
    (hd : env.dims.lookup n = some [((N : Int) - 1, 0), ((N : Int), 0)])
    (hie : evalInt env ie = .ok (i : Int))
    (hje : evalInt env je = .ok (j : Int)) :
    instLhs2 env elems (.arrayElem n [ie, je]) =
      .ok (.slice n (i * (N + 1) + j) 1, 1) := by
  rw [instLhs2_arrayElem, arrayElemTarget_of_inRange
    (arrayElemWindow_desc0_2 hd (by omega) (by omega) hie (by omega) (by omega)
      hje (by omega) (by omega))]
  have hidx : (i : Int) * ((N : Int) + 1) + (j : Int) =
      ((i * (N + 1) + j : Nat) : Int) := by simp
  rw [hidx, Int.toNat_natCast]





theorem test_noisy_and_conn_driverWins
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String) (l : Lhs2) (w : Nat)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hc : names.contains (pfx ++ "c") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "pp" = true)
    (hl : ∀ x ∈ l.drvWins, x.1 ∈ names)
    (hq : instLhs2 env elems (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]) = .ok (l, w)) :
    driverWins names
      (andDesign.decls.toList.flatMap (connProcs env elems pfx andInst.conns)) = l.drvWins := by
  simp [driverWins, andDesign, andInst, connProcs, PConn.port, List.find?,
    Process2.drvWins, Lhs2.drvWins, portInOk, PExpr.portSafe, portOut,
    ha, hb, hf, hy, hp, hq]
  have ha' : ¬ (pfx ++ "a") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [ha] at ht
    cases ht
  have hb' : ¬ (pfx ++ "b") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hb] at ht
    cases ht
  have hf' : ¬ (pfx ++ "f") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hf] at ht
    cases ht
  have hy' : ¬ (pfx ++ "y") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hy] at ht
    cases ht
  have hlf : List.filter (fun w => decide (w.fst ∈ names)) l.drvWins = l.drvWins := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp [hl x hx]
  simp [ha', hb', hf', hy', hlf]

theorem noisy_xor_conn_driverWins
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String) (l : Lhs2) (w : Nat)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "t" = true)
    (hl : ∀ x ∈ l.drvWins, x.1 ∈ names)
    (hq : instLhs2 env elems (.arrayElem "t" [.genvarRef "i", .genvarRef "j"]) = .ok (l, w)) :
    driverWins names
      (xorDesign.decls.toList.flatMap (connProcs env elems pfx xorInst.conns)) = l.drvWins := by
  simp [driverWins, xorDesign, xorInst, connProcs, PConn.port, List.find?,
    Process2.drvWins, Lhs2.drvWins, portInOk, PExpr.portSafe, portOut,
    ha, hb, hf, hy, hp, hq]
  have ha' : ¬ (pfx ++ "a") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [ha] at ht
    cases ht
  have hb' : ¬ (pfx ++ "b") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hb] at ht
    cases ht
  have hf' : ¬ (pfx ++ "f") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hf] at ht
    cases ht
  have hy' : ¬ (pfx ++ "y") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hy] at ht
    cases ht
  have hlf : List.filter (fun w => decide (w.fst ∈ names)) l.drvWins = l.drvWins := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp [hl x hx]
  simp [ha', hb', hf', hy', hlf]

theorem noisy_xorS_conn_driverWins
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String) (l : Lhs2) (w : Nat)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "s" = true)
    (hl : ∀ x ∈ l.drvWins, x.1 ∈ names)
    (hq : instLhs2 env elems (.arrayElem "s" [.genvarRef "i", .genvarRef "j"]) = .ok (l, w)) :
    driverWins names
      (xorDesign.decls.toList.flatMap (connProcs env elems pfx xorSInst.conns)) = l.drvWins := by
  simp [driverWins, xorDesign, xorSInst, connProcs, PConn.port, List.find?,
    Process2.drvWins, Lhs2.drvWins, portInOk, PExpr.portSafe, portOut,
    ha, hb, hf, hy, hp, hq]
  have ha' : ¬ (pfx ++ "a") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [ha] at ht
    cases ht
  have hb' : ¬ (pfx ++ "b") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hb] at ht
    cases ht
  have hf' : ¬ (pfx ++ "f") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hf] at ht
    cases ht
  have hy' : ¬ (pfx ++ "y") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hy] at ht
    cases ht
  have hlf : List.filter (fun w => decide (w.fst ∈ names)) l.drvWins = l.drvWins := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp [hl x hx]
  simp [ha', hb', hf', hy', hlf]

theorem noisy_maj_conn_driverWins
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String) (l : Lhs2) (w : Nat)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hc : names.contains (pfx ++ "c") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "c" = true)
    (hl : ∀ x ∈ l.drvWins, x.1 ∈ names)
    (hq : instLhs2 env elems
      (.arrayElem "c" [.genvarRef "i",
        .binary (.m0 .add) (.genvarRef "j") (.int 1)]) = .ok (l, w)) :
    driverWins names
      (majDesign.decls.toList.flatMap (connProcs env elems pfx majInst.conns)) = l.drvWins := by
  simp [driverWins, majDesign, majInst, connProcs, PConn.port, List.find?,
    Process2.drvWins, Lhs2.drvWins, portInOk, PExpr.portSafe, portOut,
    ha, hb, hc, hf, hy, hp, hq]
  have ha' : ¬ (pfx ++ "a") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [ha] at ht
    cases ht
  have hb' : ¬ (pfx ++ "b") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hb] at ht
    cases ht
  have hf' : ¬ (pfx ++ "f") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hf] at ht
    cases ht
  have hc' : ¬ (pfx ++ "c") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hc] at ht
    cases ht
  have hy' : ¬ (pfx ++ "y") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hy] at ht
    cases ht
  have hlf : List.filter (fun w => decide (w.fst ∈ names)) l.drvWins = l.drvWins := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp [hl x hx]
  simp [ha', hb', hc', hf', hy', hlf]

theorem noisy_row_major_cell_windows_disjoint
    {N i₁ j₁ i₂ j₂ : Nat} (hN : 1 ≤ N)
    (hi₁ : i₁ < N) (hj₁ : j₁ < N)
    (hi₂ : i₂ < N) (hj₂ : j₂ < N)
    (hneq : i₁ ≠ i₂ ∨ j₁ ≠ j₂) :
    DrvWin.overlaps
      ("pp", some (i₁ * N + j₁, 1))
      ("pp", some (i₂ * N + j₂, 1)) = false := by
  have hidx : i₁ * N + j₁ ≠ i₂ * N + j₂ := by
    intro heq
    by_cases hir : i₁ = i₂
    · rcases hneq with h | h
      · exact (h hir).elim
      · subst i₂
        omega
    · rcases Nat.lt_or_gt_of_ne hir with hlt | hgt
      · have htop : i₁ * N + j₁ < (i₁ + 1) * N := by
          simp [Nat.add_mul]
          omega
        have hrow : (i₁ + 1) * N ≤ i₂ * N := by
          exact Nat.mul_le_mul_right N (Nat.succ_le_of_lt hlt)
        omega
      · have htop : i₂ * N + j₂ < (i₂ + 1) * N := by
          simp [Nat.add_mul]
          omega
        have hrow : (i₂ + 1) * N ≤ i₁ * N := by
          exact Nat.mul_le_mul_right N (Nat.succ_le_of_lt hgt)
        omega
  by_cases hlt : i₁ * N + j₁ < i₂ * N + j₂
  · simp [DrvWin.overlaps]
    omega
  · have hgt : i₂ * N + j₂ < i₁ * N + j₁ := by omega
    simp [DrvWin.overlaps]
    omega

theorem noisy_row_major_rect_windows_disjoint
    {N i₁ j₁ i₂ j₂ : Nat} (hN : 1 ≤ N)
    (hi₁ : i₁ < N) (hj₁ : j₁ ≤ N)
    (hi₂ : i₂ < N) (hj₂ : j₂ ≤ N)
    (hneq : i₁ ≠ i₂ ∨ j₁ ≠ j₂) (signal : String) :
    DrvWin.overlaps
      (signal, some (i₁ * (N + 1) + j₁, 1))
      (signal, some (i₂ * (N + 1) + j₂, 1)) = false := by
  have hcols : j₁ < N + 1 ∧ j₂ < N + 1 := by omega
  have hidx : i₁ * (N + 1) + j₁ ≠ i₂ * (N + 1) + j₂ := by
    intro heq
    by_cases hir : i₁ = i₂
    · rcases hneq with h | h
      · exact (h hir).elim
      · subst i₂
        omega
    · rcases Nat.lt_or_gt_of_ne hir with hlt | hgt
      · have htop : i₁ * (N + 1) + j₁ < (i₁ + 1) * (N + 1) := by
          simp [Nat.add_mul]
          omega
        have hrow : (i₁ + 1) * (N + 1) ≤ i₂ * (N + 1) := by
          exact Nat.mul_le_mul_right (N + 1) (Nat.succ_le_of_lt hlt)
        omega
      · have htop : i₂ * (N + 1) + j₂ < (i₂ + 1) * (N + 1) := by
          simp [Nat.add_mul]
          omega
        have hrow : (i₂ + 1) * (N + 1) ≤ i₁ * (N + 1) := by
          exact Nat.mul_le_mul_right (N + 1) (Nat.succ_le_of_lt hgt)
        omega
  by_cases hlt : i₁ * (N + 1) + j₁ < i₂ * (N + 1) + j₂
  · simp [DrvWin.overlaps]
    omega
  · have hgt : i₂ * (N + 1) + j₂ < i₁ * (N + 1) + j₁ := by omega
    simp [DrvWin.overlaps]
    omega

theorem noisy_different_signal_windows_disjoint
    {a b : String} {x y : Option (Nat × Nat)} (hne : a ≠ b) :
    DrvWin.overlaps (a, x) (b, y) = false := by
  simp [DrvWin.overlaps, hne]

theorem noisy_square_family_windows_pairwise (N : Nat) (hN : 1 ≤ N)
    (signal : String) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      ((List.range N).flatMap (fun i =>
        (List.range N).map (fun j => (signal, some (i * N + j, 1))))) := by
  rw [List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range.imp ?_)
    intro j k hjk
    have hidx : i * N + j < i * N + k := by omega
    simp [DrvWin.overlaps]
    omega

  · refine List.pairwise_lt_range.imp ?_
    intro i k hik x hx y hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨l, hl, rfl⟩ := hy
    have htop : i * N + j < (i + 1) * N := by
      simp [Nat.add_mul]
      omega
    have hrow : (i + 1) * N ≤ k * N := by
      exact Nat.mul_le_mul_right N (Nat.succ_le_of_lt hik)
    simp [DrvWin.overlaps]
    omega

theorem noisy_pp_family_windows_pairwise (N : Nat) (hN : 1 ≤ N) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      ((List.range N).flatMap (fun i =>
        (List.range N).map (fun j => ("pp", some (i * N + j, 1))))) := by
  simpa using noisy_square_family_windows_pairwise N hN "pp"

theorem noisy_rect_family_windows_pairwise (N : Nat) (hN : 1 ≤ N)
    (signal : String) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      ((List.range N).flatMap (fun i =>
        (List.range (N + 1)).map (fun j =>
          (signal, some (i * (N + 1) + j, 1))))) := by
  rw [List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp ?_
    intro j k hjk
    have hidx : i * (N + 1) + j < i * (N + 1) + k := by omega
    simp [DrvWin.overlaps]
    omega
  · refine List.pairwise_lt_range.imp ?_
    intro i k hik x hx y hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨l, hl, rfl⟩ := hy
    have htop : i * (N + 1) + j < (i + 1) * (N + 1) := by
      simp [Nat.add_mul]
      omega
    have hrow : (i + 1) * (N + 1) ≤ k * (N + 1) := by
      exact Nat.mul_le_mul_right (N + 1) (Nat.succ_le_of_lt hik)
    simp [DrvWin.overlaps]
    omega

theorem noisy_arrayElemTarget_sq_genvar
    {env : IEnv} {elems : List (String × Nat)} {n : String}
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (hd : env.dims.lookup n = some [((N : Int) - 1, 0), ((N : Int) - 1, 0)]) :
    instLhs2 ((env.bindVal "i" i).bindVal "j" j) elems
        (.arrayElem n [.genvarRef "i", .genvarRef "j"]) =
      .ok (.slice n (i * N + j) 1, 1) := by
  refine noisy_arrayElemTarget_sq_of_range
    (env := (env.bindVal "i" i).bindVal "j" j) (elems := elems) hN hi hj ?_ ?_ ?_
  · simpa [IEnv.bindVal] using hd
  · exact evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])
  · exact evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])

theorem noisy_and_conn_driverWins_at
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hc : names.contains (pfx ++ "c") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "pp" = true)
    (hd : env.dims.lookup "pp" = some [((N : Int) - 1, 0), ((N : Int) - 1, 0)]) :
    driverWins names
      (andDesign.decls.toList.flatMap
        (connProcs ((env.bindVal "i" i).bindVal "j" j) elems pfx andInst.conns)) =
      [("pp", some (i * N + j, 1))] := by
  have hq := noisy_arrayElemTarget_sq_genvar (env := env) (elems := elems)
    (n := "pp") hN hi hj hd
  apply test_noisy_and_conn_driverWins ((env.bindVal "i" i).bindVal "j" j)
    elems pfx names
    (.slice "pp" (i * N + j) 1) 1 ha hb hc hf hy hp
  · simp [Lhs2.drvWins]
    exact List.contains_iff_mem.mp hp
  · simpa using hq

theorem noisy_xor_conn_driverWins_at
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "t" = true)
    (hd : env.dims.lookup "t" = some [((N : Int) - 1, 0), ((N : Int) - 1, 0)]) :
    driverWins names
      (xorDesign.decls.toList.flatMap
        (connProcs ((env.bindVal "i" i).bindVal "j" j) elems pfx xorInst.conns)) =
      [("t", some (i * N + j, 1))] := by
  have hq := noisy_arrayElemTarget_sq_genvar (env := env) (elems := elems)
    (n := "t") hN hi hj hd
  apply noisy_xor_conn_driverWins ((env.bindVal "i" i).bindVal "j" j)
    elems pfx names (.slice "t" (i * N + j) 1) 1 ha hb hf hy hp
  · simp [Lhs2.drvWins]
    exact List.contains_iff_mem.mp hp
  · simpa using hq

theorem noisy_arrayElemTarget_rect_genvar
    {env : IEnv} {elems : List (String × Nat)} {n : String}
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j ≤ N)
    (hd : env.dims.lookup n = some [((N : Int) - 1, 0), ((N : Int), 0)]) :
    instLhs2 ((env.bindVal "i" i).bindVal "j" j) elems
        (.arrayElem n [.genvarRef "i", .genvarRef "j"]) =
      .ok (.slice n (i * (N + 1) + j) 1, 1) := by
  refine noisy_arrayElemTarget_rect_of_range
    (env := (env.bindVal "i" i).bindVal "j" j) (elems := elems) hN hi hj ?_ ?_ ?_
  · simpa [IEnv.bindVal] using hd
  · exact evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])
  · exact evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])

theorem noisy_xorS_conn_driverWins_at
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j ≤ N)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "s" = true)
    (hd : env.dims.lookup "s" = some [((N : Int) - 1, 0), ((N : Int), 0)]) :
    driverWins names
      (xorDesign.decls.toList.flatMap
        (connProcs ((env.bindVal "i" i).bindVal "j" j) elems pfx xorSInst.conns)) =
      [("s", some (i * (N + 1) + j, 1))] := by
  have hq := noisy_arrayElemTarget_rect_genvar (env := env) (elems := elems)
    (n := "s") hN hi hj hd
  apply noisy_xorS_conn_driverWins ((env.bindVal "i" i).bindVal "j" j)
    elems pfx names (.slice "s" (i * (N + 1) + j) 1) 1 ha hb hf hy hp
  · simp [Lhs2.drvWins]
    exact List.contains_iff_mem.mp hp
  · simpa using hq

theorem noisy_maj_conn_driverWins_at
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hc : names.contains (pfx ++ "c") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "c" = true)
    (hd : env.dims.lookup "c" = some [((N : Int) - 1, 0), ((N : Int), 0)]) :
    driverWins names
      (majDesign.decls.toList.flatMap
        (connProcs ((env.bindVal "i" i).bindVal "j" j) elems pfx majInst.conns)) =
      [("c", some (i * (N + 1) + (j + 1), 1))] := by
  have hq := noisy_arrayElemTarget_rect_of_range
    (env := (env.bindVal "i" i).bindVal "j" j) (elems := elems)
    (n := "c") (N := N) (i := i) (j := j + 1)
    (ie := .genvarRef "i")
    (je := .binary (.m0 .add) (.genvarRef "j") (.int 1))
    hN hi (by omega) hd
    (evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup]))
    (by
      have hjv : evalInt ((env.bindVal "i" i).bindVal "j" j)
          (.genvarRef "j") = .ok (j : Int) :=
        evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])
      rw [evalInt_add_of rfl rfl
        hjv (evalInt_int 1)]
      simp)
  apply noisy_maj_conn_driverWins ((env.bindVal "i" i).bindVal "j" j)
    elems pfx names (.slice "c" (i * (N + 1) + (j + 1)) 1) 1 ha hb hc hf hy hp
  · simp [Lhs2.drvWins]
    exact List.contains_iff_mem.mp hp
  · simpa using hq


theorem noisy_xor_flatten_driverWins_at
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "t" = true)
    (hd : env.dims.lookup "t" = some [((N : Int) - 1, 0), ((N : Int) - 1, 0)]) :
    driverWins names
      (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems pfx xorInst xorDesign).2 =
      [("t", some (i * N + j, 1))] := by
  have hconn := noisy_xor_conn_driverWins_at
    (N := N) (i := i) (j := j) hN hi hj
    env elems pfx names ha hb hf hy hp hd
  unfold flattenInst
  rw [driverWins_append, driverWins_append]
  have hconn' : driverWins names
      ((xorDesign.decls.toList.filter (fun dc => dc.isInput || dc.isOutput)).flatMap
        (connProcs ((env.bindVal "i" i).bindVal "j" j) elems pfx xorInst.conns)) =
      [("t", some (i * N + j, 1))] := by
    simpa [xorDesign] using hconn
  rw [hconn']
  have ha' : ¬ (pfx ++ "a") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [ha] at ht
    cases ht
  have hb' : ¬ (pfx ++ "b") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hb] at ht
    cases ht
  have hf' : ¬ (pfx ++ "f") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hf] at ht
    cases ht
  have hy' : ¬ (pfx ++ "y") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hy] at ht
    cases ht
  simp [driverWins, xorDesign, xorInst, instBodyProc, Process2.drvWins,
    Lhs2.drvWins, connProcs, PConn.port, List.find?, portInOk,
    PExpr.portSafe, portOut, strayConn, Process2.rename, Lhs2.rename,
    Expr2.rename, Process2.clock?, ha, hb, hf, hy, hp, ha', hb', hf', hy']

theorem noisy_and_flatten_driverWins_at
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hc : names.contains (pfx ++ "c") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "pp" = true)
    (hd : env.dims.lookup "pp" = some [((N : Int) - 1, 0), ((N : Int) - 1, 0)]) :
    driverWins names
      (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems pfx andInst andDesign).2 =
      [("pp", some (i * N + j, 1))] := by
  have hconn := noisy_and_conn_driverWins_at
    (N := N) (i := i) (j := j) hN hi hj
    env elems pfx names ha hb hc hf hy hp hd
  unfold flattenInst
  rw [driverWins_append, driverWins_append]
  have hconn' : driverWins names
      ((andDesign.decls.toList.filter (fun dc => dc.isInput || dc.isOutput)).flatMap
        (connProcs ((env.bindVal "i" i).bindVal "j" j) elems pfx andInst.conns)) =
      [("pp", some (i * N + j, 1))] := by
    simpa [andDesign] using hconn
  rw [hconn']
  have ha' : ¬ (pfx ++ "a") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [ha] at ht
    cases ht
  have hb' : ¬ (pfx ++ "b") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hb] at ht
    cases ht
  have hc' : ¬ (pfx ++ "c") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hc] at ht
    cases ht
  have hf' : ¬ (pfx ++ "f") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hf] at ht
    cases ht
  have hy' : ¬ (pfx ++ "y") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hy] at ht
    cases ht
  simp [driverWins, andDesign, andInst, instBodyProc, Process2.drvWins,
    Lhs2.drvWins, connProcs, PConn.port, List.find?, portInOk,
    PExpr.portSafe, portOut, strayConn, Process2.rename, Lhs2.rename,
    Expr2.rename, Process2.clock?, ha, hb, hc, hf, hy, hp, ha', hb', hc', hf', hy']

theorem noisy_xorS_flatten_driverWins_at
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j ≤ N)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "s" = true)
    (hd : env.dims.lookup "s" = some [((N : Int) - 1, 0), ((N : Int), 0)]) :
    driverWins names
      (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems pfx xorSInst xorDesign).2 =
      [("s", some (i * (N + 1) + j, 1))] := by
  have hconn := noisy_xorS_conn_driverWins_at
    (N := N) (i := i) (j := j) hN hi hj
    env elems pfx names ha hb hf hy hp hd
  unfold flattenInst
  rw [driverWins_append, driverWins_append]
  have hconn' : driverWins names
      ((xorDesign.decls.toList.filter (fun dc => dc.isInput || dc.isOutput)).flatMap
        (connProcs ((env.bindVal "i" i).bindVal "j" j) elems pfx xorSInst.conns)) =
      [("s", some (i * (N + 1) + j, 1))] := by
    simpa [xorDesign] using hconn
  rw [hconn']
  have ha' : ¬ (pfx ++ "a") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [ha] at ht
    cases ht
  have hb' : ¬ (pfx ++ "b") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hb] at ht
    cases ht
  have hf' : ¬ (pfx ++ "f") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hf] at ht
    cases ht
  have hy' : ¬ (pfx ++ "y") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hy] at ht
    cases ht
  simp [driverWins, xorDesign, xorSInst, instBodyProc, Process2.drvWins,
    Lhs2.drvWins, connProcs, PConn.port, List.find?, portInOk,
    PExpr.portSafe, portOut, strayConn, Process2.rename, Lhs2.rename,
    Expr2.rename, Process2.clock?, ha, hb, hf, hy, hp, ha', hb', hf', hy']

theorem noisy_maj_flatten_driverWins_at
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (ha : names.contains (pfx ++ "a") = false)
    (hb : names.contains (pfx ++ "b") = false)
    (hc : names.contains (pfx ++ "c") = false)
    (hf : names.contains (pfx ++ "f") = false)
    (hy : names.contains (pfx ++ "y") = false)
    (hp : names.contains "c" = true)
    (hd : env.dims.lookup "c" = some [((N : Int) - 1, 0), ((N : Int), 0)]) :
    driverWins names
      (flattenInst ((env.bindVal "i" i).bindVal "j" j) elems pfx majInst majDesign).2 =
      [("c", some (i * (N + 1) + (j + 1), 1))] := by
  have hconn := noisy_maj_conn_driverWins_at
    (N := N) (i := i) (j := j) hN hi hj
    env elems pfx names ha hb hc hf hy hp hd
  unfold flattenInst
  rw [driverWins_append, driverWins_append]
  have hconn' : driverWins names
      ((majDesign.decls.toList.filter (fun dc => dc.isInput || dc.isOutput)).flatMap
        (connProcs ((env.bindVal "i" i).bindVal "j" j) elems pfx majInst.conns)) =
      [("c", some (i * (N + 1) + (j + 1), 1))] := by
    simpa [majDesign] using hconn
  rw [hconn']
  have ha' : ¬ (pfx ++ "a") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [ha] at ht
    cases ht
  have hb' : ¬ (pfx ++ "b") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hb] at ht
    cases ht
  have hc' : ¬ (pfx ++ "c") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hc] at ht
    cases ht
  have hf' : ¬ (pfx ++ "f") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hf] at ht
    cases ht
  have hy' : ¬ (pfx ++ "y") ∈ names := by
    intro h
    have ht := List.contains_iff.mpr h
    rw [hy] at ht
    cases ht
  simp [driverWins, majDesign, majInst, instBodyProc, Process2.drvWins,
    Lhs2.drvWins, connProcs, PConn.port, List.find?, portInOk,
    PExpr.portSafe, portOut, strayConn, Process2.rename, Lhs2.rename,
    Expr2.rename, Process2.clock?, ha, hb, hc, hf, hy, hp, ha', hb', hc', hf', hy']



theorem noisy_pp_child_driverWins_flat
    (N : Nat)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (hwin : ∀ i j : Nat, i < N → j < N →
      driverWins names
        (andDesign.decls.toList.flatMap
          (connProcs ((env.bindVal "i" (i : Int)).bindVal "j" (j : Int)) elems pfx andInst.conns)) =
        [("pp", some (i * N + j, 1))]) :
    driverWins names
        ((List.range N).flatMap (fun (i : Nat) =>
          (List.range N).flatMap (fun (j : Nat) =>
            andDesign.decls.toList.flatMap
              (connProcs ((env.bindVal "i" (i : Int)).bindVal "j" (j : Int)) elems pfx andInst.conns)))) =
      (List.range N).flatMap (fun (i : Nat) =>
        (List.range N).flatMap (fun (j : Nat) =>
          [("pp", some (i * N + j, 1))])) := by
  have flatMap_congr : ∀ (l : List Nat) (f g : Nat → List DrvWin),
      (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
        intro f g h
        simp only [List.flatMap_cons]
        rw [h x (by simp)]
        exact congrArg (fun z => g x ++ z) (ih f g (by
          intro y hy
          exact h y (by simp [hy])))
  rw [driverWins_flatMap]
  apply flatMap_congr
  intro i hi
  rw [driverWins_flatMap]
  apply flatMap_congr
  intro j hj
  simpa using hwin i j (List.mem_range.mp hi) (List.mem_range.mp hj)

theorem noisy_pp_child_driverWins_pairwise
    (N : Nat) (hN : 1 ≤ N)
    (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (names : List String)
    (hwin : ∀ i j : Nat, i < N → j < N →
      driverWins names
        (andDesign.decls.toList.flatMap
          (connProcs ((env.bindVal "i" (i : Int)).bindVal "j" (j : Int)) elems pfx andInst.conns)) =
        [("pp", some (i * N + j, 1))]) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (driverWins names
        ((List.range N).flatMap (fun (i : Nat) =>
          (List.range N).flatMap (fun (j : Nat) =>
            andDesign.decls.toList.flatMap
              (connProcs ((env.bindVal "i" (i : Int)).bindVal "j" (j : Int)) elems pfx andInst.conns))))) := by
  rw [noisy_pp_child_driverWins_flat N env elems pfx names hwin]
  have hsingleton : ∀ (l : List Nat) (f : Nat → DrvWin),
      l.flatMap (fun j => [f j]) = l.map f := by
    intro l f
    induction l with
    | nil => rfl
    | cons j js ih => simp [ih]
  have flatMap_congr : ∀ (l : List Nat) (f g : Nat → List DrvWin),
      (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
        intro f g h
        simp only [List.flatMap_cons]
        rw [h x (by simp)]
        exact congrArg (fun z => g x ++ z) (ih f g (by
          intro y hy
          exact h y (by simp [hy])))
  have hnorm :
      (List.range N).flatMap (fun (i : Nat) =>
        (List.range N).flatMap (fun (j : Nat) =>
          [("pp", some (i * N + j, 1))])) =
      (List.range N).flatMap (fun (i : Nat) =>
        (List.range N).map (fun (j : Nat) =>
          ("pp", some (i * N + j, 1)))) := by
    apply flatMap_congr
    intro i hi
    exact hsingleton (List.range N) (fun j => ("pp", some (i * N + j, 1)))
  rw [hnorm]
  exact noisy_pp_family_windows_pairwise N hN

theorem noisy_pp_paths_driverWins
    (N : Nat) (env : IEnv) (elems : List (String × Nat))
    (names : List String)
    (hwin : ∀ i ∈ intRange 0 (N : Int).toNat,
      ∀ j ∈ intRange 0 (N : Int).toNat,
        driverWins names
          ((noisyFullFamilySegment env elems
            (.child { loops := ppSourceLoops, inst := andInst, child := andDef },
              [i, j])).2) =
          [("pp", some (i.toNat * N + j.toNat, 1))]) :
    driverWins names
        ((intRange 0 (N : Int).toNat).flatMap (fun i =>
          (noisyPpPaths N i).flatMap
            (fun p => (noisyFullFamilySegment env elems p).2))) =
      (intRange 0 (N : Int).toNat).flatMap (fun i =>
        (intRange 0 (N : Int).toNat).flatMap (fun j =>
          [("pp", some (i.toNat * N + j.toNat, 1))])) := by
  rw [driverWins_flatMap]
  apply CombView.flatMap_congr'
  intro i hi
  have hshape :
      (noisyPpPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).2) =
        (intRange 0 (N : Int).toNat).flatMap (fun j =>
          (noisyFullFamilySegment env elems
            (.child { loops := ppSourceLoops, inst := andInst, child := andDef },
              [i, j])).2) := by
    simp only [noisyPpPaths]
    induction (intRange 0 (N : Int).toNat) with
    | nil => rfl
    | cons j js ih =>
        simp only [List.map_cons, List.flatMap_cons]
        rw [ih]
  rw [hshape, driverWins_flatMap]
  apply CombView.flatMap_congr'
  intro j hj
  exact hwin i hi j hj

theorem noisy_pp_path_driverWins_at
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (env : IEnv) (elems : List (String × Nat)) (names : List String)
    (ha : names.contains (("g_pp[" ++ toString (i : Int) ++ "].g_pp_j[" ++
      toString (j : Int) ++ "].u_and.") ++ "a") = false)
    (hb : names.contains (("g_pp[" ++ toString (i : Int) ++ "].g_pp_j[" ++
      toString (j : Int) ++ "].u_and.") ++ "b") = false)
    (hc : names.contains (("g_pp[" ++ toString (i : Int) ++ "].g_pp_j[" ++
      toString (j : Int) ++ "].u_and.") ++ "c") = false)
    (hf : names.contains (("g_pp[" ++ toString (i : Int) ++ "].g_pp_j[" ++
      toString (j : Int) ++ "].u_and.") ++ "f") = false)
    (hy : names.contains (("g_pp[" ++ toString (i : Int) ++ "].g_pp_j[" ++
      toString (j : Int) ++ "].u_and.") ++ "y") = false)
    (hp : names.contains "pp" = true)
    (hd : env.dims.lookup "pp" = some [((N : Int) - 1, 0), ((N : Int) - 1, 0)]) :
    driverWins names
      (noisyFullFamilySegment env elems
        (.child { loops := ppSourceLoops, inst := andInst, child := andDef },
          [i, j])).2 =
      [("pp", some (i * N + j, 1))] := by
  simpa [noisyFullFamilySegment, noisyTopNodeSegment,
    noisyTopGeneratedPairSegment, noisyTopNodeChild, andInst] using
    (noisy_and_flatten_driverWins_at hN hi hj env elems
      ("g_pp[" ++ toString (i : Int) ++ "].g_pp_j[" ++
        toString (j : Int) ++ "].u_and.") names ha hb hc hf hy hp hd)

theorem noisy_out_paths_driverWins
    (N : Nat) (env : IEnv) (elems : List (String × Nat))
    (names : List String)
    (hwin : ∀ i ∈ intRange 0 (N : Int).toNat,
      driverWins names [instProcess2 (env.bindVal "i" i) elems outProc] =
        [("p", some (i.toNat, 1))]) :
    driverWins names
        ((noisyOutPaths N).flatMap
          (fun p => (noisyFullFamilySegment env elems p).2)) =
      (intRange 0 (N : Int).toNat).flatMap (fun i =>
        [("p", some (i.toNat, 1))]) := by
  simp only [noisyOutPaths, List.flatMap_map]
  rw [driverWins_flatMap]
  apply CombView.flatMap_congr'
  intro i hi
  exact hwin i hi

theorem noisy_generated_family_driverWins_append
    (names : List String)
    (pp row out : List Process2)
    (ppWins rowWins outWins : List DrvWin)
    (hpp : driverWins names pp = ppWins)
    (hrow : driverWins names row = rowWins)
    (hout : driverWins names out = outWins) :
    driverWins names (pp ++ row ++ out) = ppWins ++ rowWins ++ outWins := by
  rw [driverWins_append, driverWins_append, hpp, hrow, hout]

theorem noisy_generated_family_driverWins_flat
    (rows cols : Nat) (signal : String)
    (off : Nat → Nat → Nat)
    (family : Nat → Nat → List Process2)
    (names : List String)
    (hwin : ∀ i j : Nat, i < rows → j < cols →
      driverWins names (family i j) = [(signal, some (off i j, 1))]) :
    driverWins names
        ((List.range rows).flatMap (fun i =>
          (List.range cols).flatMap (fun j => family i j))) =
      (List.range rows).flatMap (fun i =>
        (List.range cols).flatMap (fun j => [(signal, some (off i j, 1))])) := by
  have flatMap_congr : ∀ (l : List Nat) (f g : Nat → List DrvWin),
      (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
        intro f g h
        simp only [List.flatMap_cons]
        rw [h x (by simp)]
        exact congrArg (fun z => g x ++ z) (ih f g (by
          intro y hy
          exact h y (by simp [hy])))
  rw [driverWins_flatMap]
  apply flatMap_congr
  intro i hi
  rw [driverWins_flatMap]
  apply flatMap_congr
  intro j hj
  exact hwin i j (List.mem_range.mp hi) (List.mem_range.mp hj)

theorem noisy_generated_family_driverWins_pairwise
    (rows cols : Nat) (signal : String)
    (off : Nat → Nat → Nat)
    (family : Nat → Nat → List Process2)
    (names : List String)
    (hwin : ∀ i j : Nat, i < rows → j < cols →
      driverWins names (family i j) = [(signal, some (off i j, 1))])
    (hdis : List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      ((List.range rows).flatMap (fun i =>
        (List.range cols).flatMap (fun j =>
          [(signal, some (off i j, 1))])))) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (driverWins names
        ((List.range rows).flatMap (fun i =>
          (List.range cols).flatMap (fun j => family i j)))) := by
  rw [noisy_generated_family_driverWins_flat rows cols signal off family names hwin]
  exact hdis

theorem noisy_generated_family_driverWins_flat_lists
    {α β : Type} (rows : List α) (cols : List β) (signal : String)
    (off : α → β → Nat)
    (family : α → β → List Process2)
    (names : List String)
    (hwin : ∀ i ∈ rows, ∀ j ∈ cols,
      driverWins names (family i j) = [(signal, some (off i j, 1))]) :
    driverWins names
        (rows.flatMap (fun i => cols.flatMap (fun j => family i j))) =
      rows.flatMap (fun i => cols.flatMap (fun j =>
        [(signal, some (off i j, 1))])) := by
  have flatMap_congr : ∀ {γ δ : Type} (l : List γ) (f g : γ → List δ),
      (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g := by
    intro γ δ l
    induction l with
    | nil => simp
    | cons x xs ih =>
        intro f g h
        simp only [List.flatMap_cons]
        rw [h x (by simp)]
        exact congrArg (fun z => g x ++ z) (ih f g (by
          intro y hy
          exact h y (by simp [hy])))
  rw [driverWins_flatMap]
  apply flatMap_congr
  intro i hi
  rw [driverWins_flatMap]
  apply flatMap_congr
  intro j hj
  exact hwin i hi j hj

theorem noisy_generated_family_driverWins_pairwise_lists
    {α β : Type} (rows : List α) (cols : List β) (signal : String)
    (off : α → β → Nat)
    (family : α → β → List Process2)
    (names : List String)
    (hwin : ∀ i ∈ rows, ∀ j ∈ cols,
      driverWins names (family i j) = [(signal, some (off i j, 1))])
    (hdis : List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (rows.flatMap (fun i => cols.flatMap (fun j =>
        [(signal, some (off i j, 1))])))) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (driverWins names (rows.flatMap (fun i => cols.flatMap (fun j => family i j)))) := by
  rw [noisy_generated_family_driverWins_flat_lists rows cols signal off family names hwin]
  exact hdis

theorem noisy_generated_family_driverWins_pairwise_cells
    {α β : Type} (rows : List α) (cols : List β)
    (family : α → β → List Process2) (names : List String)
    (cell : α → β → List DrvWin)
    (hwin : ∀ i ∈ rows, ∀ j ∈ cols,
      driverWins names (family i j) = cell i j)
    (hdis : List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (rows.flatMap (fun i => cols.flatMap (fun j => cell i j)))) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (driverWins names (rows.flatMap (fun i => cols.flatMap (fun j => family i j)))) := by
  have hflat : driverWins names
      (rows.flatMap (fun i => cols.flatMap (fun j => family i j))) =
      rows.flatMap (fun i => cols.flatMap (fun j => cell i j)) := by
    rw [driverWins_flatMap]
    apply CombView.flatMap_congr'
    intro i hi
    rw [driverWins_flatMap]
    apply CombView.flatMap_congr'
    intro j hj
    exact hwin i hi j hj
  rw [hflat]
  exact hdis

theorem noisy_shifted_rect_family_windows_pairwise
    (N : Nat) (hN : 1 ≤ N) (signal : String) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      ((intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
        (intRange 0 (N : Int).toNat).map (fun j =>
          (signal, some (i.toNat * (N + 1) + j.toNat, 1))))) := by
  have hiN : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat, i.toNat < N := by
    intro i hi
    rw [mem_intRange] at hi
    have hi0 : 0 ≤ i := by omega
    have hcast : (i.toNat : Int) = i := Int.toNat_of_nonneg hi0
    rw [← hcast]
    omega
  have hjN : ∀ j ∈ intRange 0 (N : Int).toNat, j.toNat ≤ N := by
    intro j hj
    rw [mem_intRange] at hj
    have hj0 : 0 ≤ j := by omega
    have hcast : (j.toNat : Int) = j := Int.toNat_of_nonneg hj0
    rw [← hcast]
    omega
  rw [List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [List.pairwise_map]
    apply CombView.pairwise_intRange
    intro j k hj hjk hk
    have hj' : j ∈ intRange 0 (N : Int).toNat := by
      rw [mem_intRange]
      omega
    have hk' : k ∈ intRange 0 (N : Int).toNat := by
      rw [mem_intRange]
      omega
    exact noisy_row_major_rect_windows_disjoint
      (N := N) (i₁ := i.toNat) (j₁ := j.toNat)
      (i₂ := i.toNat) (j₂ := k.toNat)
      hN (hiN i hi) (hjN j hj') (hiN i hi) (hjN k hk') (by omega) signal
  · apply CombView.pairwise_intRange
    intro i k hi hik hk
    have hi' : i ∈ intRange 1 ((N : Int) - 1).toNat := by
      rw [mem_intRange]
      omega
    have hk' : k ∈ intRange 1 ((N : Int) - 1).toNat := by
      rw [mem_intRange]
      omega
    intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨l, hl, rfl⟩ := hy
    exact noisy_row_major_rect_windows_disjoint
      (N := N) (i₁ := i.toNat) (j₁ := j.toNat)
      (i₂ := k.toNat) (j₂ := l.toNat)
      hN (hiN i hi') (hjN j hj) (hiN k hk') (hjN l hl) (by omega) signal

theorem noisy_shifted_rect_plus_one_family_windows_pairwise
    (N : Nat) (hN : 1 ≤ N) (signal : String) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      ((intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
        (intRange 0 (N : Int).toNat).map (fun j =>
          (signal, some (i.toNat * (N + 1) + (j.toNat + 1), 1))))) := by
  have hiN : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat, i.toNat < N := by
    intro i hi
    rw [mem_intRange] at hi
    have hi0 : 0 ≤ i := by omega
    have hcast : (i.toNat : Int) = i := Int.toNat_of_nonneg hi0
    rw [← hcast]
    omega
  have hjN : ∀ j ∈ intRange 0 (N : Int).toNat, j.toNat + 1 ≤ N := by
    intro j hj
    rw [mem_intRange] at hj
    have hj0 : 0 ≤ j := by omega
    have hcast : (j.toNat : Int) = j := Int.toNat_of_nonneg hj0
    rw [← hcast]
    omega
  rw [List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [List.pairwise_map]
    apply CombView.pairwise_intRange
    intro j k hj hjk hk
    have hj' : j ∈ intRange 0 (N : Int).toNat := by
      rw [mem_intRange]
      omega
    have hk' : k ∈ intRange 0 (N : Int).toNat := by
      rw [mem_intRange]
      omega
    exact noisy_row_major_rect_windows_disjoint
      (N := N) (i₁ := i.toNat) (j₁ := j.toNat + 1)
      (i₂ := i.toNat) (j₂ := k.toNat + 1)
      hN (hiN i hi) (hjN j hj') (hiN i hi) (hjN k hk') (by omega) signal
  · apply CombView.pairwise_intRange
    intro i k hi hik hk
    have hi' : i ∈ intRange 1 ((N : Int) - 1).toNat := by
      rw [mem_intRange]
      omega
    have hk' : k ∈ intRange 1 ((N : Int) - 1).toNat := by
      rw [mem_intRange]
      omega
    intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨l, hl, rfl⟩ := hy
    exact noisy_row_major_rect_windows_disjoint
      (N := N) (i₁ := i.toNat) (j₁ := j.toNat + 1)
      (i₂ := k.toNat) (j₂ := l.toNat + 1)
      hN (hiN i hi') (hjN j hj) (hiN k hk') (hjN l hl) (by omega) signal

theorem noisy_row_three_signal_windows_pairwise
    (N : Nat) (hN : 1 ≤ N) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      ((intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
        (intRange 0 (N : Int).toNat).flatMap (fun j =>
          [("t", some (i.toNat * N + j.toNat, 1)),
           ("s", some (i.toNat * (N + 1) + j.toNat, 1)),
           ("c", some (i.toNat * (N + 1) + (j.toNat + 1), 1))]))) := by
  have hiN : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat, i.toNat < N := by
    intro i hi
    rw [mem_intRange] at hi
    have hi0 : 0 ≤ i := by omega
    have hcast : (i.toNat : Int) = i := Int.toNat_of_nonneg hi0
    rw [← hcast]
    omega
  have hjN : ∀ j ∈ intRange 0 (N : Int).toNat, j.toNat < N := by
    intro j hj
    rw [mem_intRange] at hj
    have hj0 : 0 ≤ j := by omega
    have hcast : (j.toNat : Int) = j := Int.toNat_of_nonneg hj0
    rw [← hcast]
    omega
  rw [List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [List.pairwise_flatMap]
    refine ⟨?_, ?_⟩
    · intro j hj
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact noisy_different_signal_windows_disjoint (by decide)
        · exact noisy_different_signal_windows_disjoint (by decide)
      · refine List.pairwise_cons.mpr ⟨?_, by simp⟩
        intro y hy
        simp only [List.mem_singleton] at hy
        subst y
        exact noisy_different_signal_windows_disjoint (by decide)
    · apply CombView.pairwise_intRange
      intro j k hj hjk hk
      have hj' : j ∈ intRange 0 (N : Int).toNat := by
        rw [mem_intRange]
        omega
      have hk' : k ∈ intRange 0 (N : Int).toNat := by
        rw [mem_intRange]
        omega
      intro x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact noisy_row_major_cell_windows_disjoint
          (N := N) (i₁ := i.toNat) (j₁ := j.toNat)
          (i₂ := i.toNat) (j₂ := k.toNat)
          hN (hiN i hi) (hjN j hj') (hiN i hi) (hjN k hk') (by omega)
      · exact noisy_different_signal_windows_disjoint (by decide)
      · exact noisy_different_signal_windows_disjoint (by decide)
      · exact noisy_different_signal_windows_disjoint (by decide)
      · exact noisy_row_major_rect_windows_disjoint
          (N := N) (i₁ := i.toNat) (j₁ := j.toNat)
          (i₂ := i.toNat) (j₂ := k.toNat)
          hN (hiN i hi) (by omega) (hiN i hi) (by omega) (by omega) "s"
      · exact noisy_different_signal_windows_disjoint (by decide)
      · exact noisy_different_signal_windows_disjoint (by decide)
      · exact noisy_different_signal_windows_disjoint (by decide)
      · exact noisy_row_major_rect_windows_disjoint
          (N := N) (i₁ := i.toNat) (j₁ := j.toNat + 1)
          (i₂ := i.toNat) (j₂ := k.toNat + 1)
          hN (hiN i hi) (by omega) (hiN i hi) (by omega) (by omega) "c"
  · apply CombView.pairwise_intRange
    intro i k hi hik hk
    have hi' : i ∈ intRange 1 ((N : Int) - 1).toNat := by
      rw [mem_intRange]
      omega
    have hk' : k ∈ intRange 1 ((N : Int) - 1).toNat := by
      rw [mem_intRange]
      omega
    intro x hx y hy
    simp only [List.mem_flatMap] at hx hy
    obtain ⟨j, hj, hx⟩ := hx
    obtain ⟨l, hl, hy⟩ := hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact noisy_row_major_cell_windows_disjoint
        (N := N) (i₁ := i.toNat) (j₁ := j.toNat)
        (i₂ := k.toNat) (j₂ := l.toNat)
        hN (hiN i hi') (hjN j hj) (hiN k hk') (hjN l hl) (by omega)
    · exact noisy_different_signal_windows_disjoint (by decide)
    · exact noisy_different_signal_windows_disjoint (by decide)
    · exact noisy_different_signal_windows_disjoint (by decide)
    · exact noisy_row_major_rect_windows_disjoint
        (N := N) (i₁ := i.toNat) (j₁ := j.toNat)
        (i₂ := k.toNat) (j₂ := l.toNat)
        hN (hiN i hi') (Nat.le_of_lt (hjN j hj)) (hiN k hk')
          (Nat.le_of_lt (hjN l hl)) (by omega) "s"
    · exact noisy_different_signal_windows_disjoint (by decide)
    · exact noisy_different_signal_windows_disjoint (by decide)
    · exact noisy_different_signal_windows_disjoint (by decide)
    · exact noisy_row_major_rect_windows_disjoint
        (N := N) (i₁ := i.toNat) (j₁ := j.toNat + 1)
        (i₂ := k.toNat) (j₂ := l.toNat + 1)
        hN (hiN i hi') (Nat.succ_le_of_lt (hjN j hj)) (hiN k hk')
          (Nat.succ_le_of_lt (hjN l hl)) (by omega) "c"

theorem noisy_row_child_generated_driverWins_pairwise
    (N : Nat) (hN : 1 ≤ N) (names : List String)
    (family : Int → Int → List Process2)
    (hwin : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat,
      ∀ j ∈ intRange 0 (N : Int).toNat,
        driverWins names (family i j) =
          [("t", some (i.toNat * N + j.toNat, 1)),
           ("s", some (i.toNat * (N + 1) + j.toNat, 1)),
           ("c", some (i.toNat * (N + 1) + (j.toNat + 1), 1))]) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (driverWins names
        ((intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
          (intRange 0 (N : Int).toNat).flatMap (fun j => family i j)))) := by
  apply noisy_generated_family_driverWins_pairwise_cells
    (rows := intRange 1 ((N : Int) - 1).toNat)
    (cols := intRange 0 (N : Int).toNat)
    (family := family) (names := names)
    (cell := fun i j =>
      [("t", some (i.toNat * N + j.toNat, 1)),
       ("s", some (i.toNat * (N + 1) + j.toNat, 1)),
       ("c", some (i.toNat * (N + 1) + (j.toNat + 1), 1))])
  · exact hwin
  · simpa using noisy_row_three_signal_windows_pairwise N hN

def noisyRowTPrefix (i j : Int) : String :=
  "g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_t."

def noisyRowSPrefix (i j : Int) : String :=
  "g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_s."

def noisyRowCPrefix (i j : Int) : String :=
  "g_row[" ++ toString i ++ "].g_bit[" ++ toString j ++ "].u_c."

def noisyRowChildCellProcs
    (env : IEnv) (elems : List (String × Nat)) (i j : Int) : List Process2 :=
  (flattenInst (env.bindVal "i" i |>.bindVal "j" j) elems
      (noisyRowTPrefix i j) xorInst xorDesign).2 ++
    (flattenInst (env.bindVal "i" i |>.bindVal "j" j) elems
      (noisyRowSPrefix i j) xorSInst xorDesign).2 ++
    (flattenInst (env.bindVal "i" i |>.bindVal "j" j) elems
      (noisyRowCPrefix i j) majInst majDesign).2

theorem noisy_row_child_cell_driverWins
    {N i j : Nat} (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (env : IEnv) (elems : List (String × Nat)) (names : List String)
    (hT : names.contains (noisyRowTPrefix i j ++ "a") = false ∧
      names.contains (noisyRowTPrefix i j ++ "b") = false ∧
      names.contains (noisyRowTPrefix i j ++ "f") = false ∧
      names.contains (noisyRowTPrefix i j ++ "y") = false)
    (hS : names.contains (noisyRowSPrefix i j ++ "a") = false ∧
      names.contains (noisyRowSPrefix i j ++ "b") = false ∧
      names.contains (noisyRowSPrefix i j ++ "f") = false ∧
      names.contains (noisyRowSPrefix i j ++ "y") = false)
    (hC : names.contains (noisyRowCPrefix i j ++ "a") = false ∧
      names.contains (noisyRowCPrefix i j ++ "b") = false ∧
      names.contains (noisyRowCPrefix i j ++ "c") = false ∧
      names.contains (noisyRowCPrefix i j ++ "f") = false ∧
      names.contains (noisyRowCPrefix i j ++ "y") = false)
    (ht : names.contains "t" = true)
    (hs : names.contains "s" = true)
    (hc : names.contains "c" = true)
    (hdT : env.dims.lookup "t" = some [((N : Int) - 1, 0), ((N : Int) - 1, 0)])
    (hdS : env.dims.lookup "s" = some [((N : Int) - 1, 0), ((N : Int), 0)])
    (hdC : env.dims.lookup "c" = some [((N : Int) - 1, 0), ((N : Int), 0)]) :
    driverWins names (noisyRowChildCellProcs env elems i j) =
      [("t", some (i * N + j, 1)),
       ("s", some (i * (N + 1) + j, 1)),
       ("c", some (i * (N + 1) + (j + 1), 1))] := by
  rcases hT with ⟨hTa, hTb, hTf, hTy⟩
  rcases hS with ⟨hSa, hSb, hSf, hSy⟩
  rcases hC with ⟨hCa, hCb, hCc, hCf, hCy⟩
  have htw := noisy_xor_flatten_driverWins_at
    (N := N) (i := i) (j := j) hN hi hj env elems
    (noisyRowTPrefix i j) names hTa hTb hTf hTy ht hdT
  have hsw := noisy_xorS_flatten_driverWins_at
    (N := N) (i := i) (j := j) hN hi (Nat.le_of_lt hj) env elems
    (noisyRowSPrefix i j) names hSa hSb hSf hSy hs hdS
  have hcw := noisy_maj_flatten_driverWins_at
    (N := N) (i := i) (j := j) hN hi hj env elems
    (noisyRowCPrefix i j) names hCa hCb hCc hCf hCy hc hdC
  unfold noisyRowChildCellProcs
  rw [driverWins_append, driverWins_append, htw, hsw, hcw]
  simp

theorem noisy_row_child_paths_processes
    (env : IEnv) (elems : List (String × Nat)) (N i : Int) :
    (noisyRowChildPaths N i).flatMap
        (fun p => (noisyFullFamilySegment env elems p).2) =
      (intRange 0 N.toNat).flatMap (fun j =>
        noisyRowChildCellProcs env elems i j) := by
  unfold noisyRowChildPaths
  rw [List.flatMap_assoc]
  apply CombView.flatMap_congr'
  intro j hj
  have hta : xorInst.name ≠ andInst.name := by decide
  have hsa : xorSInst.name ≠ andInst.name := by decide
  have hst : xorSInst.name ≠ xorInst.name := by decide
  have hma : majInst.name ≠ andInst.name := by decide
  have hmt : majInst.name ≠ xorInst.name := by decide
  have hms : majInst.name ≠ xorSInst.name := by decide
  simp [noisyFullFamilySegment, noisyTopNodeSegment,
    noisyTopGeneratedPairSegment, noisyRowChildCellProcs,
    noisyRowTPrefix, noisyRowSPrefix, noisyRowCPrefix, hta, hsa, hst,
    hma, hmt, hms]

theorem noisy_row_child_generated_driverWins_pairwise_paths
    (N : Nat) (hN : 1 ≤ N) (env : IEnv) (elems : List (String × Nat))
    (names : List String)
    (cell : Int → Int → List DrvWin)
    (hwin : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat,
      ∀ j ∈ intRange 0 (N : Int).toNat,
        driverWins names (noisyRowChildCellProcs env elems i j) = cell i j)
    (hdis : List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      ((intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
        (intRange 0 (N : Int).toNat).flatMap (fun j => cell i j)))) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (driverWins names
        ((intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
          (noisyRowChildPaths N i).flatMap
            (fun p => (noisyFullFamilySegment env elems p).2)))) := by
  have hrow : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat,
      driverWins names
        ((noisyRowChildPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).2)) =
        (intRange 0 (N : Int).toNat).flatMap (fun j => cell i j) := by
    intro i hi
    have hpaths := noisy_row_child_paths_processes env elems N i
    rw [hpaths]
    rw [driverWins_flatMap]
    apply CombView.flatMap_congr'
    intro j hj
    exact hwin i hi j hj
  rw [driverWins_flatMap]
  have hrows : (intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
      driverWins names
        ((noisyRowChildPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).2))) =
      (intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
        (intRange 0 (N : Int).toNat).flatMap (fun j => cell i j)) := by
    apply CombView.flatMap_congr'
    intro i hi
    exact hrow i hi
  rw [hrows]
  exact hdis

theorem noisy_row_child_generated_driverWins_paths
    (N : Nat) (hN : 1 ≤ N) (env : IEnv) (elems : List (String × Nat))
    (names : List String)
    (cell : Int → Int → List DrvWin)
    (hwin : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat,
      ∀ j ∈ intRange 0 (N : Int).toNat,
        driverWins names (noisyRowChildCellProcs env elems i j) = cell i j) :
    driverWins names
        ((intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
          (noisyRowChildPaths N i).flatMap
            (fun p => (noisyFullFamilySegment env elems p).2))) =
      (intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
        (intRange 0 (N : Int).toNat).flatMap (fun j => cell i j)) := by
  have hrow : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat,
      driverWins names
        ((noisyRowChildPaths N i).flatMap
          (fun p => (noisyFullFamilySegment env elems p).2)) =
        (intRange 0 (N : Int).toNat).flatMap (fun j => cell i j) := by
    intro i hi
    rw [noisy_row_child_paths_processes env elems N i]
    rw [driverWins_flatMap]
    apply CombView.flatMap_congr'
    intro j hj
    exact hwin i hi j hj
  rw [driverWins_flatMap]
  apply CombView.flatMap_congr'
  intro i hi
  exact hrow i hi

theorem noisy_row_family_driverWins
    {α : Type} (rows : List α) (names : List String)
    (left right : α → Process2) (children : α → List Process2)
    (leftWin rightWin : α → DrvWin) (childWins : α → List DrvWin)
    (hleft : ∀ i ∈ rows, driverWins names [left i] = [leftWin i])
    (hright : ∀ i ∈ rows, driverWins names [right i] = [rightWin i])
    (hchildren : ∀ i ∈ rows, driverWins names (children i) = childWins i) :
    driverWins names
        (rows.flatMap (fun i => left i :: children i ++ [right i])) =
      rows.flatMap (fun i => [leftWin i] ++ childWins i ++ [rightWin i]) := by
  rw [driverWins_flatMap]
  apply CombView.flatMap_congr'
  intro i hi
  rw [show left i :: children i ++ [right i] = [left i] ++ children i ++ [right i] by simp]
  rw [driverWins_append, driverWins_append, hleft i hi, hchildren i hi, hright i hi]

theorem noisy_row_paths_driverWins
    (N : Nat) (env : IEnv) (elems : List (String × Nat))
    (names : List String)
    (cell : Int → Int → List DrvWin)
    (hleft : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat,
      driverWins names [instProcess2 (env.bindVal "i" i) elems rowLeft] =
        [("c", some (i.toNat * (N + 1), 1))])
    (hright : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat,
      driverWins names [instProcess2 (env.bindVal "i" i) elems rowRight] =
        [("s", some (i.toNat * (N + 1) + N, 1))])
    (hchildren : ∀ i ∈ intRange 1 ((N : Int) - 1).toNat,
      driverWins names
          ((noisyRowChildPaths N i).flatMap
            (fun p => (noisyFullFamilySegment env elems p).2)) =
        (intRange 0 (N : Int).toNat).flatMap (fun j => cell i j)) :
    driverWins names
        ((intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
          (noisyRowPaths N i).flatMap
            (fun p => (noisyFullFamilySegment env elems p).2))) =
      (intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
        [("c", some (i.toNat * (N + 1), 1))] ++
          (intRange 0 (N : Int).toNat).flatMap (fun j => cell i j) ++
          [("s", some (i.toNat * (N + 1) + N, 1))]) := by
  have hshape :
      (intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
          (noisyRowPaths N i).flatMap
            (fun p => (noisyFullFamilySegment env elems p).2)) =
        (intRange 1 ((N : Int) - 1).toNat).flatMap (fun i =>
          instProcess2 (env.bindVal "i" i) elems rowLeft ::
            (noisyRowChildPaths N i).flatMap
              (fun p => (noisyFullFamilySegment env elems p).2) ++
            [instProcess2 (env.bindVal "i" i) elems rowRight]) := by
    apply CombView.flatMap_congr'
    intro i hi
    simp only [noisyRowPaths, List.flatMap_cons, List.flatMap_append,
      List.flatMap_singleton]
    rw [noisy_row_child_paths_processes env elems N i]
    rfl
  rw [hshape]
  apply noisy_row_family_driverWins
    (rows := intRange 1 ((N : Int) - 1).toNat)
    (names := names)
    (left := fun i => instProcess2 (env.bindVal "i" i) elems rowLeft)
    (right := fun i => instProcess2 (env.bindVal "i" i) elems rowRight)
    (children := fun i =>
      (noisyRowChildPaths N i).flatMap
        (fun p => (noisyFullFamilySegment env elems p).2))
    (leftWin := fun i => ("c", some (i.toNat * (N + 1), 1)))
    (rightWin := fun i => ("s", some (i.toNat * (N + 1) + N, 1)))
    (childWins := fun i =>
      (intRange 0 (N : Int).toNat).flatMap (fun j => cell i j))
  · exact hleft
  · exact hright
  · exact hchildren

theorem noisy_row_left_driverWins_at
    {N i : Nat} (hN : 1 ≤ N) (hi : i < N)
    (env : IEnv) (elems : List (String × Nat)) (names : List String)
    (hc : names.contains "c" = true)
    (hd : env.dims.lookup "c" = some [((N : Int) - 1, 0), ((N : Int), 0)]) :
    driverWins names [instProcess2 (env.bindVal "i" i) elems rowLeft] =
      [("c", some (i * (N + 1), 1))] := by
  have hq := noisy_arrayElemTarget_rect_of_range
    (env := env.bindVal "i" i) (elems := elems) (n := "c")
    (N := N) (i := i) (j := 0)
    (ie := .genvarRef "i") (je := .int 0) hN hi (by omega) hd
    (evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup]))
    (evalInt_int 0)
  have hcm : "c" ∈ names := List.contains_iff_mem.mp hc
  simp [instProcess2, rowLeft, driverWins, Process2.drvWins, Lhs2.drvWins,
    hq, hcm]

theorem noisy_row_right_driverWins_at
    {N i : Nat} (hN : 1 ≤ N) (hi : i < N)
    (env : IEnv) (elems : List (String × Nat)) (names : List String)
    (hs : names.contains "s" = true)
    (hNval : evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok N)
    (hd : env.dims.lookup "s" = some [((N : Int) - 1, 0), ((N : Int), 0)]) :
    driverWins names [instProcess2 (env.bindVal "i" i) elems rowRight] =
      [("s", some (i * (N + 1) + N, 1))] := by
  have hq := noisy_arrayElemTarget_rect_of_range
    (env := env.bindVal "i" i) (elems := elems) (n := "s")
    (N := N) (i := i) (j := N)
    (ie := .genvarRef "i") (je := .paramRef "N" none) hN hi (by omega) hd
    (evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup]))
    (by exact hNval)
  have hsm : "s" ∈ names := List.contains_iff_mem.mp hs
  simp [instProcess2, rowRight, driverWins, Process2.drvWins, Lhs2.drvWins,
    hq, hsm]

theorem noisy_row_boundary_family_driverWins_pairwise
    (names : List String) (left right : Process2) (children : List Process2)
    (leftWin rightWin : DrvWin) (childWins : List DrvWin)
    (hleft : driverWins names [left] = [leftWin])
    (hright : driverWins names [right] = [rightWin])
    (hchildren : driverWins names children = childWins)
    (hdis : List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (leftWin :: childWins ++ [rightWin])) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      (driverWins names (left :: children ++ [right])) := by
  have hwhole : driverWins names (left :: children ++ [right]) =
      leftWin :: childWins ++ [rightWin] := by
    rw [show left :: children ++ [right] = [left] ++ children ++ [right] by simp]
    rw [driverWins_append, driverWins_append, hleft, hchildren, hright]
    simp [List.append_assoc]
  rw [hwhole]
  exact hdis

theorem noisy_pairwise_append_driverWins
    (left right : List DrvWin)
    (hleft : List.Pairwise (fun a b : DrvWin => a.overlaps b = false) left)
    (hright : List.Pairwise (fun a b : DrvWin => a.overlaps b = false) right)
    (hcross : ∀ a ∈ left, ∀ b ∈ right, a.overlaps b = false) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false) (left ++ right) := by
  rw [List.pairwise_append]
  exact ⟨hleft, hright, hcross⟩

theorem noisy_out_driverWins_at_of_target
    (env : IEnv) (elems : List (String × Nat)) (i : Int)
    (names : List String)
    (hp : names.contains "p" = true)
    (hq : instLhs2 (env.bindVal "i" i) elems
      (.bitSel "p" (.genvarRef "i")) = .ok (.slice "p" i.toNat 1, 1)) :
    driverWins names [instProcess2 (env.bindVal "i" i) elems outProc] =
      [("p", some (i.toNat, 1))] := by
  have hpm : "p" ∈ names := List.contains_iff_mem.mp hp
  simp [instProcess2, outProc, driverWins, Process2.drvWins, Lhs2.drvWins,
    hq, hpm]

theorem noisy_out_target_of_elem
    (env : IEnv) (elems : List (String × Nat)) (i : Int)
    (helem : elems.lookup "p" = some 1)
    (hinonneg : 0 ≤ i)
    (hi : (env.bindVal "i" i).vals.lookup "i" = some i) :
    instLhs2 (env.bindVal "i" i) elems
      (.bitSel "p" (.genvarRef "i")) = .ok (.slice "p" i.toNat 1, 1) := by
  simp [instLhs2, instLhsLeaf2, instIndex2, helem, evalInt,
    IEnv.bindVal, List.lookup, hi, hinonneg]

theorem noisy_output_family_windows_pairwise (N : Nat) :
    List.Pairwise (fun a b : DrvWin => a.overlaps b = false)
      ((List.range N).map (fun i => ("p", some (i, 1)))) := by
  rw [List.pairwise_map]
  apply List.pairwise_lt_range.imp
  intro i k hik
  simp [DrvWin.overlaps]
  omega

theorem noisy_out_target_actual (N i : Int)
    (hCanon : canonInt 32 true N = N)
    (hi : 0 ≤ i) :
    instLhs2 (((noisyEnv N).withDecls (noisyDeclsRaw N)).bindVal "i" i)
      (noisyElems N) (.bitSel "p" (.genvarRef "i")) =
      Except.ok (.slice "p" i.toNat 1, 1) := by
  apply noisy_out_target_of_elem
  · rfl
  · exact hi
  · rw [IEnv.bindVal_vals, IEnv.withDecls_vals]
    rfl

theorem noisy_static_driverWins (N : Nat)
    (env : IEnv) (decls : List Decl) (elems : List (String × Nat))
    (hS : arrayElemTarget (env.withDecls decls) "s" [.int 0] =
      .ok (.slice "s" 0 (N + 1), N + 1))
    (hC : arrayElemTarget (env.withDecls decls) "c" [.int 0] =
      .ok (.slice "c" 0 (N + 1), N + 1))
    (hT : arrayElemTarget (env.withDecls decls) "t" [.int 0] =
      .ok (.slice "t" 0 N, N))
    (hP : arrayPartTarget (env.withDecls decls) "p" [] PartMode.range
        (.binary (SymBinOp.m0 BinOp.sub) (.binary SymBinOp.mul (.int 2) (.paramRef "N" none)) (.int 1))
        (.paramRef "N" none) =
      .ok (.slice "p" N N, N)) :
    driverWins ["a", "b", "f", "p", "pp", "s", "c", "t"]
      (noisyStaticProcs env decls elems) =
      [("s", some (0, N + 1)), ("c", some (0, N + 1)),
       ("t", some (0, N)), ("p", some (N, N))] := by
  simp [noisyStaticProcs, noisyMul.pdesign, driverWins, Process2.drvWins,
    Lhs2.drvWins, instProcess2, instLhs2, instLhsLeaf2, instIndex2,
    hS, hC, hT, hP]

end Examples.«system-verilog».sem2.noisy_mul_generate
