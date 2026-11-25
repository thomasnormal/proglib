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

theorem noisy_generated_row_nodes :
    CombHier.generatedNodes noisyMul.plib [] [rowGen] =
      .ok [
        .process [rowLoop] rowLeft,
        .child (CombHier.GeneratedChildRef.mk rowInnerLoops xorInst xorDef),
        .child (CombHier.GeneratedChildRef.mk rowInnerLoops xorSInst xorDef),
        .child (CombHier.GeneratedChildRef.mk rowInnerLoops majInst majDef),
        .process [rowLoop] rowRight] := by
  rw [noisy_row_shape_test, noisy_row_body_shape]
  rw [noisy_row_inner_shape]
  simp [rowLoop, rowInnerLoops, CombHier.generatedNodes,
    noisyMul.plib, andDef, xorDef, majDef, xorInst, xorSInst, majInst]

theorem noisy_generated_top_nodes :
    CombHier.generatedNodes noisyMul.plib [] noisyMul.pdesign.generates =
      .ok [
        .child (CombHier.GeneratedChildRef.mk ppLoops andInst andDef),
        .process [rowLoop] rowLeft,
        .child (CombHier.GeneratedChildRef.mk rowInnerLoops xorInst xorDef),
        .child (CombHier.GeneratedChildRef.mk rowInnerLoops xorSInst xorDef),
        .child (CombHier.GeneratedChildRef.mk rowInnerLoops majInst majDef),
        .process [rowLoop] rowRight,
        .process [outLoop] outProc] := by
  rw [noisy_top_generates_shape]
  rw [show ppGen = .genFor (some "g_pp") "i" (.int 0)
      (.binary .slt (.genvarRef "i") (.paramRef "N" none))
      (.unary .inc (.genvarRef "i")) (some 4)
      [.genFor (some "g_pp_j") "j" (.int 0)
        (.binary .slt (.genvarRef "j") (.paramRef "N" none))
        (.unary .inc (.genvarRef "j")) (some 4) [.inst andInst]] by rfl]
  rw [noisy_row_shape_test, noisy_row_body_shape, noisy_row_inner_shape,
    noisy_out_body_shape]
  simp [ppLoops, rowLoop, outLoop, CombHier.generatedNodes,
    noisyMul.plib, andDef, xorDef, majDef, xorInst, xorSInst, majInst]

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

end Examples.«system-verilog».sem2.noisy_mul_generate
