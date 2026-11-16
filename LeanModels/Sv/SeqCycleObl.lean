import LeanModels.Sv.SeqCycle

/-!
# The obligations of the clocked profile, and the theorems that use them (`LeanModels.Sv.Kernel`)

**Status: derived from the ordinary E route** (part of the clocked tactics' theory, `SeqCycle.lean`).

* `SeqPorts`: the interface of a family member.
* `seqOblB`: the obligations, decided: one driver per signal (a memory counts as one signal: one writer per memory),
  the continuous assigns in topological source order on what the route evaluates (`topoC`: a compiled expression's
  identifiers, or for an assign that reads a memory the names `evalV` reads, `readsV`), no process writing an input or
  the clock, no process reading the clock, an asynchronous reset that is an input port, the edge order irrelevant, no
  unconverted expression. `SeqDesign`: the structure judgment (instantiation, profile, obligations).
* The theorems that USE the obligations: `settleV_idem` (one settle pass is the fixpoint: no continuous assignment is
  out of date when a slot closes), `slotV_eq_slot1V` (the slot is one pass before the edge and one after),
  `edgesV_order` (every order of the edge processes commits to the same views: rule 4).
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## The interface and the obligations -/

/-- The input ports of a canonical-E design with their declared widths, in declaration order. -/
def CoreMemDesign.inputPorts (E : CoreMemDesign) : List (String × Nat) :=
  E.scalar.decls.toList.filterMap fun dc => if dc.isInput then some (dc.name, dc.width) else none

/-- The output ports of a canonical-E design with their declared widths, in declaration order. -/
def CoreMemDesign.outputPorts (E : CoreMemDesign) : List (String × Nat) :=
  E.scalar.decls.toList.filterMap fun dc => if dc.isOutput then some (dc.name, dc.width) else none

/-- **The interface of a family member**: it instantiates, with these ports. -/
def SeqPorts (r : Res CoreMemDesign) (ins outs : List (String × Nat)) : Prop :=
  ∃ E, r = .ok E ∧ E.inputPorts = ins ∧ E.outputPorts = outs

mutual

/-- The signal names an expression reads (identifiers and select bases). -/
def _root_.LeanModels.Sv.PExpr.sigNames : PExpr → List String
  | .ident n => [n]
  | .arrayElem n is => n :: PExpr.sigNamesList is
  | .arrayPart n is _ a b => n :: (PExpr.sigNamesList is ++ PExpr.sigNames a ++ PExpr.sigNames b)
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a | .sysCall _ a | .reduce _ a | .cast _ a =>
      PExpr.sigNames a
  | .binary _ a b | .bitSel a b | .repl a b => PExpr.sigNames a ++ PExpr.sigNames b
  | .ternary c a b | .partSel c a b => PExpr.sigNames c ++ PExpr.sigNames a ++ PExpr.sigNames b
  | .concat xs | .functionCall _ xs => PExpr.sigNamesList xs
  | .lit _ | .paramRef _ _ | .genvarRef _ | .enumRef _ _ _ | .int _ | .fill _ | .unsupported _ _ => []

/-- `sigNames` of a list. -/
def _root_.LeanModels.Sv.PExpr.sigNamesList : List PExpr → List String
  | [] => []
  | x :: xs => PExpr.sigNames x ++ PExpr.sigNamesList xs

end

mutual

/-- The signal a write target writes (its base name; every leaf of a concatenation). -/
def _root_.LeanModels.Sv.PLhs.baseNames : PLhs → List String
  | .ident n => [n]
  | .bitSel n _ => [n]
  | .partSel n _ _ => [n]
  | .arrayElem n _ => [n]
  | .arrayPart n _ _ _ _ => [n]
  | .concat parts => PLhs.baseNamesList parts

/-- `baseNames` of a list. -/
def _root_.LeanModels.Sv.PLhs.baseNamesList : List PLhs → List String
  | [] => []
  | p :: ps => PLhs.baseNames p ++ PLhs.baseNamesList ps

end

mutual

/-- The names a target's index expressions read. -/
def _root_.LeanModels.Sv.PLhs.indexNames : PLhs → List String
  | .ident _ => []
  | .bitSel _ i => PExpr.sigNames i
  | .partSel _ a b => PExpr.sigNames a ++ PExpr.sigNames b
  | .arrayElem _ is => PExpr.sigNamesList is
  | .arrayPart _ is _ a b => PExpr.sigNamesList is ++ PExpr.sigNames a ++ PExpr.sigNames b
  | .concat parts => PLhs.indexNamesList parts

/-- `indexNames` of a list. -/
def _root_.LeanModels.Sv.PLhs.indexNamesList : List PLhs → List String
  | [] => []
  | p :: ps => PLhs.indexNames p ++ PLhs.indexNamesList ps

end

mutual

/-- The signals an edge body writes, blocking or nonblocking (base names). -/
def _root_.LeanModels.Sv.PStmt.writes : PStmt → List String
  | .nbaAssign t _ => [t]
  | .blockingAssign t _ => [t]
  | .nbaAssignL t _ => PLhs.baseNames t
  | .blockingAssignL t _ => PLhs.baseNames t
  | .ifStmt _ y n => PStmt.writes y ++ PStmt.optWrites n
  | .block body => PStmt.listWrites body
  | .caseStmt _ items d _ _ => PStmt.itemsWrites items ++ PStmt.optWrites d
  | _ => []
termination_by structural s => s

/-- `writes` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optWrites : Option PStmt → List String
  | none => []
  | some s => PStmt.writes s
termination_by structural o => o

/-- `writes` of a list. -/
def _root_.LeanModels.Sv.PStmt.listWrites : List PStmt → List String
  | [] => []
  | s :: ss => PStmt.writes s ++ PStmt.listWrites ss
termination_by structural xs => xs

/-- `writes` of the arms of a `case`. -/
def _root_.LeanModels.Sv.PStmt.itemsWrites : List (List PExpr × PStmt) → List String
  | [] => []
  | (_, b) :: rest => PStmt.writes b ++ PStmt.itemsWrites rest
termination_by structural xs => xs

end

mutual

/-- Whether an edge body has a blocking write. -/
def _root_.LeanModels.Sv.PStmt.hasBlocking : PStmt → Bool
  | .blockingAssign _ _ => true
  | .blockingAssignL _ _ => true
  | .ifStmt _ y n => PStmt.hasBlocking y || PStmt.optHasBlocking n
  | .block body => PStmt.listHasBlocking body
  | .caseStmt _ items d _ _ => PStmt.itemsHasBlocking items || PStmt.optHasBlocking d
  | _ => false
termination_by structural s => s

/-- `hasBlocking` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optHasBlocking : Option PStmt → Bool
  | none => false
  | some s => PStmt.hasBlocking s
termination_by structural o => o

/-- `hasBlocking` of a list. -/
def _root_.LeanModels.Sv.PStmt.listHasBlocking : List PStmt → Bool
  | [] => false
  | s :: ss => PStmt.hasBlocking s || PStmt.listHasBlocking ss
termination_by structural xs => xs

/-- `hasBlocking` of the arms of a `case`. -/
def _root_.LeanModels.Sv.PStmt.itemsHasBlocking : List (List PExpr × PStmt) → Bool
  | [] => false
  | (_, b) :: rest => PStmt.hasBlocking b || PStmt.itemsHasBlocking rest
termination_by structural xs => xs

end

mutual

/-- The names a body reads: conditions, case subjects and patterns, right-hand sides, target indices. -/
def _root_.LeanModels.Sv.PStmt.readNames : PStmt → List String
  | .nbaAssign _ e | .blockingAssign _ e => PExpr.sigNames e
  | .nbaAssignL t e | .blockingAssignL t e => PLhs.indexNames t ++ PExpr.sigNames e
  | .ifStmt c y n => PExpr.sigNames c ++ PStmt.readNames y ++ PStmt.optReadNames n
  | .block body => PStmt.listReadNames body
  | .caseStmt s items d _ _ => PExpr.sigNames s ++ PStmt.itemsReadNames items ++ PStmt.optReadNames d
  | _ => []
termination_by structural s => s

/-- `readNames` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optReadNames : Option PStmt → List String
  | none => []
  | some s => PStmt.readNames s
termination_by structural o => o

/-- `readNames` of a list. -/
def _root_.LeanModels.Sv.PStmt.listReadNames : List PStmt → List String
  | [] => []
  | s :: ss => PStmt.readNames s ++ PStmt.listReadNames ss
termination_by structural xs => xs

/-- `readNames` of the arms of a `case`. -/
def _root_.LeanModels.Sv.PStmt.itemsReadNames : List (List PExpr × PStmt) → List String
  | [] => []
  | (ps, b) :: rest => PExpr.sigNamesList ps ++ PStmt.readNames b ++ PStmt.itemsReadNames rest
termination_by structural xs => xs

end

mutual

/-- The kinds of the nodes of an expression that ingestion kept as `unsupported` (not converted). -/
def _root_.LeanModels.Sv.PExpr.unconverted : PExpr → List String
  | .unsupported k _ => [k]
  | .arrayElem _ is => PExpr.unconvertedList is
  | .arrayPart _ is _ a b => PExpr.unconvertedList is ++ PExpr.unconverted a ++ PExpr.unconverted b
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a | .sysCall _ a | .reduce _ a | .cast _ a =>
      PExpr.unconverted a
  | .binary _ a b | .bitSel a b | .repl a b => PExpr.unconverted a ++ PExpr.unconverted b
  | .ternary c a b | .partSel c a b => PExpr.unconverted c ++ PExpr.unconverted a ++ PExpr.unconverted b
  | .concat xs | .functionCall _ xs => PExpr.unconvertedList xs
  | .ident _ | .lit _ | .paramRef _ _ | .genvarRef _ | .enumRef _ _ _ | .int _ | .fill _ => []

/-- `unconverted` of a list. -/
def _root_.LeanModels.Sv.PExpr.unconvertedList : List PExpr → List String
  | [] => []
  | x :: xs => PExpr.unconverted x ++ PExpr.unconvertedList xs

end

mutual

/-- The unconverted expression nodes of a body (conditions, case subjects and patterns, right-hand sides). -/
def _root_.LeanModels.Sv.PStmt.unconverted : PStmt → List String
  | .nbaAssign _ e | .blockingAssign _ e | .nbaAssignL _ e | .blockingAssignL _ e => PExpr.unconverted e
  | .ifStmt c y n => PExpr.unconverted c ++ PStmt.unconverted y ++ PStmt.optUnconverted n
  | .block body => PStmt.listUnconverted body
  | .caseStmt s items d _ _ => PExpr.unconverted s ++ PStmt.itemsUnconverted items ++ PStmt.optUnconverted d
  | _ => []
termination_by structural s => s

/-- `unconverted` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optUnconverted : Option PStmt → List String
  | none => []
  | some s => PStmt.unconverted s
termination_by structural o => o

/-- `unconverted` of a list. -/
def _root_.LeanModels.Sv.PStmt.listUnconverted : List PStmt → List String
  | [] => []
  | s :: ss => PStmt.unconverted s ++ PStmt.listUnconverted ss
termination_by structural xs => xs

/-- `unconverted` of the arms of a `case`. -/
def _root_.LeanModels.Sv.PStmt.itemsUnconverted : List (List PExpr × PStmt) → List String
  | [] => []
  | (ps, b) :: rest => PExpr.unconvertedList ps ++ PStmt.unconverted b ++ PStmt.itemsUnconverted rest
termination_by structural xs => xs

end

/-- The unconverted expression nodes of a process. -/
def CoreMemProc.unconverted : CoreMemProc → List String
  | .assign _ v => PExpr.unconverted v
  | .edge f => f.body.unconverted
  | _ => []

/-- The names a process drives. -/
def CoreMemProc.targets : CoreMemProc → List String
  | .assign (.ident n) _ => [n]
  | .edge f => f.body.writes.eraseDups
  | _ => []

/-- The names a process reads. -/
def CoreMemProc.reads : CoreMemProc → List String
  | .assign _ v => PExpr.sigNames v
  | .edge f => f.body.readNames
  | _ => []

/-- The asynchronous reset of an edge process, when it has one. -/
def CoreMemProc.reset? : CoreMemProc → Option String
  | .edge f => f.reset
  | _ => none

/-- Whether a process is an edge process with a blocking write. -/
def CoreMemProc.blocking : CoreMemProc → Bool
  | .edge f => f.body.hasBlocking
  | _ => false

/-- Whether a process is an edge process. -/
def CoreMemProc.isEdge : CoreMemProc → Bool
  | .edge _ => true
  | _ => false

/-- The targets of the continuous assigns of a list. -/
def assignTargets (ps : List CoreMemProc) : List String :=
  ps.flatMap fun p => match p with
    | .assign (.ident n) _ => [n]
    | _ => []

/-! ## The names the route's evaluator reads -/

mutual

/-- The names `evalIdxV` reads on the view. -/
def CoreMemDesign.readsIdxV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (e : PExpr) :
    List String :=
  match evalInt env e with
  | .ok _ => []
  | .error _ => E.readsV env elems none e

/-- **The names `evalV` reads on the view**, arm by arm: a compiled scalar subexpression reads its compiled
identifiers, a memory element read reads its index (the memory view is not a name). -/
def CoreMemDesign.readsV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (ctx : Option Nat) :
    PExpr → List String
  | e@(.arrayElem name [index]) =>
      match E.memDecl? name with
      | some _ => E.readsIdxV env elems index
      | none => (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e@(.arrayElem _ _) => (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e@(.arrayPart _ _ _ _ _) => (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e@(.bitSel base index) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then E.readsV env elems none base ++ E.readsIdxV env elems index
      else (instExpr2 env (E.widthsOf elems) ctx e).idents
  | .functionCall _ _ => []
  | e@(.unary _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then E.readsV env elems ctx a
      else (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e@(.binary _ a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then E.readsV env elems ctx a ++ E.readsV env elems ctx b
      else (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e@(.ternary c a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then
        E.readsV env elems none c ++ E.readsV env elems ctx a ++ E.readsV env elems ctx b
      else (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e@(.concat xs) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then E.readsListV env elems xs
      else (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e@(.resize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then E.readsV env elems ctx a
      else (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e@(.signedResize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then E.readsV env elems ctx a
      else (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e@(.squash2 _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then E.readsV env elems ctx a
      else (instExpr2 env (E.widthsOf elems) ctx e).idents
  | e => (instExpr2 env (E.widthsOf elems) ctx e).idents

/-- `readsV` of a list (the list arm of `evalV`). -/
def CoreMemDesign.readsListV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) :
    List PExpr → List String
  | [] => []
  | e :: es => E.readsV env elems none e ++ E.readsListV env elems es

end

/-- The scalar arm reads only its compiled identifiers. -/
theorem CoreMemDesign.evalScalarV_congr {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {v v' : SvState} {ctx : Option Nat} {e : PExpr}
    (h : ∀ x ∈ (instExpr2 env (E.widthsOf elems) ctx e).idents, SvState.lookup v x = SvState.lookup v' x) :
    E.evalScalarV env elems v ctx e = E.evalScalarV env elems v' ctx e :=
  evalPure2_congr h

mutual

theorem CoreMemDesign.evalIdxV_congr {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {v v' : SvState} {mv : MemV} :
    ∀ (e : PExpr), (∀ x ∈ E.readsIdxV env elems e, SvState.lookup v x = SvState.lookup v' x) →
      E.evalIdxV env elems v mv e = E.evalIdxV env elems v' mv e
  | e, h => by
      unfold CoreMemDesign.readsIdxV at h
      unfold CoreMemDesign.evalIdxV
      cases he : evalInt env e with
      | ok i => rfl
      | error m =>
          rw [he] at h
          exact CoreMemDesign.evalV_congr none e h

/-- **`evalV` reads the view only at `readsV`**: two views that agree there give the same value. -/
theorem CoreMemDesign.evalV_congr {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {v v' : SvState} {mv : MemV} :
    ∀ (ctx : Option Nat) (e : PExpr), (∀ x ∈ E.readsV env elems ctx e, SvState.lookup v x = SvState.lookup v' x) →
      E.evalV env elems v mv ctx e = E.evalV env elems v' mv ctx e
  | ctx, .lit _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .ident _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .paramRef _ _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .genvarRef _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .enumRef _ _ _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .int _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .fill _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .unsupported _ _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .sysCall _ _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .partSel _ _ _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .repl _ _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .reduce _ _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .cast _ _, h => by
      simp only [CoreMemDesign.readsV] at h; simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
  | ctx, .functionCall _ _, _ => by simp only [CoreMemDesign.evalV]
  | ctx, .arrayElem name indices, h => by
      cases indices with
      | nil =>
          simp only [CoreMemDesign.readsV] at h
          simp only [CoreMemDesign.evalV]
          split
          · rfl
          · exact CoreMemDesign.evalScalarV_congr h
      | cons i is =>
          cases is with
          | nil =>
              simp only [CoreMemDesign.readsV] at h
              simp only [CoreMemDesign.evalV]
              cases hmd : E.memDecl? name with
              | none =>
                  simp only [hmd] at h
                  exact CoreMemDesign.evalScalarV_congr h
              | some md =>
                  simp only [hmd] at h
                  rw [CoreMemDesign.evalIdxV_congr i h]
          | cons j js =>
              simp only [CoreMemDesign.readsV] at h
              simp only [CoreMemDesign.evalV]
              split
              · rfl
              · exact CoreMemDesign.evalScalarV_congr h
  | ctx, .arrayPart name indices mode a b, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      cases E.memDecl? name with
      | some _ => rfl
      | none => exact CoreMemDesign.evalScalarV_congr h
  | ctx, .bitSel base index, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      split
      · rename_i hm
        simp only [hm, ↓reduceIte] at h
        rw [CoreMemDesign.evalV_congr none base (fun x hx => h x (List.mem_append_left _ hx)),
          CoreMemDesign.evalIdxV_congr index (fun x hx => h x (List.mem_append_right _ hx))]
      · rename_i hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
        exact CoreMemDesign.evalScalarV_congr h
  | ctx, .unary op a, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      split
      · rename_i hm
        simp only [hm, ↓reduceIte] at h
        rw [CoreMemDesign.evalV_congr ctx a h]
      · rename_i hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
        exact CoreMemDesign.evalScalarV_congr h
  | ctx, .binary op a b, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      split
      · rename_i hm
        simp only [hm, ↓reduceIte] at h
        rw [CoreMemDesign.evalV_congr ctx a (fun x hx => h x (List.mem_append_left _ hx)),
          CoreMemDesign.evalV_congr ctx b (fun x hx => h x (List.mem_append_right _ hx))]
      · rename_i hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
        exact CoreMemDesign.evalScalarV_congr h
  | ctx, .ternary c a b, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      split
      · rename_i hm
        simp only [hm, ↓reduceIte] at h
        rw [CoreMemDesign.evalV_congr none c (fun x hx => h x (by simp [hx])),
          CoreMemDesign.evalV_congr ctx a (fun x hx => h x (by simp [hx])),
          CoreMemDesign.evalV_congr ctx b (fun x hx => h x (by simp [hx]))]
      · rename_i hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
        exact CoreMemDesign.evalScalarV_congr h
  | ctx, .concat xs, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      split
      · rename_i hm
        simp only [hm, ↓reduceIte] at h
        rw [CoreMemDesign.evalListV_congr xs h]
      · rename_i hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
        exact CoreMemDesign.evalScalarV_congr h
  | ctx, .resize w a, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      split
      · rename_i hm
        simp only [hm, ↓reduceIte] at h
        rw [CoreMemDesign.evalV_congr ctx a h]
      · rename_i hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
        exact CoreMemDesign.evalScalarV_congr h
  | ctx, .signedResize w a, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      split
      · rename_i hm
        simp only [hm, ↓reduceIte] at h
        rw [CoreMemDesign.evalV_congr ctx a h]
      · rename_i hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
        exact CoreMemDesign.evalScalarV_congr h
  | ctx, .squash2 w a, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      split
      · rename_i hm
        simp only [hm, ↓reduceIte] at h
        rw [CoreMemDesign.evalV_congr ctx a h]
      · rename_i hm
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
        exact CoreMemDesign.evalScalarV_congr h

theorem CoreMemDesign.evalListV_congr {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {v v' : SvState} {mv : MemV} :
    ∀ (xs : List PExpr), (∀ x ∈ E.readsListV env elems xs, SvState.lookup v x = SvState.lookup v' x) →
      E.evalListV env elems v mv xs = E.evalListV env elems v' mv xs
  | [], _ => by simp [CoreMemDesign.evalListV]
  | e :: es, h => by
      simp only [CoreMemDesign.readsListV] at h
      simp only [CoreMemDesign.evalListV]
      rw [CoreMemDesign.evalV_congr none e (fun x hx => h x (List.mem_append_left _ hx)),
        CoreMemDesign.evalListV_congr es (fun x hx => h x (List.mem_append_right _ hx))]

end

#print axioms CoreMemDesign.evalV_congr

/-- Each continuous assign, from index `idx` on, reads (in what the route evaluates: its compiled expression, or for an
assign that reads a memory the names `evalV` reads) no target of itself or of a LATER assign: topological source
order. -/
def CoreMemDesign.topoFrom (E : CoreMemDesign) (idx : Nat) : List CoreMemProc → Bool
  | [] => true
  | p :: rest =>
      (match p with
        | .assign (.ident n) value =>
            if LeanModels.Sv.PExpr.hasMemoryRead value || LeanModels.Sv.PExpr.hasFunctionCall value then
              match E.scalarWidth? n with
              | some w => (E.readsV E.env E.elems (some w) value).all fun x => !(assignTargets (p :: rest)).contains x
              | none => true
            else
              match E.compiledAssigns[idx]? with
              | some (some c) => c.idents.all fun x => !(assignTargets (p :: rest)).contains x
              | _ => true
        | _ => true) && E.topoFrom (idx + 1) rest

/-- The continuous assigns are in topological source order (on what the route evaluates). -/
def CoreMemDesign.topoC (E : CoreMemDesign) : Bool := E.topoFrom 0 E.processes.toList

mutual

/-- An edge body of nonblocking writes to whole signals only (under `if`, `case`, blocks): it reads one view and
issues updates of whole declared signals. -/
def _root_.LeanModels.Sv.PStmt.nbaWhole : PStmt → Bool
  | .nbaAssign _ _ => true
  | .nbaAssignL (.ident _) _ => true
  | .ifStmt _ y n => PStmt.nbaWhole y && PStmt.optNbaWhole n
  | .block body => PStmt.listNbaWhole body
  | .caseStmt _ items d _ _ => PStmt.itemsNbaWhole items && PStmt.optNbaWhole d
  | _ => false
termination_by structural s => s

/-- `nbaWhole` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optNbaWhole : Option PStmt → Bool
  | none => true
  | some s => PStmt.nbaWhole s
termination_by structural o => o

/-- `nbaWhole` of a list. -/
def _root_.LeanModels.Sv.PStmt.listNbaWhole : List PStmt → Bool
  | [] => true
  | s :: ss => PStmt.nbaWhole s && PStmt.listNbaWhole ss
termination_by structural xs => xs

/-- `nbaWhole` of the arms of a `case`. -/
def _root_.LeanModels.Sv.PStmt.itemsNbaWhole : List (List PExpr × PStmt) → Bool
  | [] => true
  | (_, b) :: rest => PStmt.nbaWhole b && PStmt.itemsNbaWhole rest
termination_by structural xs => xs

end

/-- A process whose edge body (if it is an edge process) is `nbaWhole`. -/
def CoreMemProc.nbaWholeP : CoreMemProc → Bool
  | .edge f => f.body.nbaWhole
  | _ => true

/-- The names the processes drive, process by process. -/
def CoreMemDesign.driven (E : CoreMemDesign) : List String := E.processes.toList.flatMap CoreMemProc.targets

/-- The input ports' names. -/
def CoreMemDesign.inputNamesL (E : CoreMemDesign) : List String :=
  E.scalar.decls.toList.filterMap fun dc => if dc.isInput then some dc.name else none

/-- One driver per signal: the names the processes drive are pairwise distinct. -/
def CoreMemDesign.oblDrivers (E : CoreMemDesign) : Bool := E.driven.Nodup

/-- No process drives an input or the clock. -/
def CoreMemDesign.oblNoInputWrite (E : CoreMemDesign) (clk : String) : Bool :=
  E.driven.all fun t => !E.inputNamesL.contains t && t != clk

/-- No process reads the clock. -/
def CoreMemDesign.oblNoClockRead (E : CoreMemDesign) (clk : String) : Bool :=
  E.processes.toList.all fun p => !p.reads.contains clk

/-- An asynchronous reset is an input port other than the clock. -/
def CoreMemDesign.oblReset (E : CoreMemDesign) (clk : String) : Bool :=
  E.processes.toList.all fun p => match p.reset? with
    | none => true
    | some r => E.inputNamesL.contains r && r != clk

/-- The edge order is irrelevant: at most one edge process, or every edge body nonblocking to whole signals
(`edgesV_perm`). -/
def CoreMemDesign.oblEdgeOrder (E : CoreMemDesign) : Bool :=
  let edges := E.processes.toList.filter CoreMemProc.isEdge
  decide (edges.length ≤ 1) || E.processes.toList.all CoreMemProc.nbaWholeP

/-- No expression of a process holds a node ingestion kept unconverted. -/
def CoreMemDesign.oblConverted (E : CoreMemDesign) : Bool :=
  E.processes.toList.all fun p => p.unconverted.isEmpty

/-- **The obligations of the clocked profile**, decided:
* one driver per signal: the base names the processes write are pairwise distinct across processes;
* the continuous assigns in topological source order on the expressions the route evaluates (`topoC`): then one settle
  pass is the fixpoint (`settleV_idem`), so no assign is out of date when a slot closes (§4.5, §10.3; the condition
  U1 violates);
* no process writes an input or the clock, and no process reads the clock;
* an asynchronous reset is an input port other than the clock (one the design drives would be seen by the route's
  edge detection only in a later slot: finding F7; the route itself refuses such designs since it gained
  `coreMemClockResetViol`, so this obligation is a check the instantiation already makes);
* the edge order is irrelevant: either every edge body writes whole signals with nonblocking assignments only (then
  each body reads the pre-edge view and the queues commit to disjoint signals: `edgesV_perm`) or there is at most one
  edge process (no order to choose: `edgesV_single`);
* no expression of a process holds a node ingestion kept unconverted (the route refuses it when evaluated).
Under them two choices of the route are proved harmless (rule 4's cheap sufficient conditions): its fixed number of
settle passes reaches the fixpoint (`settleV_idem`), and its source order of the edge processes does not change the
commit (`edgesV_order`). That `step` is every legal schedule of the scheduled E is the semantics lane's U3. -/
def CoreMemDesign.seqOblB (E : CoreMemDesign) (clk : String) : Bool :=
  E.oblDrivers && E.topoC && E.oblNoInputWrite clk && E.oblNoClockRead clk && E.oblReset clk && E.oblEdgeOrder &&
    E.oblConverted

/-- **The structure of a clocked family member**: it instantiates, in the clocked profile, with its obligations. -/
def SeqDesign (r : Res CoreMemDesign) (clk : String) : Prop :=
  ∃ E, r = .ok E ∧ E.SeqProfile clk ∧ E.seqOblB clk = true


/-! ## What the obligations buy: the settle is a fixpoint (§4.5, §10.3; U1 excluded)

The route closes a slot after a fixed number of source-order passes over the continuous assigns. Under the topological
obligation (`topoC`: each assign reads, in what the route evaluates, no target of itself or of a later assign) one pass
already reaches the fixpoint: a further pass changes nothing (`settleV_idem`), so no continuous assignment is out of
date when the slot closes, and the route's settled value is the LRM's. -/

/-- One settle pass changes only the targets of the assigns it runs. -/
theorem CoreMemDesign.settleRaw_frame {E : CoreMemDesign} {mv : MemV} :
    ∀ (procs : List CoreMemProc) (idx : Nat) (r r' : SvState), E.settleRaw mv r idx procs = .ok r' →
      ∀ x, x ∉ assignTargets procs → SvState.lookup r' x = SvState.lookup r x
  | [], _, r, r', h, x, _ => by
      simp only [CoreMemDesign.settleRaw, Res.ok.injEq] at h
      subst h; rfl
  | p :: rest, idx, r, r', h, x, hx => by
      cases p with
      | assign t v =>
          cases t with
          | ident n =>
              have hxn : n ≠ x := fun h' => hx (by subst h'; simp [assignTargets])
              have hxr : x ∉ assignTargets rest := fun h' => hx (by simp [assignTargets] at h' ⊢; exact Or.inr h')
              simp only [CoreMemDesign.settleRaw] at h
              split at h
              · split at h
                · simp only [Res.bind_eq_ok] at h
                  obtain ⟨y, -, h⟩ := h
                  rw [CoreMemDesign.settleRaw_frame rest (idx + 1) _ r' h x hxr, lookup_set']
                  simp [hxn]
                · simp at h
              · split at h
                · simp only [Res.bind_eq_ok] at h
                  obtain ⟨y, -, h⟩ := h
                  rw [CoreMemDesign.settleRaw_frame rest (idx + 1) _ r' h x hxr, lookup_set']
                  simp [hxn]
                · simp at h
          | _ => simp [CoreMemDesign.settleRaw] at h
      | edge f =>
          simp only [CoreMemDesign.settleRaw] at h
          exact CoreMemDesign.settleRaw_frame rest (idx + 1) r r' h x (by simpa [assignTargets] using hx)
      | initial _ => simp [CoreMemDesign.settleRaw] at h
      | comb _ => simp [CoreMemDesign.settleRaw] at h
      | implicit _ => simp [CoreMemDesign.settleRaw] at h
      | unsupported _ _ => simp [CoreMemDesign.settleRaw] at h

/-- The materialization reads a raw view only through its lookups. -/
theorem CoreMemDesign.matV_congr {E : CoreMemDesign} {r r' : SvState}
    (h : ∀ x, SvState.lookup r x = SvState.lookup r' x) : E.matV r = E.matV r' := by
  unfold CoreMemDesign.matV
  exact List.map_congr_left fun dc _ => by rw [h dc.name]

/-- The materialization at one name reads the raw view only at that name. -/
theorem CoreMemDesign.lookup_matV_congr {E : CoreMemDesign} {r r' : SvState} {x : String}
    (h : SvState.lookup r x = SvState.lookup r' x) :
    SvState.lookup (E.matV r) x = SvState.lookup (E.matV r') x := by
  unfold CoreMemDesign.matV
  induction E.scalar.decls.toList with
  | nil => rfl
  | cons dc ds ih =>
      simp only [List.map_cons, SvState.lookup]
      by_cases hx : dc.name = x
      · subst hx; simp [h]
      · have hx' : (dc.name == x) = false := by simpa using hx
        simp only [hx', Bool.false_eq_true, ↓reduceIte]
        exact ih

/-- **Two passes from views that agree off the remaining targets agree everywhere at the end**, when the assigns are
in topological order: each assign reads only names that are not remaining targets. -/
theorem CoreMemDesign.settleRaw_agree {E : CoreMemDesign} {mv : MemV} :
    ∀ (procs : List CoreMemProc) (idx : Nat) (r1 r2 r1' : SvState), E.topoFrom idx procs = true →
      (∀ x, x ∉ assignTargets procs → SvState.lookup r1 x = SvState.lookup r2 x) →
      E.settleRaw mv r1 idx procs = .ok r1' →
      ∃ r2', E.settleRaw mv r2 idx procs = .ok r2' ∧ ∀ x, SvState.lookup r1' x = SvState.lookup r2' x
  | [], _, r1, r2, r1', _, hag, h => by
      simp only [CoreMemDesign.settleRaw, Res.ok.injEq] at h
      subst h
      exact ⟨r2, rfl, fun x => hag x (by simp [assignTargets])⟩
  | p :: rest, idx, r1, r2, r1', ht, hag, h => by
      simp only [CoreMemDesign.topoFrom, Bool.and_eq_true] at ht
      cases p with
      | assign t v =>
          cases t with
          | ident n =>
              -- the continuation after the assign sets `n` to the same value on both sides
              have hcont : ∀ y, E.settleRaw mv (SvState.set r1 n y) (idx + 1) rest = .ok r1' →
                  ∃ r2', E.settleRaw mv (SvState.set r2 n y) (idx + 1) rest = .ok r2' ∧
                    ∀ x, SvState.lookup r1' x = SvState.lookup r2' x := by
                intro y hy
                have hag' : ∀ x, x ∉ assignTargets rest →
                    SvState.lookup (SvState.set r1 n y) x = SvState.lookup (SvState.set r2 n y) x := by
                  intro x hx
                  rw [lookup_set', lookup_set']
                  by_cases hnx : n = x
                  · simp [hnx]
                  · simp only [hnx, ↓reduceIte]
                    exact hag x (by simp [assignTargets] at hx ⊢; exact ⟨fun h' => hnx h'.symm, hx⟩)
                exact CoreMemDesign.settleRaw_agree rest (idx + 1) _ _ r1' ht.2 hag' hy
              have hnot : ∀ (ns : List String), (ns.all fun x => !(assignTargets (.assign (.ident n) v :: rest)).contains x) = true →
                  ∀ x ∈ ns, SvState.lookup r1 x = SvState.lookup r2 x := by
                intro ns hns x hx
                simp only [List.all_eq_true, Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false,
                  beq_iff_eq] at hns
                exact hag x fun hxt => hns x hx x hxt rfl
              simp only [CoreMemDesign.settleRaw] at h
              have ht1 := ht.1
              split at h
              · rename_i hm
                simp only [hm, ↓reduceIte] at ht1
                cases hw : E.scalarWidth? n with
                | none => simp [hw] at h
                | some w =>
                    simp only [hw, Res.bind_eq_ok] at h ht1
                    obtain ⟨y, hy, h⟩ := h
                    have hreads := hnot _ ht1
                    have hy2 : E.evalV E.env E.elems (E.matV r2) mv (some w) v = .ok y := by
                      rw [← CoreMemDesign.evalV_congr (some w) v
                        (fun x hx => CoreMemDesign.lookup_matV_congr (hreads x hx))]
                      exact hy
                    obtain ⟨r2', h2, hfin⟩ := hcont y h
                    exact ⟨r2', by simp [CoreMemDesign.settleRaw, hm, hw, hy2, h2], hfin⟩
              · rename_i hm
                simp only [hm, Bool.false_eq_true, ↓reduceIte] at ht1
                cases hc : E.compiledAssigns[idx]? with
                | none => simp [hc] at h
                | some oc =>
                    cases oc with
                    | none => simp [hc] at h
                    | some c =>
                        simp only [hc, Res.bind_eq_ok] at h ht1
                        obtain ⟨y, hy, h⟩ := h
                        have hy2 : evalPure2 r2 c = .ok y := by rw [← evalPure2_congr (hnot _ ht1)]; exact hy
                        obtain ⟨r2', h2, hfin⟩ := hcont y h
                        exact ⟨r2', by simp [CoreMemDesign.settleRaw, hm, hc, hy2, h2], hfin⟩
          | _ => simp [CoreMemDesign.settleRaw] at h
      | edge f =>
          simp only [CoreMemDesign.settleRaw] at h
          obtain ⟨r2', h2, hfin⟩ := CoreMemDesign.settleRaw_agree rest (idx + 1) r1 r2 r1' ht.2
            (fun x hx => hag x (by simpa [assignTargets] using hx)) h
          exact ⟨r2', by simp [CoreMemDesign.settleRaw, h2], hfin⟩
      | initial _ => simp [CoreMemDesign.settleRaw] at h
      | comb _ => simp [CoreMemDesign.settleRaw] at h
      | implicit _ => simp [CoreMemDesign.settleRaw] at h
      | unsupported _ _ => simp [CoreMemDesign.settleRaw] at h

/-- **THE SETTLE IS A FIXPOINT**: under the topological obligation, from a materialized view (every view of a coherent
state is one, `matV_view`), one more settle pass after a settle pass changes nothing, whatever the memory view. So the
route's slot never closes with a continuous assignment out of date (§4.5, §10.3: the condition U1 violates), and its
extra passes are idle. -/
theorem CoreMemDesign.settleV_idem {E : CoreMemDesign} (ht : E.topoC = true) {mv : MemV} {v v' : SvState}
    (hv : E.matV v = v) (h : E.settleV mv v = .ok v') : E.settleV mv v' = .ok v' := by
  simp only [CoreMemDesign.settleV, Res.bind_eq_ok, Res.ok.injEq] at h
  obtain ⟨r1, hr1, rfl⟩ := h
  have hinv : ∀ x, x ∉ assignTargets E.processes.toList → SvState.lookup v x = SvState.lookup (E.matV r1) x := by
    intro x hx
    have hf := CoreMemDesign.settleRaw_frame _ _ _ _ hr1 x hx
    calc SvState.lookup v x = SvState.lookup (E.matV v) x := by rw [hv]
      _ = SvState.lookup (E.matV r1) x := CoreMemDesign.lookup_matV_congr hf.symm
  obtain ⟨r2, hr2, hagree⟩ := CoreMemDesign.settleRaw_agree E.processes.toList 0 v (E.matV r1) r1 ht hinv hr1
  simp only [CoreMemDesign.settleV, hr2, Res.ok_bind, Res.ok.injEq]
  exact (CoreMemDesign.matV_congr hagree).symm

#print axioms CoreMemDesign.settleV_idem

/-- **The slot under the obligations**: one settle pass before the edge, one after (`slotV`'s second passes are idle). -/
def CoreMemDesign.slot1V (E : CoreMemDesign) (v : SvState) (mv : MemV) (entry : SvState) : Res (SvState × MemV) := do
  let p ← E.settleV mv (applyInputs2 E.scalar.toDesign2 entry v)
  let r ← E.edgesV v p p mv E.processes.toList
  let s ← E.settleV (commitMemV mv r.2.2) (commitNba2 r.1 r.2.1)
  .ok (s, commitMemV mv r.2.2)

/-- **The cycle under the obligations**, two `slot1V`s. -/
def CoreMemDesign.cycle1V (E : CoreMemDesign) (clk : String) (σ : SvState × MemV) (data : SvState) :
    Res ((SvState × MemV) × (SvState × MemV)) := do
  let pre ← E.slot1V σ.1 σ.2 (lowEntry clk data)
  let post ← E.slot1V pre.1 pre.2 (highEntry clk)
  .ok (pre, post)

/-- A settle pass's result is materialized (on distinct 4-state declarations). -/
theorem CoreMemDesign.matV_settleV {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {mv : MemV} {v v' : SvState} (h : E.settleV mv v = .ok v') : E.matV v' = v' := by
  simp only [CoreMemDesign.settleV, Res.bind_eq_ok, Res.ok.injEq] at h
  obtain ⟨r, -, rfl⟩ := h
  rw [← E.view_storeFromView r]
  exact CoreMemDesign.matV_view hnd h4 (E.typed_storeFromView r)

/-- The view a slot commits its edge updates on is materialized (it is the view of a typed store). -/
theorem CoreMemDesign.matV_commit_of_slot {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory) {entry : SvState}
    (hty : EntryTyped E.scalar.toDesign2 entry) {p : SvState}
    (hp : E.settleV (E.memOf st.memory) (applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar)) = .ok p)
    {r : ExecV} (hr : E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) E.processes.toList = .ok r) :
    E.matV (commitNba2 r.1 r.2.1) = commitNba2 r.1 r.2.1 := by
  have hmi : E.applyMemoryInputs entry st.memory = st.memory := E.applyMemoryInputs_id hP.mems entry st.memory
  have hTin : E.scalar.Typed (E.scalar.applyInputs st.scalar entry) := hc.typed.applyInputs entry
  have hci := E.normalizeScalar_coherent { st with memory := E.applyMemoryInputs entry st.memory } hTin
  have hvi : E.scalar.view (E.normalizeScalar { st with memory := E.applyMemoryInputs entry st.memory }
      (E.scalar.applyInputs st.scalar entry)).scalar =
        applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar) := by
    rw [E.normalizeScalar_view, Elab.view_applyInputs hP.names hP.four hc.typed hty]
  have hmemi : (E.normalizeScalar { st with memory := E.applyMemoryInputs entry st.memory }
      (E.scalar.applyInputs st.scalar entry)).memory = st.memory := hmi
  obtain ⟨st0, -, hv0, hc0, hm0⟩ := CoreMemDesign.settleAssign_seq hP hci (by rw [hmemi]; exact hmc)
    (by rw [hvi, hmemi]; exact hp)
  rw [hmemi] at hm0
  rcases r with ⟨r1, r2, r3⟩
  obtain ⟨st2, -, hv2, hc2, -⟩ := CoreMemDesign.runEdges_V hP.names hP.four clk
    (E.scalar.view st.scalar) p E.processes.toList hP.shapes st0 r1 r2 r3 hc0 (by rw [hm0]; exact hmc)
    (by rw [hv0, hm0]; exact hr)
  have hT2 : E.scalarEdge.base.Typed st2.scalar := by rw [hP.base]; exact hc2.typed
  have hTc : E.scalar.Typed (E.scalarEdge.commit st2.scalar r2) := by
    have := Elab1.typed_commit (E := E.scalarEdge) r2 hT2
    rwa [hP.base] at this
  have hvc : E.scalar.view (E.scalarEdge.commit st2.scalar r2) = commitNba2 r1 r2 := by
    have := Elab1.view_commit (E := E.scalarEdge) (by rw [hP.base]; exact hP.four) r2 hT2
    rw [hP.base] at this
    rw [this, hv2]
  show E.matV (commitNba2 r1 r2) = commitNba2 r1 r2
  rw [← hvc]
  exact CoreMemDesign.matV_view hP.names hP.four hTc

/-- **THE SLOT UNDER THE OBLIGATIONS**: from a coherent state's view and memory view and a typed entry, the route's slot
(four settle passes) and the one-pass slot agree. -/
theorem CoreMemDesign.slotV_eq_slot1V {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (ht : E.topoC = true) {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory) {entry : SvState}
    (hty : EntryTyped E.scalar.toDesign2 entry) :
    E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry =
      E.slot1V (E.scalar.view st.scalar) (E.memOf st.memory) entry := by
  have hin : E.matV (applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar)) =
      applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar) := by
    rw [← Elab.view_applyInputs hP.names hP.four hc.typed hty]
    exact CoreMemDesign.matV_view hP.names hP.four (hc.typed.applyInputs entry)
  simp only [CoreMemDesign.slotV, CoreMemDesign.slot1V]
  cases hp : E.settleV (E.memOf st.memory) (applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar)) with
  | ok p =>
      simp only [Res.ok_bind, CoreMemDesign.settleV_idem ht hin hp]
      cases hr : E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) E.processes.toList with
      | ok r =>
          simp only [Res.ok_bind]
          cases hs : E.settleV (commitMemV (E.memOf st.memory) r.2.2) (commitNba2 r.1 r.2.1) with
          | ok s1 =>
              simp only [Res.ok_bind]
              rw [CoreMemDesign.settleV_idem ht (CoreMemDesign.matV_commit_of_slot hP hc hmc hty hp hr) hs]
              rfl
          | timeout => rfl
          | unsupported m => rfl
      | timeout => rfl
      | unsupported m => rfl
  | timeout => rfl
  | unsupported m => rfl

/-! ## What the obligations buy: the edge order does not matter (rule 4)

The route runs the edge processes of a slot in source order; the LRM leaves the order open. Under `oblEdgeOrder` and
one driver per signal, every order gives the same committed view: with at most one edge process there is nothing to
order (`edgesV_single`); with nonblocking whole-signal bodies each body reads the same view, issues no memory record,
and the queues write disjoint signals, so their commits commute (`edgesV_perm`, through `commitNba2_perm`). -/

mutual

/-- An `nbaWhole` body leaves the view alone, issues updates of the signals it writes, and no memory record. -/
theorem CoreMemDesign.execV_nbaWhole {E : CoreMemDesign} (v : SvState) (mv : MemV) :
    ∀ (b : PStmt) (v' : SvState) (q : NbaQueue2) (mq : MemQV), b.nbaWhole = true →
      E.execV v mv b = .ok (v', q, mq) → v' = v ∧ (∀ u ∈ q, u.1 ∈ b.writes) ∧ mq = []
  | .nbaAssign t e, v', q, mq, _, h => by
      simp only [CoreMemDesign.execV] at h
      split at h
      · simp at h
      · simp only [Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨x, -, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, by simp [PStmt.writes], rfl⟩
  | .nbaAssignL lhs e, v', q, mq, hb, h => by
      cases lhs with
      | ident t =>
          simp only [CoreMemDesign.execV] at h
          split at h
          · simp at h
          · simp only [Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨x, -, rfl, rfl, rfl⟩ := h
            exact ⟨rfl, by simp [PStmt.writes, PLhs.baseNames], rfl⟩
      | _ => simp [PStmt.nbaWhole] at hb
  | .ifStmt c y n, v', q, mq, hb, h => by
      simp only [PStmt.nbaWhole, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at h
      obtain ⟨cv, -, h⟩ := h
      split at h
      · obtain ⟨h1, h2, h3⟩ := CoreMemDesign.execV_nbaWhole v mv y v' q mq hb.1 h
        exact ⟨h1, fun u hu => by simp only [PStmt.writes, List.mem_append]; exact Or.inl (h2 u hu), h3⟩
      · cases n with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨rfl, by simp, rfl⟩
        | some s =>
            simp only [CoreMemDesign.execOptV] at h
            simp only [PStmt.optNbaWhole] at hb
            obtain ⟨h1, h2, h3⟩ := CoreMemDesign.execV_nbaWhole v mv s v' q mq hb.2 h
            exact ⟨h1, fun u hu => by
              simp only [PStmt.writes, PStmt.optWrites, List.mem_append]; exact Or.inr (h2 u hu), h3⟩
  | .block body, v', q, mq, hb, h => by
      simp only [PStmt.nbaWhole] at hb
      simp only [CoreMemDesign.execV] at h
      obtain ⟨h1, h2, h3⟩ := CoreMemDesign.execListV_nbaWhole v mv body v' q mq hb h
      exact ⟨h1, fun u hu => by simp only [PStmt.writes]; exact h2 u hu, h3⟩
  | .caseStmt subject items d mode check, v', q, mq, hb, h => by
      simp only [PStmt.nbaWhole, Bool.and_eq_true] at hb
      have hdflt : ∀ r, E.execOptV v mv d = .ok r → r.1 = v ∧ (∀ u ∈ r.2.1, u.1 ∈ PStmt.optWrites d) ∧ r.2.2 = [] := by
        intro r hr
        cases d with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq] at hr
            subst hr
            exact ⟨rfl, by simp, rfl⟩
        | some s =>
            simp only [CoreMemDesign.execOptV] at hr
            simp only [PStmt.optNbaWhole] at hb
            exact CoreMemDesign.execV_nbaWhole v mv s r.1 r.2.1 r.2.2 hb.2 hr
      have hitems : ∀ sv res, E.execItemsV v mv sv mode items (E.execOptV v mv d) = .ok res →
          res.1 = v ∧ (∀ u ∈ res.2.1, u.1 ∈ (PStmt.caseStmt subject items d mode check).writes) ∧ res.2.2 = [] := by
        intro sv res hres
        obtain ⟨h1, h2, h3⟩ := CoreMemDesign.execItemsV_nbaWhole v mv sv mode items _ res hb.1 hdflt hres
        exact ⟨h1, fun u hu => by simp only [PStmt.writes]; exact h2 u hu, h3⟩
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at h
      obtain ⟨sv, -, h⟩ := h
      cases check
      case none => exact hitems sv (v', q, mq) h
      all_goals
        simp only [Res.bind_eq_ok] at h
        obtain ⟨n, -, h⟩ := h
        split at h
        · exact hitems sv (v', q, mq) h
        · simp at h
  | .blockingAssign _ _, _, _, _, hb, _ => by simp [PStmt.nbaWhole] at hb
  | .blockingAssignL _ _, _, _, _, hb, _ => by simp [PStmt.nbaWhole] at hb
  | .forLoop .., _, _, _, hb, _ => by simp [PStmt.nbaWhole] at hb
  | .unsupported .., _, _, _, hb, _ => by simp [PStmt.nbaWhole] at hb

/-- The list form of `execV_nbaWhole`. -/
theorem CoreMemDesign.execListV_nbaWhole {E : CoreMemDesign} (v : SvState) (mv : MemV) :
    ∀ (bs : List PStmt) (v' : SvState) (q : NbaQueue2) (mq : MemQV), PStmt.listNbaWhole bs = true →
      E.execListV v mv bs = .ok (v', q, mq) → v' = v ∧ (∀ u ∈ q, u.1 ∈ PStmt.listWrites bs) ∧ mq = []
  | [], v', q, mq, _, h => by
      simp only [CoreMemDesign.execListV, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, by simp, rfl⟩
  | s :: ss, v', q, mq, hb, h => by
      simp only [PStmt.listNbaWhole, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.execListV, Res.bind_eq_ok, Res.ok.injEq] at h
      obtain ⟨⟨v1, a, ma⟩, h1, ⟨v2, b, mb⟩, h2, hq⟩ := h
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      obtain ⟨hv1, ha, hma⟩ := CoreMemDesign.execV_nbaWhole v mv s v1 a ma hb.1 h1
      rw [hv1] at h2
      obtain ⟨hv2, hb', hmb⟩ := CoreMemDesign.execListV_nbaWhole v mv ss v2 b mb hb.2 h2
      refine ⟨hv2, fun u hu => ?_, by simp [hma, hmb]⟩
      simp only [PStmt.listWrites, List.mem_append]
      rcases List.mem_append.mp hu with hu | hu
      · exact Or.inl (ha u hu)
      · exact Or.inr (hb' u hu)

/-- The arms of a `case` in `nbaWhole` form: the view is left alone, the updates write the arms' or the default's
signals, no memory record. -/
theorem CoreMemDesign.execItemsV_nbaWhole {E : CoreMemDesign} (v : SvState) (mv : MemV) (sv : LVec)
    (mode : CaseMode) :
    ∀ (items : List (List PExpr × PStmt)) (dflt : Res ExecV) (res : ExecV) {D : List String},
      PStmt.itemsNbaWhole items = true →
      (∀ r, dflt = .ok r → r.1 = v ∧ (∀ u ∈ r.2.1, u.1 ∈ D) ∧ r.2.2 = []) →
      E.execItemsV v mv sv mode items dflt = .ok res →
      res.1 = v ∧ (∀ u ∈ res.2.1, u.1 ∈ PStmt.itemsWrites items ++ D) ∧ res.2.2 = []
  | [], dflt, res, D, _, hd, h => by
      simp only [CoreMemDesign.execItemsV] at h
      obtain ⟨h1, h2, h3⟩ := hd res h
      exact ⟨h1, fun u hu => by simp [PStmt.itemsWrites, h2 u hu], h3⟩
  | (ps, b) :: rest, dflt, res, D, hb, hd, h => by
      simp only [PStmt.itemsNbaWhole, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.execItemsV, Res.bind_eq_ok] at h
      obtain ⟨vals, -, h⟩ := h
      split at h
      · obtain ⟨h1, h2, h3⟩ := CoreMemDesign.execV_nbaWhole v mv b res.1 res.2.1 res.2.2 hb.1 h
        exact ⟨h1, fun u hu => by
          simp only [PStmt.itemsWrites, List.mem_append]; exact Or.inl (Or.inl (h2 u hu)), h3⟩
      · obtain ⟨h1, h2, h3⟩ := CoreMemDesign.execItemsV_nbaWhole v mv sv mode rest dflt res hb.2 hd h
        refine ⟨h1, fun u hu => ?_, h3⟩
        have := h2 u hu
        simp only [PStmt.itemsWrites, List.mem_append] at this ⊢
        rcases this with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'

end

/-- Two queues writing disjoint signals commit in either order. -/
theorem commitNba2_swap {st : SvState} (hnd : (st.map Prod.fst).Nodup) {q₁ q₂ : NbaQueue2}
    (h : ∀ u ∈ q₁, ∀ u' ∈ q₂, u.1 ≠ u'.1) : commitNba2 st (q₂ ++ q₁) = commitNba2 st (q₁ ++ q₂) := by
  have := commitNba2_perm (B := fun i => if i = 0 then q₁ else if i = 1 then q₂ else [])
    (by
      intro p p' hpp u hu u' hu'
      left
      by_cases h0 : p = 0
      · subst h0
        by_cases h1 : p' = 1
        · subst h1; simp at hu hu'; exact h u hu u' hu'
        · simp [h1, show p' ≠ 0 from fun h' => hpp h'.symm] at hu'
      · by_cases h1 : p = 1
        · subst h1
          by_cases h0' : p' = 0
          · subst h0'; simp at hu hu'; exact fun he => h u' hu' u hu he.symm
          · simp [h0', show p' ≠ 1 from fun h' => hpp h'.symm] at hu'
        · simp [h0, h1] at hu)
    (l := [1, 0]) (l' := [0, 1]) (List.Perm.swap 0 1 []) (by decide) hnd
  simpa using this

/-- The scalar updates a process issues in the edge pass on the views `v`, `mv` (none if it is not an edge process or
does not fire). -/
def CoreMemDesign.procQ (E : CoreMemDesign) (before after v : SvState) (mv : MemV) : CoreMemProc → Res NbaQueue2
  | .edge p => if p.fires before after then do
      let r ← E.execV v mv p.body
      .ok r.2.1
    else .ok []
  | _ => .ok []

/-- The edge pass over `p :: rest`, `p` in `nbaWhole` form: `p`'s updates (of signals `p` drives, no memory record),
then the pass over `rest` on the same view. -/
theorem CoreMemDesign.edgesV_cons_inv {E : CoreMemDesign} {before after v : SvState} {mv : MemV} {p : CoreMemProc}
    {rest : List CoreMemProc} (hp : p.nbaWholeP = true) {r : ExecV}
    (h : E.edgesV before after v mv (p :: rest) = .ok r) :
    ∃ qp rr, E.procQ before after v mv p = .ok qp ∧ (∀ u ∈ qp, u.1 ∈ p.targets) ∧
      E.edgesV before after v mv rest = .ok rr ∧ r = (rr.1, qp ++ rr.2.1, rr.2.2) := by
  cases p with
  | edge f =>
      simp only [CoreMemDesign.edgesV] at h
      simp only [CoreMemDesign.procQ]
      split at h
      · rename_i hf
        simp only [Res.bind_eq_ok, Res.ok.injEq] at h
        obtain ⟨⟨v1, a, ma⟩, h1, rr, h2, rfl⟩ := h
        obtain ⟨rfl, ha, rfl⟩ := CoreMemDesign.execV_nbaWhole v mv f.body v1 a ma
          (by simpa [CoreMemProc.nbaWholeP] using hp) h1
        exact ⟨a, rr, by simp [hf, h1], fun u hu => by simp [CoreMemProc.targets, List.mem_eraseDups, ha u hu],
          h2, by simp⟩
      · rename_i hf
        exact ⟨[], r, by simp [hf], by simp, h, by simp⟩
  | assign t e => simp only [CoreMemDesign.edgesV] at h; exact ⟨[], r, rfl, by simp, h, by simp⟩
  | initial b => simp only [CoreMemDesign.edgesV] at h; exact ⟨[], r, rfl, by simp, h, by simp⟩
  | comb b => simp only [CoreMemDesign.edgesV] at h; exact ⟨[], r, rfl, by simp, h, by simp⟩
  | implicit b => simp only [CoreMemDesign.edgesV] at h; exact ⟨[], r, rfl, by simp, h, by simp⟩
  | unsupported k t => simp only [CoreMemDesign.edgesV] at h; exact ⟨[], r, rfl, by simp, h, by simp⟩

/-- The converse of `edgesV_cons_inv`. -/
theorem CoreMemDesign.edgesV_cons_mk {E : CoreMemDesign} {before after v : SvState} {mv : MemV} {p : CoreMemProc}
    {rest : List CoreMemProc} (hp : p.nbaWholeP = true) {qp : NbaQueue2} {rr : ExecV}
    (h1 : E.procQ before after v mv p = .ok qp) (h2 : E.edgesV before after v mv rest = .ok rr) :
    E.edgesV before after v mv (p :: rest) = .ok (rr.1, qp ++ rr.2.1, rr.2.2) := by
  cases p with
  | edge f =>
      simp only [CoreMemDesign.procQ] at h1
      simp only [CoreMemDesign.edgesV]
      split at h1
      · rename_i hf
        simp only [Res.bind_eq_ok, Res.ok.injEq] at h1
        obtain ⟨⟨v1, a, ma⟩, ha, rfl⟩ := h1
        obtain ⟨rfl, -, rfl⟩ := CoreMemDesign.execV_nbaWhole v mv f.body v1 a ma
          (by simpa [CoreMemProc.nbaWholeP] using hp) ha
        simp [hf, ha, h2]
      · rename_i hf
        simp only [Res.ok.injEq] at h1
        subst h1
        simp [hf, h2]
  | assign t e => simp only [CoreMemDesign.procQ, Res.ok.injEq] at h1; subst h1; simp [CoreMemDesign.edgesV, h2]
  | initial b => simp only [CoreMemDesign.procQ, Res.ok.injEq] at h1; subst h1; simp [CoreMemDesign.edgesV, h2]
  | comb b => simp only [CoreMemDesign.procQ, Res.ok.injEq] at h1; subst h1; simp [CoreMemDesign.edgesV, h2]
  | implicit b => simp only [CoreMemDesign.procQ, Res.ok.injEq] at h1; subst h1; simp [CoreMemDesign.edgesV, h2]
  | unsupported k t =>
      simp only [CoreMemDesign.procQ, Res.ok.injEq] at h1; subst h1; simp [CoreMemDesign.edgesV, h2]

/-- An edge pass over `nbaWhole` processes leaves the view alone and issues no memory record. -/
theorem CoreMemDesign.edgesV_view {E : CoreMemDesign} {before after v : SvState} {mv : MemV} :
    ∀ {ps : List CoreMemProc}, (∀ p ∈ ps, p.nbaWholeP = true) → ∀ {r : ExecV},
      E.edgesV before after v mv ps = .ok r → r.1 = v ∧ r.2.2 = []
  | [], _, r, h => by
      simp only [CoreMemDesign.edgesV, Res.ok.injEq] at h
      subst h; exact ⟨rfl, rfl⟩
  | p :: rest, hw, r, h => by
      obtain ⟨qp, rr, -, -, h2, rfl⟩ := CoreMemDesign.edgesV_cons_inv (hw p (by simp)) h
      exact (CoreMemDesign.edgesV_view (fun q hq => hw q (List.mem_cons_of_mem _ hq)) h2 : rr.1 = v ∧ rr.2.2 = [])

/-- **THE EDGE ORDER DOES NOT MATTER** (nonblocking whole-signal bodies, one driver per signal): every permutation of
the processes gives an edge pass that succeeds when the route's succeeds, leaves the view alone, issues no memory
record, and commits to the same view from every state with distinct names. -/
theorem CoreMemDesign.edgesV_perm {E : CoreMemDesign} {before after v : SvState} {mv : MemV} :
    ∀ {ps ps' : List CoreMemProc}, ps.Perm ps' → (∀ p ∈ ps, p.nbaWholeP = true) →
      (ps.flatMap CoreMemProc.targets).Nodup → ∀ {r : ExecV},
      E.edgesV before after v mv ps = .ok r →
      r.1 = v ∧ r.2.2 = [] ∧ ∃ r', E.edgesV before after v mv ps' = .ok r' ∧ r'.1 = v ∧ r'.2.2 = [] ∧
        ∀ st : SvState, (st.map Prod.fst).Nodup → commitNba2 st r'.2.1 = commitNba2 st r.2.1 := by
  intro ps ps' hperm
  induction hperm with
  | nil =>
      intro _ _ r h
      simp only [CoreMemDesign.edgesV, Res.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl, _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons x _ ih =>
      intro hw hnd r h
      have hnd' := (List.nodup_append.mp (by simpa [List.flatMap_cons] using hnd)).2.1
      cases x with
      | edge f =>
          simp only [CoreMemDesign.edgesV] at h ⊢
          split at h
          · rename_i hf
            simp only [hf, ↓reduceIte]
            simp only [Res.bind_eq_ok, Res.ok.injEq] at h
            obtain ⟨⟨v1, a, ma⟩, h1, ⟨v2, b, mb⟩, h2, rfl⟩ := h
            obtain ⟨rfl, -, rfl⟩ := CoreMemDesign.execV_nbaWhole v mv f.body v1 a ma
              (by simpa [CoreMemProc.nbaWholeP] using hw (.edge f) (by simp)) h1
            obtain ⟨hv2, hm2, r', h2', hv2', hm2', hc⟩ := ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hnd' h2
            refine ⟨hv2, by simpa using hm2, (r'.1, a ++ r'.2.1, [] ++ r'.2.2), ?_, hv2', by simpa using hm2',
              fun st hst => ?_⟩
            · simp [h1, h2']
            · show commitNba2 st (a ++ r'.2.1) = commitNba2 st (a ++ b)
              rw [commitNba2_append, commitNba2_append]
              exact hc _ (by rw [keys_commitNba2]; exact hst)
          · rename_i hf
            simp only [hf, Bool.false_eq_true, ↓reduceIte]
            exact ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hnd' h
      | assign t e =>
          simp only [CoreMemDesign.edgesV] at h ⊢
          exact ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hnd' h
      | initial b =>
          simp only [CoreMemDesign.edgesV] at h ⊢
          exact ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hnd' h
      | comb b =>
          simp only [CoreMemDesign.edgesV] at h ⊢
          exact ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hnd' h
      | implicit b =>
          simp only [CoreMemDesign.edgesV] at h ⊢
          exact ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hnd' h
      | unsupported k t =>
          simp only [CoreMemDesign.edgesV] at h ⊢
          exact ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hnd' h
  | swap x y l =>
      intro hw hnd r h
      have hy := hw y (by simp)
      have hx := hw x (by simp)
      have hl : ∀ p ∈ l, p.nbaWholeP = true := fun p hp => hw p (by simp [hp])
      obtain ⟨qy, r1, hqy, hny, h1, rfl⟩ := CoreMemDesign.edgesV_cons_inv hy h
      obtain ⟨qx, r2, hqx, hnx, h2, rfl⟩ := CoreMemDesign.edgesV_cons_inv hx h1
      obtain ⟨hv2, hm2⟩ := CoreMemDesign.edgesV_view hl h2
      refine ⟨hv2, hm2, (r2.1, qx ++ (qy ++ r2.2.1), r2.2.2),
        CoreMemDesign.edgesV_cons_mk hx hqx (CoreMemDesign.edgesV_cons_mk hy hqy h2), hv2, hm2, fun st hst => ?_⟩
      have hdisj : ∀ u ∈ qx, ∀ u' ∈ qy, u.1 ≠ u'.1 := by
        simp only [List.flatMap_cons] at hnd
        have h3 := (List.nodup_append.mp hnd).2.2
        intro u hu u' hu' he
        exact h3 u'.1 (hny u' hu') u.1 (List.mem_append_left _ (hnx u hu)) he.symm
      show commitNba2 st (qx ++ (qy ++ r2.2.1)) = commitNba2 st (qy ++ (qx ++ r2.2.1))
      rw [← List.append_assoc, ← List.append_assoc, commitNba2_append st (qx ++ qy),
        commitNba2_append st (qy ++ qx), commitNba2_swap hst hdisj]
  | trans h₁₂ _ ih₁ ih₂ =>
      intro hw hnd r h
      obtain ⟨hv, hm, r₁, h₁, hv₁, hm₁, hc₁⟩ := ih₁ hw hnd h
      obtain ⟨-, -, r₂, h₂, hv₂, hm₂, hc₂⟩ := ih₂ (fun p hp => hw p (h₁₂.mem_iff.mpr hp))
        ((List.Perm.flatMap_right _ h₁₂).nodup_iff.mp hnd) h₁
      exact ⟨hv, hm, r₂, h₂, hv₂, hm₂, fun st hst => (hc₂ st hst).trans (hc₁ st hst)⟩

/-- The edge pass reads only the edge processes. -/
theorem CoreMemDesign.edgesV_filter {E : CoreMemDesign} {before after : SvState} {mv : MemV} :
    ∀ (ps : List CoreMemProc) (v : SvState),
      E.edgesV before after v mv ps = E.edgesV before after v mv (ps.filter CoreMemProc.isEdge)
  | [], _ => rfl
  | .edge f :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .assign t e :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .initial b :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .comb b :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .implicit b :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .unsupported k t :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]

/-- **With at most one edge process there is no order to choose**: every permutation gives the same edge pass. -/
theorem CoreMemDesign.edgesV_single {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {ps ps' : List CoreMemProc} (hp : ps.Perm ps') (h1 : (ps.filter CoreMemProc.isEdge).length ≤ 1) :
    E.edgesV before after v mv ps' = E.edgesV before after v mv ps := by
  rw [CoreMemDesign.edgesV_filter ps', CoreMemDesign.edgesV_filter ps]
  have hp' := hp.filter CoreMemProc.isEdge
  generalize ps.filter CoreMemProc.isEdge = a at hp' h1
  generalize ps'.filter CoreMemProc.isEdge = b at hp'
  rcases a with _ | ⟨x, _ | ⟨y, a⟩⟩
  · obtain rfl := List.nil_perm.mp hp'
    rfl
  · obtain rfl := List.singleton_perm.mp hp'
    rfl
  · simp at h1

/-- **THE EDGE ORDER DOES NOT MATTER, under the obligations** (rule 4): for every permutation of the processes, the
edge pass succeeds when the route's (source order) succeeds and commits to the same views. -/
theorem CoreMemDesign.edgesV_order {E : CoreMemDesign} {clk : String} (hO : E.seqOblB clk = true)
    {ps : List CoreMemProc} (hσ : ps.Perm E.processes.toList) {before after v : SvState} {mv : MemV}
    (hv : (v.map Prod.fst).Nodup) {r : ExecV}
    (h : E.edgesV before after v mv E.processes.toList = .ok r) :
    ∃ r', E.edgesV before after v mv ps = .ok r' ∧ commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      commitMemV mv r'.2.2 = commitMemV mv r.2.2 := by
  simp only [CoreMemDesign.seqOblB, Bool.and_eq_true] at hO
  obtain ⟨⟨⟨⟨⟨⟨hdr, -⟩, -⟩, -⟩, -⟩, hord⟩, -⟩ := hO
  simp only [CoreMemDesign.oblDrivers, CoreMemDesign.driven, decide_eq_true_eq] at hdr
  simp only [CoreMemDesign.oblEdgeOrder, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at hord
  rcases hord with h1 | hw
  · exact ⟨r, by rw [CoreMemDesign.edgesV_single hσ.symm h1]; exact h, rfl, rfl⟩
  · obtain ⟨hv1, hm1, r', h', hv1', hm1', hc⟩ := CoreMemDesign.edgesV_perm hσ.symm hw (of_decide_eq_true hdr) h
    exact ⟨r', h', by rw [hv1', hv1]; exact hc v hv, by rw [hm1, hm1']⟩

#print axioms CoreMemDesign.edgesV_order

end LeanModels.Sv.Kernel
