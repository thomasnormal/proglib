import LeanModels.Sv.SeqCycle

/-!
# The obligations of the clocked profile, and the theorems that use them (`LeanModels.Sv.Kernel`)

**Status: derived from the ordinary E route** (part of the clocked tactics' theory, `SeqCycle.lean`).

* `SeqPorts`: the interface of a family member.
* `seqOblI`: the obligations for any number of events, decided: one driver per signal (a memory counts as one signal:
  one writer per memory), the continuous assigns in topological source order on what the route evaluates (`topoC`: a
  compiled expression's identifiers, or for an assign that reads a memory the names `evalV` reads, `readsV`), no
  process writing an input, every event source a one-bit input port, no process reading an event source as data
  (except an edge process its own reset), the edge order irrelevant, no unconverted expression. `seqOblB clk`: their
  single-clock instance (with the clock-specific facts). `SeqDesignI` / `SeqDesign`: the structure judgments
  (instantiation, profile, obligations).
* The theorems that USE the obligations: `settleV_idem` (one settle pass is the fixpoint: no continuous assignment is
  out of date when a slot closes; the route's quiesce loop returns that pass's view, `settleCanonical_seq`),
  `slot_noFollowup` (no process drives an event source, so a slot's first round causes no further event: the route's
  in-slot iteration stops after one round; the frame lemmas `execV_frame`, `edgesV_frame`, `commitNba2_frame`),
  `slotV_eq_slot1V` (the slot is one pass before the edge and one after), `edgesV_order` (every order of the edge
  processes commits to the same views: rule 4).
* **`CoreMemDesign.step_seqI`** (any row, any number of events) and its single-clock corollaries `step_seq`,
  `cycleMV_refines`, `cycle_of_seqProfile`: the refinement theorems, under the obligations: from every coherent state
  with a coherent memory, the route's slots exist, stay coherent, and land exactly on the views the mirror computes.
  The route's slot function is read through `SeqCycleStep.lean` only.
* `SeqProfileI.initialState` (and `SeqProfile.initialState`): under the topological obligation, the route's time-zero
  state on the profile is the canonical quiescent settle of the continuous assigns from the x start
  `CoreMemDesign.initial`; when the view-level pass succeeds it exists and is coherent with a coherent memory, so it
  is one of the run judgment's start states. `initialState_settled` records the same settled view explicitly.
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
  | .aggregateMember base path => base :: PExpr.sigNamesPath path
  | .packageAggElem _ _ index => PExpr.sigNames index
  | .ternary c a b | .partSel c a b => PExpr.sigNames c ++ PExpr.sigNames a ++ PExpr.sigNames b
  | .concat xs | .functionCall _ xs => PExpr.sigNamesList xs
  | .lit _ | .paramRef _ _ | .genvarRef _ | .enumRef _ _ _ | .int _ | .fill _ | .typeBits _ _ | .unsupported _ _ => []

/-- `sigNames` of a list. -/
def _root_.LeanModels.Sv.PExpr.sigNamesList : List PExpr → List String
  | [] => []
  | x :: xs => PExpr.sigNames x ++ PExpr.sigNamesList xs

def _root_.LeanModels.Sv.PExpr.sigNamesOpt : Option PExpr → List String
  | none => []
  | some e => PExpr.sigNames e

def _root_.LeanModels.Sv.PExpr.sigNamesPath :
    List (Option String × Option PExpr) → List String
  | [] => []
  | (_, index) :: rest => PExpr.sigNamesOpt index ++ PExpr.sigNamesPath rest

end

/-! Aggregate selectors retain both the aggregate base and every signal read by
their parser-native index expressions in the clocked obligation read set. -/
#guard PExpr.sigNames (.aggregateMember "state"
    [(some "value", none), (none, some (.ident "sel_i"))]) == ["state", "sel_i"]

mutual

/-- The signal a write target writes (its base name; every leaf of a concatenation). -/
def _root_.LeanModels.Sv.PLhs.baseNames : PLhs → List String
  | .ident n => [n]
  | .bitSel n _ => [n]
  | .partSel n _ _ => [n]
  | .arrayElem n _ => [n]
  | .arrayPart n _ _ _ _ => [n]
  | .aggregateMember n _ => [n]
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
  | .aggregateMember _ path => path.foldl (fun acc step =>
      match step.2 with | some e => acc ++ PExpr.sigNames e | none => acc) []
  | .concat parts => PLhs.indexNamesList parts

/-- `indexNames` of a list. -/
def _root_.LeanModels.Sv.PLhs.indexNamesList : List PLhs → List String
  | [] => []
  | p :: ps => PLhs.indexNames p ++ PLhs.indexNamesList ps

end

mutual

/-- The signals an edge body writes, blocking or nonblocking (base names); a `for` loop writes what its body writes. -/
def _root_.LeanModels.Sv.PStmt.writes : PStmt → List String
  | .nbaAssign t _ => [t]
  | .blockingAssign t _ => [t]
  | .nbaAssignL t _ => PLhs.baseNames t
  | .blockingAssignL t _ => PLhs.baseNames t
  | .ifStmt _ y n => PStmt.writes y ++ PStmt.optWrites n
  | .block body => PStmt.listWrites body
  | .caseStmt _ items d _ _ => PStmt.itemsWrites items ++ PStmt.optWrites d
  | .forLoop _ _ _ _ body => PStmt.writes body
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
  | .forLoop _ _ _ _ body => PStmt.hasBlocking body
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
  | .forLoop _ init condition step body =>
      PExpr.sigNames init ++ PExpr.sigNames condition ++ PExpr.sigNames step ++ PStmt.readNames body
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
  | .aggregateMember .. => []
  | .packageAggElem _ _ index => PExpr.unconverted index
  | .ident _ | .lit _ | .paramRef _ _ | .genvarRef _ | .enumRef _ _ _ | .int _ | .fill _ | .typeBits _ _ => []

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
  | .forLoop _ init condition step body =>
      PExpr.unconverted init ++ PExpr.unconverted condition ++ PExpr.unconverted step ++ PStmt.unconverted body
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
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.unconverted
      | none => []
  | _ => []

/-- The names a process drives. -/
def CoreMemProc.targets : CoreMemProc → List String
  | .assign (.ident n) _ => [n]
  | .edge f => f.body.writes.eraseDups
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.writes.eraseDups
      | none => []
  | _ => []

/-- The names a process reads. -/
def CoreMemProc.reads : CoreMemProc → List String
  | .assign _ v => PExpr.sigNames v
  | .edge f => f.body.readNames
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.readNames
      | none => []
  | _ => []

/-- The asynchronous reset of an edge process, when it has one. -/
def CoreMemProc.reset? : CoreMemProc → Option String
  | .edge f => f.reset
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.reset
      | none => none
  | _ => none

/-- Whether a process is an edge process with a blocking write. -/
def CoreMemProc.blocking : CoreMemProc → Bool
  | .edge f => f.body.hasBlocking
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.hasBlocking
      | none => false
  | _ => false

/-- Whether a process is an edge process (a plain `always` on one clock edge is one, `CoreMemProc.edge?`). -/
def CoreMemProc.isEdge : CoreMemProc → Bool
  | .edge _ => true
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some _ => true
      | none => false
  | _ => false

/-- The names an edge process drives. -/
theorem CoreMemProc.targets_of_edge? {p : CoreMemProc} {f : CoreMemEdge} (h : p.edge? = some f) :
    p.targets = f.body.writes.eraseDups := by
  cases p with
  | edge g =>
      simp only [CoreMemProc.edge?, Option.some.injEq] at h
      subst h
      rfl
  | event evs body =>
      simp only [CoreMemProc.edge?] at h
      simp only [CoreMemProc.targets, h]
  | _ => exact absurd h (by simp [CoreMemProc.edge?])

theorem CoreMemProc.isEdge_of_edge? {p : CoreMemProc} {f : CoreMemEdge} (h : p.edge? = some f) :
    p.isEdge = true := by
  cases p with
  | edge g => rfl
  | event evs body =>
      simp only [CoreMemProc.edge?] at h
      simp only [CoreMemProc.isEdge, h]
  | _ => exact absurd h (by simp [CoreMemProc.edge?])

theorem CoreMemProc.isEdge_of_none {p : CoreMemProc} (h : p.edge? = none) : p.isEdge = false := by
  cases p with
  | edge g => exact absurd h (by simp [CoreMemProc.edge?])
  | event evs body =>
      simp only [CoreMemProc.edge?] at h
      simp only [CoreMemProc.isEdge, h]
  | _ => rfl

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
  | .aggregateMember .. => []
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

/-! In the scalar-only expression fragment, the source-shaped read walker is
 exactly the identifier list of the instantiated expression. -/
theorem CoreMemDesign.readsV_eq_instExpr2_idents_of_pure
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {ctx : Option Nat} {e : PExpr}
    (hmem : LeanModels.Sv.PExpr.hasMemoryRead e = false) :
    E.readsV env elems ctx e =
      (instExpr2 env (E.widthsOf elems) ctx e).idents := by
  cases e <;> simp_all [CoreMemDesign.readsV, CoreMemDesign.readsIdxV,
    LeanModels.Sv.PExpr.hasMemoryRead, instExpr2, Expr2.idents]

/-! The same parser-native closure is available at the stateful scalar
 evaluator used by retained combinational statements. -/
theorem CoreMemDesign.evalScalarLocals_congr_readsV_of_pure
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st st' : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    (hmem : LeanModels.Sv.PExpr.hasMemoryRead e = false)
    (hne : elems ≠ [])
    (h : ∀ x ∈ E.readsV env elems ctx e,
      SvState.lookup (locals ++ E.scalar.view st.scalar) x =
        SvState.lookup (locals ++ E.scalar.view st'.scalar) x) :
    E.evalScalarLocals env elems st ctx locals e =
      E.evalScalarLocals env elems st' ctx locals e := by
  unfold CoreMemDesign.evalScalarLocals
  apply evalPure2_congr
  intro x hx
  have hr : E.readsV env elems ctx e =
      (instExpr2 env (if elems.isEmpty then E.elems else elems) ctx e).idents := by
    simpa [CoreMemDesign.widthsOf, hne] using
      (CoreMemDesign.readsV_eq_instExpr2_idents_of_pure
        (E := E) (env := env) (elems := elems) (ctx := ctx) (e := e) hmem)
  rw [← hr] at hx
  exact h x hx

/-! The same parser-native frame applies to the full expression evaluator on
 pure, function-free expressions. -/
theorem CoreMemDesign.evalExprLocals_congr_readsV_of_pure
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st st' : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    (hmem : LeanModels.Sv.PExpr.hasMemoryRead e = false)
    (hcall : LeanModels.Sv.PExpr.hasFunctionCall e = false)
    (hne : elems ≠ [])
    (h : ∀ x ∈ E.readsV env elems ctx e,
      SvState.lookup (locals ++ E.scalar.view st.scalar) x =
        SvState.lookup (locals ++ E.scalar.view st'.scalar) x) :
    E.evalExprLocals env elems st ctx locals e =
      E.evalExprLocals env elems st' ctx locals e := by
  have hs := CoreMemDesign.evalScalarLocals_congr_readsV_of_pure
    (E := E) (env := env) (elems := elems) (st := st) (st' := st')
    (ctx := ctx) (locals := locals) (e := e) hmem hne h
  cases e <;> simp_all [CoreMemDesign.evalExprLocals, CoreMemDesign.evalAggregateMember,
    CoreMemDesign.evalAggPath, LeanModels.Sv.PExpr.hasMemoryRead,
    LeanModels.Sv.PExpr.hasFunctionCall, CoreMemDesign.evalScalarLocals] <;>
    exact hs

/-! A coherent scalar write is therefore invisible to the full evaluator when
 the parser-native read closure excludes its target. -/
theorem CoreMemDesign.evalExprLocals_setScalarState_of_not_read_pure
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    {n : String} {x : VarId} {v : LVec}
    (hc : E.Coherent st)
    (hx : E.scalar.resolve n = some x)
    (hmem : LeanModels.Sv.PExpr.hasMemoryRead e = false)
    (hcall : LeanModels.Sv.PExpr.hasFunctionCall e = false)
    (hne : elems ≠ [])
    (hread : ∀ y ∈ E.readsV env elems ctx e, y ≠ n) :
    E.evalExprLocals env elems st ctx locals e =
      E.evalExprLocals env elems (E.setScalarState st n v) ctx locals e := by
  apply CoreMemDesign.evalExprLocals_congr_readsV_of_pure hmem hcall hne
  intro y hy
  have hset := (CoreMemDesign.setScalarState_spec hc hx v).1
  rw [hset]
  let lookupAppend : ∀ (a b : SvState) (q : String),
      SvState.lookup (a ++ b) q =
        (SvState.lookup a q).or (SvState.lookup b q) := by
    intro a
    induction a with
    | nil => intro b q; rfl
    | cons kv rest ih =>
        intro b q
        obtain ⟨k, w⟩ := kv
        simp only [List.cons_append, SvState.lookup]
        split
        · rfl
        · simp only [ih]
  rw [lookupAppend, lookupAppend]
  have hny : n ≠ y := Ne.symm (hread y hy)
  by_cases hlocal : SvState.lookup locals y = none
  · simp [hlocal, SvState.lookup_set, hny]
  · simp [hlocal, SvState.lookup_set, hny]

/-! Two coherent scalar writes compose through the same full evaluator frame.
 The state order is explicit, so this does not claim that the writes commute. -/
theorem CoreMemDesign.evalExprLocals_setScalarState_two_of_not_read_pure
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    {n m : String} {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hmem : LeanModels.Sv.PExpr.hasMemoryRead e = false)
    (hcall : LeanModels.Sv.PExpr.hasFunctionCall e = false)
    (hne : elems ≠ [])
    (hreadN : ∀ y ∈ E.readsV env elems ctx e, y ≠ n)
    (hreadM : ∀ y ∈ E.readsV env elems ctx e, y ≠ m) :
    E.evalExprLocals env elems st ctx locals e =
      E.evalExprLocals env elems (E.setScalarState (E.setScalarState st n vN) m vM)
        ctx locals e := by
  calc
    E.evalExprLocals env elems st ctx locals e =
        E.evalExprLocals env elems (E.setScalarState st n vN) ctx locals e :=
      CoreMemDesign.evalExprLocals_setScalarState_of_not_read_pure
        hc hxN hmem hcall hne hreadN
    _ = E.evalExprLocals env elems
        (E.setScalarState (E.setScalarState st n vN) m vM) ctx locals e :=
      CoreMemDesign.evalExprLocals_setScalarState_of_not_read_pure
        (CoreMemDesign.setScalarState_spec hc hxN vN).2 hxM hmem hcall hne hreadM

/-! The parser-native read frame makes the evaluator result independent of the
 order of two scalar writes that are both outside the expression's read set.
This compares the real stateful evaluator at the two concrete write orders;
it does not identify the updated states themselves. -/
theorem CoreMemDesign.evalExprLocals_setScalarState_two_order_frame
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    {n m : String} {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hmem : LeanModels.Sv.PExpr.hasMemoryRead e = false)
    (hcall : LeanModels.Sv.PExpr.hasFunctionCall e = false)
    (hne : elems ≠ [])
    (hreadN : ∀ y ∈ E.readsV env elems ctx e, y ≠ n)
    (hreadM : ∀ y ∈ E.readsV env elems ctx e, y ≠ m) :
    E.evalExprLocals env elems
        (E.setScalarState (E.setScalarState st n vN) m vM) ctx locals e =
      E.evalExprLocals env elems
        (E.setScalarState (E.setScalarState st m vM) n vN) ctx locals e := by
  calc
    E.evalExprLocals env elems
        (E.setScalarState (E.setScalarState st n vN) m vM) ctx locals e =
        E.evalExprLocals env elems st ctx locals e :=
      (CoreMemDesign.evalExprLocals_setScalarState_two_of_not_read_pure
        hc hxN hxM hmem hcall hne hreadN hreadM).symm
    _ = E.evalExprLocals env elems
        (E.setScalarState (E.setScalarState st m vM) n vN) ctx locals e :=
      CoreMemDesign.evalExprLocals_setScalarState_two_of_not_read_pure
        hc hxM hxN hmem hcall hne hreadM hreadN

/-! The pair form exposes both evaluator equalities needed by a two-cursor
diamond.  Each expression has its own parser-native read exclusion, while the
underlying write orders remain the actual `setScalarState` calls. -/
theorem CoreMemDesign.evalExprLocals_two_expr_setScalarState_order_frame
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st : CoreMemState} {ctxN ctxM : Option Nat} {locals : SvState}
    {eN eM : PExpr} {n m : String} {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hmemN : LeanModels.Sv.PExpr.hasMemoryRead eN = false)
    (hcallN : LeanModels.Sv.PExpr.hasFunctionCall eN = false)
    (hmemM : LeanModels.Sv.PExpr.hasMemoryRead eM = false)
    (hcallM : LeanModels.Sv.PExpr.hasFunctionCall eM = false)
    (hne : elems ≠ [])
    (hreadMN : ∀ y ∈ E.readsV env elems ctxM eM, y ≠ n)
    (hreadMM : ∀ y ∈ E.readsV env elems ctxM eM, y ≠ m)
    (hreadNN : ∀ y ∈ E.readsV env elems ctxN eN, y ≠ n)
    (hreadNM : ∀ y ∈ E.readsV env elems ctxN eN, y ≠ m) :
    E.evalExprLocals env elems
        (E.setScalarState (E.setScalarState st n vN) m vM) ctxM locals eM =
      E.evalExprLocals env elems
        (E.setScalarState (E.setScalarState st m vM) n vN) ctxM locals eM ∧
    E.evalExprLocals env elems
        (E.setScalarState (E.setScalarState st n vN) m vM) ctxN locals eN =
      E.evalExprLocals env elems
        (E.setScalarState (E.setScalarState st m vM) n vN) ctxN locals eN := by
  constructor
  · exact CoreMemDesign.evalExprLocals_setScalarState_two_order_frame
      hc hxN hxM hmemM hcallM hne hreadMN hreadMM
  · exact CoreMemDesign.evalExprLocals_setScalarState_two_order_frame
      hc hxN hxM hmemN hcallN hne hreadNN hreadNM

/-! A coherent scalar write changes the materialized view only at its target
 name. -/
theorem CoreMemDesign.setScalarState_view_lookup_of_ne
    {E : CoreMemDesign} {st : CoreMemState} {n y : String}
    {x : VarId} {v : LVec}
    (hc : E.Coherent st)
    (hx : E.scalar.resolve n = some x)
    (hne : n ≠ y) :
    SvState.lookup (E.scalar.view (E.setScalarState st n v).scalar) y =
      SvState.lookup (E.scalar.view st.scalar) y := by
  rw [(CoreMemDesign.setScalarState_spec hc hx v).1]
  exact SvState.lookup_set_ne _ _ hne

/-! The lookup frame composes through two ordered coherent scalar writes. -/
theorem CoreMemDesign.setScalarState_view_lookup_two_of_ne
    {E : CoreMemDesign} {st : CoreMemState} {n m y : String}
    {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hneN : n ≠ y)
    (hneM : m ≠ y) :
    SvState.lookup
        (E.scalar.view (E.setScalarState (E.setScalarState st n vN) m vM).scalar) y =
      SvState.lookup (E.scalar.view st.scalar) y := by
  rw [CoreMemDesign.setScalarState_view_lookup_of_ne
    (CoreMemDesign.setScalarState_spec hc hxN vN).2 hxM hneM]
  exact CoreMemDesign.setScalarState_view_lookup_of_ne hc hxN hneN

/-! The two concrete write orders agree on every parser-native read after the
same local bindings are prepended.  This is the lookup frame consumed by the
stateful expression evaluator. -/
theorem CoreMemDesign.setScalarState_two_order_read_lookup
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st : CoreMemState} {ctx : Option Nat} {locals : SvState} {e : PExpr}
    {n m : String} {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hreadN : ∀ y ∈ E.readsV env elems ctx e, y ≠ n)
    (hreadM : ∀ y ∈ E.readsV env elems ctx e, y ≠ m) :
    ∀ y ∈ E.readsV env elems ctx e,
      SvState.lookup
          (locals ++ E.scalar.view (E.setScalarState (E.setScalarState st n vN) m vM).scalar) y =
        SvState.lookup
          (locals ++ E.scalar.view (E.setScalarState (E.setScalarState st m vM) n vN).scalar) y := by
  intro y hy
  have hleft := CoreMemDesign.setScalarState_view_lookup_two_of_ne
    (vN := vN) (vM := vM) hc hxN hxM
    (Ne.symm (hreadN y hy)) (Ne.symm (hreadM y hy))
  have hright := CoreMemDesign.setScalarState_view_lookup_two_of_ne
    (vN := vM) (vM := vN) hc hxM hxN
    (Ne.symm (hreadM y hy)) (Ne.symm (hreadN y hy))
  let lookupAppend : ∀ (a b : SvState) (q : String),
      SvState.lookup (a ++ b) q =
        (SvState.lookup a q).or (SvState.lookup b q) := by
    intro a
    induction a with
    | nil => intro b q; rfl
    | cons kv rest ih =>
        intro b q
        obtain ⟨k, w⟩ := kv
        simp only [List.cons_append, SvState.lookup]
        split
        · rfl
        · simp only [ih]
  rw [lookupAppend, lookupAppend, hleft, hright]

/-! Two distinct scalar writes commute once the cross-slot scalar values are
 explicitly equal.  This is the concrete cache-level frame used before any
 scheduler diamond is stated. -/
theorem CoreMemDesign.setScalarState_commute_of_cross_values
    {E : CoreMemDesign} {st : CoreMemState}
    {n m : String} {xN xM : VarId} {vN vM : LVec}
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hdecl : xN.decl ≠ xM.decl)
    (hvalM : (E.setScalarState st n vN).scalar xM = st.scalar xM)
    (hvalN : (E.setScalarState st m vM).scalar xN = st.scalar xN) :
    E.setScalarState (E.setScalarState st n vN) m vM =
      E.setScalarState (E.setScalarState st m vM) n vN := by
  have hvalM' := hvalM
  have hvalN' := hvalN
  simp only [CoreMemDesign.setScalarState, hxN] at hvalM'
  simp only [CoreMemDesign.setScalarState, hxM] at hvalN'
  simp only [Array.set!] at hvalM' hvalN'
  simp only [CoreMemDesign.setScalarState, hxN, hxM]
  simp only [Array.set!]
  rw [Array.setIfInBounds_comm _ _ hdecl]
  rw [hvalM', hvalN']

theorem CoreMemDesign.setScalarState_scalar_of_decl_ne
    {E : CoreMemDesign} {st : CoreMemState}
    {n m : String} {xN xM : VarId} {v : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hdecl : xN.decl ≠ xM.decl) :
    (E.setScalarState st n v).scalar xM = st.scalar xM := by
  obtain ⟨dcM, hdcM, -, -, -⟩ := Elab.resolve_some hxM
  obtain ⟨hpathM, -⟩ := Elab.declOf_some hdcM
  cases xM with
  | mk path decl =>
      have hpath0 : path = [] := by
        simpa using congrArg VarId.path hpathM
      subst path
      unfold CoreMemDesign.setScalarState
      rw [hxN, hc.store]
      simp [CoreMemDesign.scalarStore, hdecl]

/-! Coherence now discharges the cross-slot value conditions of the concrete
 write commutation theorem. -/
theorem CoreMemDesign.setScalarState_commute_of_coherent_decl_ne
    {E : CoreMemDesign} {st : CoreMemState}
    {n m : String} {xN xM : VarId} {vN vM : LVec}
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hdecl : xN.decl ≠ xM.decl) :
    E.setScalarState (E.setScalarState st n vN) m vM =
      E.setScalarState (E.setScalarState st m vM) n vN := by
  apply CoreMemDesign.setScalarState_commute_of_cross_values hxN hxM hdecl
  · exact CoreMemDesign.setScalarState_scalar_of_decl_ne hc hxN hxM hdecl
  · exact CoreMemDesign.setScalarState_scalar_of_decl_ne hc hxM hxN (Ne.symm hdecl)

theorem CoreMemDesign.evalScalarV_congr_readsV_of_pure
    {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {v v' : SvState} {ctx : Option Nat} {e : PExpr}
    (hmem : LeanModels.Sv.PExpr.hasMemoryRead e = false)
    (h : ∀ x ∈ E.readsV env elems ctx e,
      SvState.lookup v x = SvState.lookup v' x) :
    E.evalScalarV env elems v ctx e = E.evalScalarV env elems v' ctx e := by
  apply CoreMemDesign.evalScalarV_congr
  rw [← CoreMemDesign.readsV_eq_instExpr2_idents_of_pure hmem]
  exact h

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
  | ctx, .typeBits _ _, h => by
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
  | ctx, .aggregateMember _ _, _ => by
      simp [CoreMemDesign.evalV, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf, instExpr2]
  | ctx, .packageAggElem _ _ _, h => by
      simp only [CoreMemDesign.readsV] at h
      simp only [CoreMemDesign.evalV]
      exact CoreMemDesign.evalScalarV_congr h
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
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.nbaWhole
      | none => true
  | _ => true

/-! Memory-aware NBA admission.  The existing `nbaWhole` predicate covers
whole scalar writes.  This companion admits one-rank memory-element writes and
the procedural loops whose body has only those nonblocking writes. -/
mutual
def _root_.LeanModels.Sv.PStmt.nbaMemory : PStmt → Bool
  | .nbaAssignL (.arrayElem _ [_]) _ => true
  | .ifStmt _ y n => PStmt.nbaMemory y && PStmt.optNbaMemory n
  | .block body => PStmt.listNbaMemory body
  | .caseStmt _ items d _ _ => PStmt.itemsNbaMemory items && PStmt.optNbaMemory d
  | .forLoop _ _ _ _ body => PStmt.loopNbaMemory body
  | _ => false
termination_by structural s => s

def _root_.LeanModels.Sv.PStmt.optNbaMemory : Option PStmt → Bool
  | none => true
  | some s => PStmt.nbaMemory s
termination_by structural o => o

def _root_.LeanModels.Sv.PStmt.listNbaMemory : List PStmt → Bool
  | [] => true
  | s :: ss => PStmt.nbaMemory s && PStmt.listNbaMemory ss
termination_by structural xs => xs

def _root_.LeanModels.Sv.PStmt.itemsNbaMemory : List (List PExpr × PStmt) → Bool
  | [] => true
  | (_, b) :: rest => PStmt.nbaMemory b && PStmt.itemsNbaMemory rest
termination_by structural xs => xs

def _root_.LeanModels.Sv.PStmt.loopNbaMemory : PStmt → Bool
  | .nbaAssignL (.arrayElem _ [_]) _ => true
  | .ifStmt _ y n => PStmt.loopNbaMemory y && PStmt.optLoopNbaMemory n
  | .block body => PStmt.listLoopNbaMemory body
  | .caseStmt _ items d _ _ => PStmt.itemsLoopNbaMemory items && PStmt.optLoopNbaMemory d
  | _ => false
termination_by structural s => s

def _root_.LeanModels.Sv.PStmt.optLoopNbaMemory : Option PStmt → Bool
  | none => true
  | some s => PStmt.loopNbaMemory s
termination_by structural o => o

def _root_.LeanModels.Sv.PStmt.listLoopNbaMemory : List PStmt → Bool
  | [] => true
  | s :: ss => PStmt.loopNbaMemory s && PStmt.listLoopNbaMemory ss
termination_by structural xs => xs

def _root_.LeanModels.Sv.PStmt.itemsLoopNbaMemory : List (List PExpr × PStmt) → Bool
  | [] => true
  | (_, b) :: rest => PStmt.loopNbaMemory b && PStmt.itemsLoopNbaMemory rest
termination_by structural xs => xs
end

def CoreMemProc.nbaMemoryP : CoreMemProc → Bool
  | .edge f => f.body.nbaMemory
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.nbaMemory
      | none => true
  | _ => true

def CoreMemProc.nbaEdgeP (p : CoreMemProc) : Bool := p.nbaWholeP || p.nbaMemoryP

/-! A procedural memory loop's body is in the evaluator's loop-body profile.
    The statement is about `loopNbaMemory`, which excludes nested loops. -/
mutual
theorem PStmt.loopNbaMemory_loopBodyB : ∀ (s : PStmt), s.loopNbaMemory = true → s.loopBodyB = true
  | .nbaAssignL (.arrayElem _ indices) _, h => by
      cases indices with
      | nil => simp [PStmt.loopNbaMemory] at h
      | cons _ rest =>
          cases rest with
          | nil => simp [PStmt.loopNbaMemory, PStmt.loopBodyB]
          | cons _ _ => simp [PStmt.loopNbaMemory] at h
  | .ifStmt _ y n, h => by
      simp only [PStmt.loopNbaMemory, Bool.and_eq_true] at h
      simp only [PStmt.loopBodyB, Bool.and_eq_true]
      exact ⟨PStmt.loopNbaMemory_loopBodyB y h.1, PStmt.optLoopNbaMemory_loopBodyB n h.2⟩
  | .block body, h => by
      simp only [PStmt.loopNbaMemory] at h
      simpa [PStmt.loopBodyB] using PStmt.listLoopNbaMemory_loopBodyB body h
  | .caseStmt _ items d _ _, h => by
      simp only [PStmt.loopNbaMemory, Bool.and_eq_true] at h
      simp only [PStmt.loopBodyB, Bool.and_eq_true]
      exact ⟨PStmt.itemsLoopNbaMemory_loopBodyB items h.1, PStmt.optLoopNbaMemory_loopBodyB d h.2⟩
  | .nbaAssign .., h => by simp [PStmt.loopNbaMemory] at h
  | .nbaAssignL (.ident _) _, h => by simp [PStmt.loopNbaMemory] at h
  | .nbaAssignL (.bitSel _ _) _, h => by simp [PStmt.loopNbaMemory] at h
  | .nbaAssignL (.partSel _ _ _) _, h => by simp [PStmt.loopNbaMemory] at h
  | .nbaAssignL (.arrayPart _ _ _ _ _) _, h => by simp [PStmt.loopNbaMemory] at h
  | .nbaAssignL (.aggregateMember _ _) _, h => by simp [PStmt.loopNbaMemory] at h
  | .nbaAssignL (.concat _) _, h => by simp [PStmt.loopNbaMemory] at h
  | .blockingAssign .., h => by simp [PStmt.loopNbaMemory] at h
  | .blockingAssignL .., h => by simp [PStmt.loopNbaMemory] at h
  | .forLoop .., h => by simp [PStmt.loopNbaMemory] at h
  | .localDecl .., h => by simp [PStmt.loopNbaMemory] at h
  | .automaticDecl .., h => by simp [PStmt.loopNbaMemory] at h
  | .unsupported .., h => by simp [PStmt.loopNbaMemory] at h

theorem PStmt.optLoopNbaMemory_loopBodyB : ∀ (o : Option PStmt),
    PStmt.optLoopNbaMemory o = true → PStmt.optLoopBodyB o = true
  | none, _ => rfl
  | some s, h => by
      simpa [PStmt.optLoopNbaMemory, PStmt.optLoopBodyB] using PStmt.loopNbaMemory_loopBodyB s h

theorem PStmt.listLoopNbaMemory_loopBodyB : ∀ (xs : List PStmt),
    PStmt.listLoopNbaMemory xs = true → PStmt.listLoopBodyB xs = true
  | [], _ => rfl
  | s :: ss, h => by
      simp only [PStmt.listLoopNbaMemory, Bool.and_eq_true] at h
      simp only [PStmt.listLoopBodyB, Bool.and_eq_true]
      exact ⟨PStmt.loopNbaMemory_loopBodyB s h.1, PStmt.listLoopNbaMemory_loopBodyB ss h.2⟩

theorem PStmt.itemsLoopNbaMemory_loopBodyB : ∀ (xs : List (List PExpr × PStmt)),
    PStmt.itemsLoopNbaMemory xs = true → PStmt.itemsLoopBodyB xs = true
  | [], _ => rfl
  | (_, s) :: ss, h => by
      simp only [PStmt.itemsLoopNbaMemory, Bool.and_eq_true] at h
      simp only [PStmt.itemsLoopBodyB, Bool.and_eq_true]
      exact ⟨PStmt.loopNbaMemory_loopBodyB s h.1, PStmt.itemsLoopNbaMemory_loopBodyB ss h.2⟩
end

def CoreMemDesign.oblEdgeOrderMemory (E : CoreMemDesign) : Bool :=
  let edges := E.processes.toList.filter CoreMemProc.isEdge
  decide (edges.length ≤ 1) || E.processes.toList.all CoreMemProc.nbaEdgeP

theorem CoreMemProc.nbaWholeP_of_edge? {p : CoreMemProc} {f : CoreMemEdge} (h : p.edge? = some f) :
    p.nbaWholeP = f.body.nbaWhole := by
  cases p with
  | edge g =>
      simp only [CoreMemProc.edge?, Option.some.injEq] at h
      subst h
      rfl
  | event evs body =>
      simp only [CoreMemProc.edge?] at h
      simp only [CoreMemProc.nbaWholeP, h]
  | _ => exact absurd h (by simp [CoreMemProc.edge?])

theorem CoreMemProc.nbaWholeP_of_none {p : CoreMemProc} (h : p.edge? = none) : p.nbaWholeP = true := by
  cases p with
  | edge g => exact absurd h (by simp [CoreMemProc.edge?])
  | event evs body =>
      simp only [CoreMemProc.edge?] at h
      simp only [CoreMemProc.nbaWholeP, h]
  | _ => rfl

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

theorem CoreMemDesign.oblEdgeOrderMemory_of_oblEdgeOrder {E : CoreMemDesign}
    (h : E.oblEdgeOrder = true) : E.oblEdgeOrderMemory = true := by
  simp only [CoreMemDesign.oblEdgeOrder, CoreMemDesign.oblEdgeOrderMemory,
    Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by
      simp only [List.all_eq_true] at h
      simp only [List.all_eq_true]
      intro i hi
      simp only [CoreMemProc.nbaEdgeP, Bool.or_eq_true]
      exact Or.inl (h i hi))

/-- No expression of a process holds a node ingestion kept unconverted. -/
def CoreMemDesign.oblConverted (E : CoreMemDesign) : Bool :=
  E.processes.toList.all fun p => p.unconverted.isEmpty

/-- The clock is an input port. -/
def CoreMemDesign.oblClockInput (E : CoreMemDesign) (clk : String) : Bool :=
  E.inputNamesL.contains clk

/-- No process drives an input port. -/
def CoreMemDesign.oblInputsUndriven (E : CoreMemDesign) : Bool := E.driven.all fun t => !E.inputNamesL.contains t

/-- Every event source is a one-bit input port. -/
def CoreMemDesign.oblSources (E : CoreMemDesign) : Bool := E.sources.all fun s => E.inputPorts.contains (s, 1)

/-- A process reads no event source as data, except an edge process its own asynchronous reset. -/
def CoreMemProc.sourceReadOk (srcs : List String) : CoreMemProc → Bool
  | .assign _ v => (PExpr.sigNames v).all fun x => !srcs.contains x
  | .edge f => f.body.readNames.all fun x => !srcs.contains x || f.reset == some x
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.readNames.all fun x => !srcs.contains x || f.reset == some x
      | none => true
  | _ => true

/-- No process reads an event source as data, except an edge process its own asynchronous reset. -/
def CoreMemDesign.oblNoSourceRead (E : CoreMemDesign) : Bool :=
  E.processes.toList.all (CoreMemProc.sourceReadOk E.sources)

/-- **The obligations of the clocked profile, for any number of events**, decided:
* one driver per signal: the base names the processes write are pairwise distinct across processes;
* the continuous assigns in topological source order on the expressions the route evaluates (`topoC`): then one settle
  pass is the fixpoint (`settleV_idem`), so the route's quiesce loop over the region returns that pass's view
  (`settleCanonical_seq`) and no assign is out of date when a slot closes (§4.5, §10.3; the condition U1 violates);
* every event source (every clock, either edge, and every asynchronous reset) is a one-bit input port (`oblSources`)
  and no process drives an input (`oblInputsUndriven`): so no edge is ever caused inside a slot (not across rounds, not
  inside one nonblocking commit, not inside one blocking sequence) and the route's in-slot iteration stops after its
  first round (`slot_noFollowup`);
* no process reads an event source as data, except an edge process its own asynchronous reset (`oblNoSourceRead`):
  with the input discipline (`Separated`) a process woken in an instant reads no signal that moves in it, except the
  reset that woke it (the reason the route's row resolution is the standard's only one, §4.7);
* the edge order is irrelevant: either every edge body writes whole signals with nonblocking assignments only (then
  each body reads the pre-edge view and the queues commit to disjoint signals: `edgesV_perm`) or there is at most one
  edge process (no order to choose: `edgesV_single`); this covers coincident events of several clocks;
* no expression of a process holds a node ingestion kept unconverted (the route refuses it when evaluated).
Under them the route's choices are proved harmless (rule 4's cheap sufficient conditions): its quiesce loops stop after
their first round, and its source order of the edge processes does not change the commit (`edgesV_order`). That
`step` is every legal schedule of a scheduler of §4 is the semantics lane's U3. -/
def CoreMemDesign.seqOblI (E : CoreMemDesign) : Bool :=
  E.oblDrivers && E.topoC && E.oblInputsUndriven && E.oblSources && E.oblNoSourceRead && E.oblEdgeOrder &&
    E.oblConverted

/-- The obligations, one by one. -/
theorem CoreMemDesign.seqOblI_spec {E : CoreMemDesign} (h : E.seqOblI = true) :
    E.oblDrivers = true ∧ E.topoC = true ∧ E.oblInputsUndriven = true ∧ E.oblSources = true ∧
      E.oblNoSourceRead = true ∧ E.oblEdgeOrder = true ∧ E.oblConverted = true := by
  simp only [CoreMemDesign.seqOblI, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- **The obligations of the single-clock profile**: the instant obligations, and for the one clock `clk`: no process
drives it or reads it, an asynchronous reset is an input other than it, it is an input port. -/
def CoreMemDesign.seqOblB (E : CoreMemDesign) (clk : String) : Bool :=
  E.seqOblI && E.oblNoInputWrite clk && E.oblNoClockRead clk && E.oblReset clk && E.oblClockInput clk

/-- The single-clock obligations include the instant obligations. -/
theorem CoreMemDesign.seqOblB_I {E : CoreMemDesign} {clk : String} (h : E.seqOblB clk = true) : E.seqOblI = true := by
  simp only [CoreMemDesign.seqOblB, Bool.and_eq_true] at h
  exact h.1.1.1.1

/-- The single-clock obligations, one by one. -/
theorem CoreMemDesign.seqOblB_spec {E : CoreMemDesign} {clk : String} (h : E.seqOblB clk = true) :
    E.seqOblI = true ∧ E.oblNoInputWrite clk = true ∧ E.oblNoClockRead clk = true ∧ E.oblReset clk = true ∧
      E.oblClockInput clk = true := by
  simp only [CoreMemDesign.seqOblB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **The structure of a clocked family member**, single clock: it instantiates, in the single-clock profile at `clk`,
with its obligations. -/
def SeqDesign (r : Res CoreMemDesign) (clk : String) : Prop :=
  ∃ E, r = .ok E ∧ E.SeqProfile clk ∧ E.seqOblB clk = true

/-- **The structure of a clocked family member, any number of events** (the instant view's): it instantiates, in the
instant profile, with the instant obligations. -/
def SeqDesignI (r : Res CoreMemDesign) : Prop :=
  ∃ E, r = .ok E ∧ E.SeqProfileI ∧ E.seqOblI = true

/-- A single-clock structure is an instant structure. -/
theorem SeqDesign.toI {r : Res CoreMemDesign} {clk : String} (h : SeqDesign r clk) : SeqDesignI r := by
  obtain ⟨E, hr, hP, hO⟩ := h
  exact ⟨E, hr, hP.toSeqProfileI, CoreMemDesign.seqOblB_I hO⟩

/-- An input port's name is an input name. -/
theorem CoreMemDesign.inputNamesL_of_ports {E : CoreMemDesign} {s : String} {w : Nat}
    (h : (s, w) ∈ E.inputPorts) : s ∈ E.inputNamesL := by
  simp only [CoreMemDesign.inputPorts, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨dc, hdc, hin, rfl, -⟩ := h
  simp only [CoreMemDesign.inputNamesL, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq]
  exact ⟨dc, hdc, hin, rfl⟩

/-- Under the obligations an event source is a one-bit input port. -/
theorem CoreMemDesign.source_port {E : CoreMemDesign} (hO : E.seqOblI = true) {s : String} (hs : s ∈ E.sources) :
    (s, 1) ∈ E.inputPorts := by
  have h := (CoreMemDesign.seqOblI_spec hO).2.2.2.1
  simp only [CoreMemDesign.oblSources, List.all_eq_true, List.contains_iff_mem] at h
  exact h s hs

/-- Under the obligations no process drives an event source. -/
theorem CoreMemDesign.source_undriven {E : CoreMemDesign} (hO : E.seqOblI = true) {s : String}
    (hs : s ∈ E.sources) : s ∉ E.driven := by
  intro hd
  have h := (CoreMemDesign.seqOblI_spec hO).2.2.1
  simp only [CoreMemDesign.oblInputsUndriven, List.all_eq_true, Bool.not_eq_true', List.contains_eq_any_beq,
    List.any_eq_false, beq_iff_eq] at h
  exact h s hd s (CoreMemDesign.inputNamesL_of_ports (CoreMemDesign.source_port hO hs)) rfl

/-- An edge process's clock and reset are event sources. -/
theorem CoreMemDesign.clock_mem_sources {E : CoreMemDesign} {f : CoreMemEdge}
    (hf : f ∈ E.edgeProcs) : f.clock ∈ E.sources := by
  simp only [CoreMemDesign.sources, List.mem_map]
  exact ⟨f.clockEvent, CoreMemDesign.mem_events.mpr ⟨f, hf, by simp [CoreMemEdge.events]⟩, rfl⟩

theorem CoreMemDesign.reset_mem_sources {E : CoreMemDesign} {f : CoreMemEdge}
    (hf : f ∈ E.edgeProcs) {r : String} (hr : f.reset = some r) : r ∈ E.sources := by
  simp only [CoreMemDesign.sources, List.mem_map]
  refine ⟨⟨r, if f.resetHigh then .posedge else .negedge⟩, CoreMemDesign.mem_events.mpr ⟨f, hf, ?_⟩, rfl⟩
  simp [CoreMemEdge.events, CoreMemEdge.resetEvent?, hr]


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
      | primitive _ _ _ => simp [CoreMemDesign.settleRaw] at h
      | initial _ => simp [CoreMemDesign.settleRaw] at h
      | comb _ => simp [CoreMemDesign.settleRaw] at h
      | implicit _ => simp [CoreMemDesign.settleRaw] at h
      | latch _ => simp [CoreMemDesign.settleRaw] at h
      | event _ _ =>
          simp only [CoreMemDesign.settleRaw] at h
          exact CoreMemDesign.settleRaw_frame rest (idx + 1) r r' h x (by simpa [assignTargets] using hx)
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
      | primitive _ _ _ => simp [CoreMemDesign.settleRaw] at h
      | initial _ => simp [CoreMemDesign.settleRaw] at h
      | comb _ => simp [CoreMemDesign.settleRaw] at h
      | implicit _ => simp [CoreMemDesign.settleRaw] at h
      | latch _ => simp [CoreMemDesign.settleRaw] at h
      | event _ _ =>
          simp only [CoreMemDesign.settleRaw] at h
          obtain ⟨r2', h2, hfin⟩ := CoreMemDesign.settleRaw_agree rest (idx + 1) r1 r2 r1' ht.2
            (fun x hx => hag x (by simpa [assignTargets] using hx)) h
          exact ⟨r2', by simp [CoreMemDesign.settleRaw, h2], hfin⟩
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
theorem CoreMemDesign.matV_commit_of_slot {E : CoreMemDesign} (hP : E.SeqProfileI)
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
  obtain ⟨st2, -, hv2, hc2, -⟩ := CoreMemDesign.runEdges_V hP.names hP.four
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
theorem CoreMemDesign.slotV_eq_slot1V {E : CoreMemDesign} (hP : E.SeqProfileI)
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
      E.execV E.env v mv b = .ok (v', q, mq) → v' = v ∧ (∀ u ∈ q, u.1 ∈ b.writes) ∧ mq = []
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
      have hdflt : ∀ r, E.execOptV E.env v mv d = .ok r → r.1 = v ∧ (∀ u ∈ r.2.1, u.1 ∈ PStmt.optWrites d) ∧ r.2.2 = [] := by
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
      have hitems : ∀ sv res, E.execItemsV E.env v mv sv mode items (E.execOptV E.env v mv d) = .ok res →
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
      E.execListV E.env v mv bs = .ok (v', q, mq) → v' = v ∧ (∀ u ∈ q, u.1 ∈ PStmt.listWrites bs) ∧ mq = []
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
      E.execItemsV E.env v mv sv mode items dflt = .ok res →
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

theorem CoreMemDesign.edgesV_cons_mk_local {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {p : CoreMemProc} {rest : List CoreMemProc} {q : NbaQueue2} {mq : MemQV} {rr : ExecV}
    (h1 : E.edgesV before after v mv rest = .ok rr)
    (he : p.edge? = none ∧ q = [] ∧ mq = [] ∨
      ∃ f, p.edge? = some f ∧ f.fires before after = true ∧ E.execV E.env v mv f.body = .ok (v, q, mq)) :
    E.edgesV before after v mv (p :: rest) = .ok (rr.1, q ++ rr.2.1, mq ++ rr.2.2) := by
  rcases he with ⟨hnone, rfl, rfl⟩ | ⟨f, hpe, hf, hb⟩
  · rw [CoreMemDesign.edgesV_cons_none hnone]
    simpa using h1
  · rw [CoreMemDesign.edgesV_cons_some hpe]
    simp [hpe, hf, hb, h1]

/-- Two enabled edge processes with scalar or memory NBAs commute over a fixed
continuation.  The evaluator results are supplied at the real `execV` boundary. -/
theorem CoreMemDesign.edgesV_swap_local {E : CoreMemDesign}
    {before after v : SvState} {mv : MemV} {p q : CoreMemProc} {rest : List CoreMemProc}
    {qp qq qr : NbaQueue2} {mp mq mr : MemQV} {rv : SvState}
    (hp : ∃ f, p.edge? = some f ∧ f.fires before after = true ∧ E.execV E.env v mv f.body = .ok (v, qp, mp))
    (hq : ∃ f, q.edge? = some f ∧ f.fires before after = true ∧ E.execV E.env v mv f.body = .ok (v, qq, mq))
    (hr : E.edgesV before after v mv rest = .ok (rv, qr, mr))
    (hdisjS : ∀ u ∈ qp, ∀ u' ∈ qq, u.1 ≠ u'.1)
    (hdisjM : ∀ u ∈ mp, ∀ u' ∈ mq, u.1 ≠ u'.1)
    (hnd : (v.map Prod.fst).Nodup) :
    ∃ r₁ r₂,
      E.edgesV before after v mv (p :: q :: rest) = .ok r₁ ∧
      E.edgesV before after v mv (q :: p :: rest) = .ok r₂ ∧
      r₁.1 = r₂.1 ∧ commitNba2 v r₁.2.1 = commitNba2 v r₂.2.1 ∧
        commitMemV mv r₁.2.2 = commitMemV mv r₂.2.2 := by
  obtain ⟨fp, hp, hfp, hbp⟩ := hp
  obtain ⟨fq, hq, hfq, hbq⟩ := hq
  let r₁ : ExecV := (rv, qp ++ qq ++ qr, mp ++ mq ++ mr)
  let r₂ : ExecV := (rv, qq ++ qp ++ qr, mq ++ mp ++ mr)
  have h₁ : E.edgesV before after v mv (p :: q :: rest) = .ok r₁ := by
    have hqrest := CoreMemDesign.edgesV_cons_mk_local hr
      (Or.inr ⟨fq, hq, hfq, hbq⟩)
    simpa [r₁] using CoreMemDesign.edgesV_cons_mk_local hqrest
      (Or.inr ⟨fp, hp, hfp, hbp⟩)
  have h₂ : E.edgesV before after v mv (q :: p :: rest) = .ok r₂ := by
    have hprest := CoreMemDesign.edgesV_cons_mk_local hr
      (Or.inr ⟨fp, hp, hfp, hbp⟩)
    simpa [r₂] using CoreMemDesign.edgesV_cons_mk_local hprest
      (Or.inr ⟨fq, hq, hfq, hbq⟩)
  refine ⟨r₁, r₂, h₁, h₂, ?_, ?_, ?_⟩
  · rfl
  · simp only [r₁, r₂]
    calc
      commitNba2 v (qp ++ qq ++ qr) = commitNba2 (commitNba2 v (qp ++ qq)) qr := by
        rw [commitNba2_append]
      _ = commitNba2 (commitNba2 v (qq ++ qp)) qr := by
        rw [commitNba2_swap hnd (fun u hu u' hu' => Or.inl (hdisjS u hu u' hu'))]
      _ = commitNba2 v (qq ++ qp ++ qr) := by
        symm
        rw [commitNba2_append]
  · simp only [r₁, r₂]
    calc
      commitMemV mv (mp ++ mq ++ mr) = commitMemV (commitMemV mv (mp ++ mq)) mr := by
        rw [commitMemV_append]
      _ = commitMemV (commitMemV mv (mq ++ mp)) mr := by
        rw [commitMemV_swap hdisjM]
      _ = commitMemV mv (mq ++ mp ++ mr) := by
        symm
        rw [commitMemV_append]

/-! The admission-side write sets provide the queue disjointness needed by the
    local diamond.  The evaluator receipts remain explicit, so this adapter
    does not treat the parser predicate as an executor result. -/
theorem CoreMemDesign.edgesV_swap_of_write_disjoint {E : CoreMemDesign}
    {before after v : SvState} {mv : MemV} {p q : CoreMemProc} {rest : List CoreMemProc}
    {qp qq qr : NbaQueue2} {mp mq mr : MemQV} {rv : SvState}
    (hp : ∃ f, p.edge? = some f ∧ f.fires before after = true ∧
      E.execV E.env v mv f.body = .ok (v, qp, mp) ∧
      (∀ u ∈ qp, u.1 ∈ f.body.writes) ∧ (∀ u ∈ mp, u.1 ∈ f.body.writes))
    (hq : ∃ f, q.edge? = some f ∧ f.fires before after = true ∧
      E.execV E.env v mv f.body = .ok (v, qq, mq) ∧
      (∀ u ∈ qq, u.1 ∈ f.body.writes) ∧ (∀ u ∈ mq, u.1 ∈ f.body.writes))
    (hr : E.edgesV before after v mv rest = .ok (rv, qr, mr))
    (hwrite : ∀ x ∈ CoreMemProc.targets p, ∀ y ∈ CoreMemProc.targets q, x ≠ y)
    (hnd : (v.map Prod.fst).Nodup) :
    ∃ r₁ r₂,
      E.edgesV before after v mv (p :: q :: rest) = .ok r₁ ∧
      E.edgesV before after v mv (q :: p :: rest) = .ok r₂ ∧
      r₁.1 = r₂.1 ∧ commitNba2 v r₁.2.1 = commitNba2 v r₂.2.1 ∧
      commitMemV mv r₁.2.2 = commitMemV mv r₂.2.2 := by
  obtain ⟨fp, hpe, hfp, hbp, hqp, hmp⟩ := hp
  obtain ⟨fq, hqe, hfq, hbq, hqq, hmq⟩ := hq
  apply CoreMemDesign.edgesV_swap_local
  · exact ⟨fp, hpe, hfp, hbp⟩
  · exact ⟨fq, hqe, hfq, hbq⟩
  · exact hr
  · intro u hu u' hu' he
    have huP : u.1 ∈ p.targets := by
      rw [CoreMemProc.targets_of_edge? hpe]
      simp only [List.mem_eraseDups]
      exact hqp u hu
    have huQ : u'.1 ∈ q.targets := by
      rw [CoreMemProc.targets_of_edge? hqe]
      simp only [List.mem_eraseDups]
      exact hqq u' hu'
    exact hwrite u.1 huP u'.1 huQ he
  · intro u hu u' hu' he
    have huP : u.1 ∈ p.targets := by
      rw [CoreMemProc.targets_of_edge? hpe]
      simp only [List.mem_eraseDups]
      exact hmp u hu
    have huQ : u'.1 ∈ q.targets := by
      rw [CoreMemProc.targets_of_edge? hqe]
      simp only [List.mem_eraseDups]
      exact hmq u' hu'
    exact hwrite u.1 huP u'.1 huQ he
  · exact hnd

/-- A direct memory-element NBA leaves scalar state and scalar queue unchanged. -/
theorem CoreMemDesign.execV_memory_leaf {E : CoreMemDesign} {v : SvState} {mv : MemV}
    {name : String} {index : PExpr} {e : PExpr} {v' : SvState} {q : NbaQueue2} {mq : MemQV}
    (env : IEnv) (hmd : ∃ md, E.memDecl? name = some md)
    (h : E.execV env v mv (.nbaAssignL (.arrayElem name [index]) e) = .ok (v', q, mq)) :
    v' = v ∧ q = [] ∧ (∀ u ∈ mq, u.1 = name) := by
  simp only [CoreMemDesign.execV] at h
  obtain ⟨md, hd⟩ := hmd
  cases hx : E.memDecl? name with
  | none => simp [hx] at hd
  | some md' =>
      have heq : md = md' := Option.some.inj (hd.symm.trans hx)
      subst md'
      simp only [hx, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨x, -, iv, -, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, rfl, ?_⟩
      have hsource := (CoreMemDesign.memDecl?_some hx).2
      simp only [CoreMemDecl.issueV, memIss]
      generalize hs : index.signedCast = sg
      cases hk : md.shape.index? sg iv
      · intro u hu; simp [hk] at hu
      · intro u hu; simp at hu; simpa [hu, hsource]

/-! A procedural loop receipt packages the per-iteration memory evaluator
    facts into the exact flat-map queue produced by `execV_forLoop_memory`. -/
theorem CoreMemDesign.execV_forLoop_memory_records {E : CoreMemDesign} (env : IEnv) (v : SvState) (mv : MemV)
    {it : String} {init condition step : PExpr} {body : PStmt} {values : List Int}
    (hloop : PStmt.loopBodyB body = true)
    (hvals : forValues2 env it init condition step = .ok values)
    (hbody : ∀ i, ∃ mq, E.execV (env.bindVal it i) v mv body = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes)) :
    ∃ mq, E.execV env v mv (.forLoop it init condition step body) = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes) := by
  classical
  let m : Int → MemQV := fun i => (hbody i).choose
  have hm : ∀ i, E.execV (env.bindVal it i) v mv body = .ok (v, [], m i) := by
    intro i
    exact (hbody i).choose_spec.1
  have hnames : ∀ i u, u ∈ m i → u.1 ∈ body.writes := by
    intro i u hu
    exact (hbody i).choose_spec.2 u hu
  have hflat : ∀ xs : List Int, ∀ u, u ∈ xs.flatMap m → u.1 ∈ body.writes := by
    intro xs
    induction xs with
    | nil => simp
    | cons i rest ih =>
        intro u hu
        simp only [List.flatMap_cons] at hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hnames i u hu
        · exact ih u hu
  refine ⟨values.flatMap m, CoreMemDesign.execV_forLoop_memory env v mv m hm hloop hvals, ?_⟩
  exact hflat values

/-! The parser-native loop predicate supplies the evaluator's body gate. -/
theorem CoreMemDesign.execV_forLoop_memory_records_of_loopNbaMemory
    {E : CoreMemDesign} (env : IEnv) (v : SvState) (mv : MemV)
    {it : String} {init condition step : PExpr} {body : PStmt} {values : List Int}
    (hbodyP : PStmt.loopNbaMemory body = true)
    (hvals : forValues2 env it init condition step = .ok values)
    (hbody : ∀ i, ∃ mq, E.execV (env.bindVal it i) v mv body = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes)) :
    ∃ mq, E.execV env v mv (.forLoop it init condition step body) = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes) := by
  exact CoreMemDesign.execV_forLoop_memory_records env v mv
    (PStmt.loopNbaMemory_loopBodyB body hbodyP) hvals hbody

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
      let r ← E.execV E.env v mv p.body
      .ok r.2.1
    else .ok []
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some p => if p.fires before after then do
          let r ← E.execV E.env v mv p.body
          .ok r.2.1
        else .ok []
      | none => .ok []
  | _ => .ok []

theorem CoreMemDesign.procQ_of_edge? {E : CoreMemDesign} {before after v : SvState} {mv : MemV} {p : CoreMemProc}
    {f : CoreMemEdge} (h : p.edge? = some f) :
    E.procQ before after v mv p = if f.fires before after then do
        let r ← E.execV E.env v mv f.body
        .ok r.2.1
      else .ok [] := by
  cases p with
  | edge g =>
      simp only [CoreMemProc.edge?, Option.some.injEq] at h
      subst h
      rfl
  | event evs body =>
      simp only [CoreMemProc.edge?] at h
      simp only [CoreMemDesign.procQ, h]
  | _ => exact absurd h (by simp [CoreMemProc.edge?])

theorem CoreMemDesign.procQ_of_none {E : CoreMemDesign} {before after v : SvState} {mv : MemV} {p : CoreMemProc}
    (h : p.edge? = none) : E.procQ before after v mv p = .ok [] := by
  cases p with
  | edge g => exact absurd h (by simp [CoreMemProc.edge?])
  | event evs body =>
      simp only [CoreMemProc.edge?] at h
      simp only [CoreMemDesign.procQ, h]
  | _ => rfl

/-- The edge pass over `p :: rest`, `p` in `nbaWhole` form: `p`'s updates (of signals `p` drives, no memory record),
then the pass over `rest` on the same view. -/
theorem CoreMemDesign.edgesV_cons_inv {E : CoreMemDesign} {before after v : SvState} {mv : MemV} {p : CoreMemProc}
    {rest : List CoreMemProc} (hp : p.nbaWholeP = true) {r : ExecV}
    (h : E.edgesV before after v mv (p :: rest) = .ok r) :
    ∃ qp rr, E.procQ before after v mv p = .ok qp ∧ (∀ u ∈ qp, u.1 ∈ p.targets) ∧
      E.edgesV before after v mv rest = .ok rr ∧ r = (rr.1, qp ++ rr.2.1, rr.2.2) := by
  cases hpe : p.edge? with
  | none =>
      rw [CoreMemDesign.edgesV_cons_none hpe] at h
      exact ⟨[], r, CoreMemDesign.procQ_of_none hpe, by simp, h, by simp⟩
  | some f =>
      rw [CoreMemDesign.edgesV_cons_some hpe] at h
      rw [CoreMemDesign.procQ_of_edge? hpe, CoreMemProc.targets_of_edge? hpe]
      rw [CoreMemProc.nbaWholeP_of_edge? hpe] at hp
      split at h
      · rename_i hf
        simp only [Res.bind_eq_ok, Res.ok.injEq] at h
        obtain ⟨⟨v1, a, ma⟩, h1, rr, h2, rfl⟩ := h
        obtain ⟨rfl, ha, rfl⟩ := CoreMemDesign.execV_nbaWhole v mv f.body v1 a ma hp h1
        exact ⟨a, rr, by simp [hf, h1], fun u hu => by simp [List.mem_eraseDups, ha u hu], h2, by simp⟩
      · rename_i hf
        exact ⟨[], r, by simp [hf], by simp, h, by simp⟩

/-! A local decomposition for an edge body whose evaluator leaves the view alone.  The
 two queue components are retained separately so scalar and memory commits can be
 framed independently. -/
theorem CoreMemDesign.edgesV_cons_local {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {p : CoreMemProc} {rest : List CoreMemProc} {r : ExecV}
    (hlocal : ∀ (f : CoreMemEdge) (v' : SvState) (q : NbaQueue2) (mq : MemQV),
      E.execV E.env v mv f.body = .ok (v', q, mq) →
      v' = v ∧ (∀ u ∈ q, u.1 ∈ f.body.writes) ∧ (∀ u ∈ mq, u.1 ∈ f.body.writes))
    (h : E.edgesV before after v mv (p :: rest) = .ok r) :
    ∃ q mq rr, E.edgesV before after v mv rest = .ok rr ∧
      r = (rr.1, q ++ rr.2.1, mq ++ rr.2.2) ∧
      (∀ u ∈ q, u.1 ∈ p.targets) ∧ (∀ u ∈ mq, u.1 ∈ p.targets) := by
  cases hpe : p.edge? with
  | none =>
      rw [CoreMemDesign.edgesV_cons_none hpe] at h
      exact ⟨[], [], r, h, by simp, by simp, by simp⟩
  | some f =>
      rw [CoreMemDesign.edgesV_cons_some hpe] at h
      split at h
      · rename_i hf
        simp only [Res.bind_eq_ok, Res.ok.injEq] at h
        obtain ⟨⟨v1, q, mq⟩, h1, rr, h2, rfl⟩ := h
        obtain ⟨hv, hq, hm⟩ := hlocal f v1 q mq h1
        subst v1
        refine ⟨q, mq, rr, h2, by simp, ?_, ?_⟩
        · intro u hu
          simp only [CoreMemProc.targets_of_edge? hpe, List.mem_eraseDups]
          exact hq u hu
        · intro u hu
          simp only [CoreMemProc.targets_of_edge? hpe, List.mem_eraseDups]
          exact hm u hu
      · rename_i hf
        exact ⟨[], [], r, h, by simp, by simp, by simp⟩

/-! The same head decomposition retains the source-shaped evaluator receipt.
    This is the boundary needed by a permutation induction over mixed scalar
    and memory NBA bodies. -/
theorem CoreMemDesign.edgesV_cons_receipt {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {p : CoreMemProc} {rest : List CoreMemProc} {r : ExecV}
    (hlocal : ∀ (f : CoreMemEdge) (v' : SvState) (q : NbaQueue2) (mq : MemQV),
      E.execV E.env v mv f.body = .ok (v', q, mq) →
      v' = v ∧ (∀ u ∈ q, u.1 ∈ f.body.writes) ∧ (∀ u ∈ mq, u.1 ∈ f.body.writes))
    (h : E.edgesV before after v mv (p :: rest) = .ok r) :
    ∃ q mq rr, E.edgesV before after v mv rest = .ok rr ∧
      r = (rr.1, q ++ rr.2.1, mq ++ rr.2.2) ∧
      (∀ u ∈ q, u.1 ∈ p.targets) ∧ (∀ u ∈ mq, u.1 ∈ p.targets) ∧
      (p.edge? = none ∧ q = [] ∧ mq = [] ∨
        (∃ f, p.edge? = some f ∧ f.fires before after = false ∧ q = [] ∧ mq = []) ∨
        (∃ f, p.edge? = some f ∧ f.fires before after = true ∧
          E.execV E.env v mv f.body = .ok (v, q, mq))) := by
  cases hpe : p.edge? with
  | none =>
      rw [CoreMemDesign.edgesV_cons_none hpe] at h
      exact ⟨[], [], r, h, by simp, by simp, by simp,
        Or.inl ⟨by simpa [hpe], rfl, rfl⟩⟩
  | some f =>
      rw [CoreMemDesign.edgesV_cons_some hpe] at h
      split at h
      · rename_i hf
        simp only [Res.bind_eq_ok, Res.ok.injEq] at h
        obtain ⟨⟨v1, q, mq⟩, h1, rr, h2, rfl⟩ := h
        obtain ⟨hv, -, -⟩ := hlocal f v1 q mq h1
        subst v1
        exact ⟨q, mq, rr, h2, by simp,
          (fun u hu => by
            rw [CoreMemProc.targets_of_edge? hpe]
            simp only [List.mem_eraseDups]
            exact (hlocal f v q mq h1).2.1 u hu),
          (fun u hu => by
            rw [CoreMemProc.targets_of_edge? hpe]
            simp only [List.mem_eraseDups]
            exact (hlocal f v q mq h1).2.2 u hu),
          Or.inr (Or.inr ⟨f, by simpa [hpe], hf, h1⟩)⟩
      · rename_i hf
        have hf' : f.fires before after = false := by
          cases hfire : f.fires before after <;> simp_all
        exact ⟨[], [], r, h, by simp, by simp, by simp,
          Or.inr (Or.inl ⟨f, by simpa [hpe], hf', rfl, rfl⟩)⟩

theorem CoreMemDesign.edgesV_cons_mk_receipt {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {p : CoreMemProc} {rest : List CoreMemProc} {q : NbaQueue2} {mq : MemQV} {rr : ExecV}
    (h1 : E.edgesV before after v mv rest = .ok rr)
    (he : p.edge? = none ∧ q = [] ∧ mq = [] ∨
      (∃ f, p.edge? = some f ∧ f.fires before after = false ∧ q = [] ∧ mq = []) ∨
      (∃ f, p.edge? = some f ∧ f.fires before after = true ∧
        E.execV E.env v mv f.body = .ok (v, q, mq))) :
    E.edgesV before after v mv (p :: rest) = .ok (rr.1, q ++ rr.2.1, mq ++ rr.2.2) := by
  rcases he with ⟨hnone, rfl, rfl⟩ | ⟨⟨f, hpe, hf, rfl, rfl⟩⟩ | ⟨f, hpe, hf, hb⟩
  · rw [CoreMemDesign.edgesV_cons_none hnone]
    simpa using h1
  · rw [CoreMemDesign.edgesV_cons_some hpe]
    simp [hf, h1]
  · rw [CoreMemDesign.edgesV_cons_some hpe]
    simp [hf, hb, h1]

theorem CoreMemDesign.edgesV_view_memory {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    (hlocal : ∀ (f : CoreMemEdge) (v' : SvState) (q : NbaQueue2) (mq : MemQV),
      E.execV E.env v mv f.body = .ok (v', q, mq) →
      v' = v ∧ (∀ u ∈ q, u.1 ∈ f.body.writes) ∧ (∀ u ∈ mq, u.1 ∈ f.body.writes)) :
    ∀ {ps : List CoreMemProc}, (∀ p ∈ ps, p.nbaEdgeP = true) → ∀ {r : ExecV},
      E.edgesV before after v mv ps = .ok r → r.1 = v
  | [], _, r, h => by
      simp only [CoreMemDesign.edgesV, Res.ok.injEq] at h
      subst h
      rfl
  | p :: rest, hw, r, h => by
      obtain ⟨_, _, rr, hrest, rfl, -, -, -⟩ :=
        CoreMemDesign.edgesV_cons_receipt hlocal h
      simpa using CoreMemDesign.edgesV_view_memory hlocal
        (fun q hq => hw q (List.mem_cons_of_mem _ hq)) hrest

/-! The permutation induction for the memory-aware NBA class.  Its only
    evaluator premise is the frame receipt above, so the theorem remains
    attached to the real `edgesV` executor and does not infer a run from the
    admission predicate. -/
theorem CoreMemDesign.edgesV_perm_memory {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    (hlocal : ∀ (f : CoreMemEdge) (v' : SvState) (q : NbaQueue2) (mq : MemQV),
      E.execV E.env v mv f.body = .ok (v', q, mq) →
      v' = v ∧ (∀ u ∈ q, u.1 ∈ f.body.writes) ∧ (∀ u ∈ mq, u.1 ∈ f.body.writes) ) :
    ∀ {ps ps' : List CoreMemProc}, ps.Perm ps' → (∀ p ∈ ps, p.nbaEdgeP = true) →
      (ps.flatMap CoreMemProc.targets).Nodup → ∀ {r : ExecV},
      E.edgesV before after v mv ps = .ok r →
      r.1 = v ∧ ∃ r', E.edgesV before after v mv ps' = .ok r' ∧ r'.1 = v ∧
        (∀ st : SvState, (st.map Prod.fst).Nodup →
          commitNba2 st r'.2.1 = commitNba2 st r.2.1) ∧
        (∀ mv0 : MemV, commitMemV mv0 r'.2.2 = commitMemV mv0 r.2.2) := by
  intro ps ps' hperm
  induction hperm with
  | nil =>
      intro _ _ r h
      simp only [CoreMemDesign.edgesV, Res.ok.injEq] at h
      subst h
      exact ⟨rfl, _, rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
  | cons x _ ih =>
      intro hw hnd r h
      have hnd' := (List.nodup_append.mp (by simpa [List.flatMap_cons] using hnd)).2.1
      have hx := hw x (by simp)
      obtain ⟨qx, mx, rr, hrest, rfl, hqx, hmx, hcase⟩ :=
        CoreMemDesign.edgesV_cons_receipt hlocal h
      obtain ⟨hv2, r', h', hv2', hc, hm⟩ :=
        ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hnd' hrest
      refine ⟨hv2, (r'.1, qx ++ r'.2.1, mx ++ r'.2.2),
        CoreMemDesign.edgesV_cons_mk_receipt h' hcase, hv2', ?_, ?_⟩
      · intro st hst
        calc
          commitNba2 st (qx ++ r'.2.1) = commitNba2 (commitNba2 st qx) r'.2.1 := by
            rw [commitNba2_append]
          _ = commitNba2 (commitNba2 st qx) rr.2.1 :=
            hc _ (by rw [keys_commitNba2]; exact hst)
          _ = commitNba2 st (qx ++ rr.2.1) := by
            rw [commitNba2_append]
      · intro mv0
        calc
          commitMemV mv0 (mx ++ r'.2.2) = commitMemV (commitMemV mv0 mx) r'.2.2 := by
            rw [commitMemV_append]
          _ = commitMemV (commitMemV mv0 mx) rr.2.2 := hm (commitMemV mv0 mx)
          _ = commitMemV mv0 (mx ++ rr.2.2) := by
            rw [commitMemV_append]
  | swap x y l =>
      intro hw hnd r h
      have hy := hw y (by simp)
      have hx := hw x (by simp)
      have hl : ∀ p ∈ l, p.nbaEdgeP = true := fun p hp => hw p (by simp [hp])
      obtain ⟨qy, my, r1, h1, rfl, hqy, hmy, hcaseY⟩ :=
        CoreMemDesign.edgesV_cons_receipt hlocal h
      obtain ⟨qx, mx, r2, h2, rfl, hqx, hmx, hcaseX⟩ :=
        CoreMemDesign.edgesV_cons_receipt hlocal h1
      have hv2 := CoreMemDesign.edgesV_view_memory hlocal hl h2
      refine ⟨hv2, (r2.1, qx ++ (qy ++ r2.2.1), mx ++ (my ++ r2.2.2)), ?_, hv2, ?_, ?_⟩
      · exact CoreMemDesign.edgesV_cons_mk_receipt
          (CoreMemDesign.edgesV_cons_mk_receipt h2 hcaseY) hcaseX
      · intro st hst
        simp only [Prod.fst, Prod.snd]
        have hdisjS : ∀ u ∈ qx, ∀ u' ∈ qy, u.1 ≠ u'.1 := by
          simp only [List.flatMap_cons] at hnd
          have h3 := (List.nodup_append.mp hnd).2.2
          intro u hu u' hu' he
          exact h3 u'.1 (hqy u' hu') u.1 (List.mem_append_left _ (hqx u hu)) he.symm
        rw [← List.append_assoc, ← List.append_assoc, commitNba2_append st (qx ++ qy),
          commitNba2_append st (qy ++ qx), commitNba2_swap hst hdisjS]
      · intro mv0
        simp only [Prod.fst, Prod.snd]
        have hdisjM : ∀ u ∈ mx, ∀ u' ∈ my, u.1 ≠ u'.1 := by
          simp only [List.flatMap_cons] at hnd
          have h3 := (List.nodup_append.mp hnd).2.2
          intro u hu u' hu' he
          exact h3 u'.1 (hmy u' hu') u.1 (List.mem_append_left _ (hmx u hu)) he.symm
        rw [← List.append_assoc, ← List.append_assoc, commitMemV_append (mv := mv0) (mx ++ my),
          commitMemV_append (mv := mv0) (my ++ mx), commitMemV_swap hdisjM]
  | trans h₁₂ _ ih₁ ih₂ =>
      intro hw hnd r h
      obtain ⟨hv, r₁, h₁, hv₁, hc₁, hm₁⟩ := ih₁ hw hnd h
      obtain ⟨-, r₂, h₂, hv₂, hc₂, hm₂⟩ :=
        ih₂ (fun p hp => hw p (h₁₂.mem_iff.mpr hp))
          ((List.Perm.flatMap_right _ h₁₂).nodup_iff.mp hnd) h₁
      refine ⟨hv, r₂, h₂, hv₂, ?_, ?_⟩
      · intro st hst
        exact (hc₂ st hst).trans (hc₁ st hst)
      · intro mv0
        exact (hm₂ mv0).trans (hm₁ mv0)

/-- Mixed scalar and memory NBA queues commute when their target names are disjoint.
This is the commit-side diamond used by the memory-aware edge-order route. -/
theorem commitMixed_swap {st : SvState} (hnd : (st.map Prod.fst).Nodup)
    {mv : MemV} {q₁ q₂ : NbaQueue2} {m₁ m₂ : MemQV}
    (hs : ∀ u ∈ q₁, ∀ u' ∈ q₂, u.1 ≠ u'.1)
    (hm : ∀ u ∈ m₁, ∀ u' ∈ m₂, u.1 ≠ u'.1) :
    commitNba2 st (q₁ ++ q₂) = commitNba2 st (q₂ ++ q₁) ∧
      commitMemV mv (m₁ ++ m₂) = commitMemV mv (m₂ ++ m₁) := by
  have hs' := commitNba2_swap (st := st) hnd hs
  have hm' := commitMemV_swap (mv := mv) hm
  exact ⟨hs'.symm, hm'⟩

/-- The converse of `edgesV_cons_inv`. -/
theorem CoreMemDesign.edgesV_cons_mk {E : CoreMemDesign} {before after v : SvState} {mv : MemV} {p : CoreMemProc}
    {rest : List CoreMemProc} (hp : p.nbaWholeP = true) {qp : NbaQueue2} {rr : ExecV}
    (h1 : E.procQ before after v mv p = .ok qp) (h2 : E.edgesV before after v mv rest = .ok rr) :
    E.edgesV before after v mv (p :: rest) = .ok (rr.1, qp ++ rr.2.1, rr.2.2) := by
  cases hpe : p.edge? with
  | none =>
      rw [CoreMemDesign.procQ_of_none hpe] at h1
      simp only [Res.ok.injEq] at h1
      subst h1
      simp [CoreMemDesign.edgesV_cons_none hpe, h2]
  | some f =>
      rw [CoreMemDesign.procQ_of_edge? hpe] at h1
      rw [CoreMemProc.nbaWholeP_of_edge? hpe] at hp
      rw [CoreMemDesign.edgesV_cons_some hpe]
      split at h1
      · rename_i hf
        simp only [Res.bind_eq_ok, Res.ok.injEq] at h1
        obtain ⟨⟨v1, a, ma⟩, ha, rfl⟩ := h1
        obtain ⟨rfl, -, rfl⟩ := CoreMemDesign.execV_nbaWhole v mv f.body v1 a ma hp ha
        simp [hf, ha, h2]
      · rename_i hf
        simp only [Res.ok.injEq] at h1
        subst h1
        simp [hf, h2]

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
      have hx := hw x (by simp)
      obtain ⟨qx, rr, hqx, -, h2, rfl⟩ := CoreMemDesign.edgesV_cons_inv hx h
      obtain ⟨hv2, hm2, r', h2', hv2', hm2', hc⟩ := ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hnd' h2
      refine ⟨hv2, hm2, (r'.1, qx ++ r'.2.1, r'.2.2), CoreMemDesign.edgesV_cons_mk hx hqx h2', hv2', hm2',
        fun st hst => ?_⟩
      show commitNba2 st (qx ++ r'.2.1) = commitNba2 st (qx ++ rr.2.1)
      rw [commitNba2_append, commitNba2_append]
      exact hc _ (by rw [keys_commitNba2]; exact hst)
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
  | .primitive _ _ _ :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .initial b :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .comb b :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .implicit b :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .latch b :: ps, v => by
      simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, CoreMemDesign.edgesV_filter ps]
  | .event evs body :: ps, v => by
      cases hfe : coreMemEventEdge? evs body <;>
        simp [CoreMemDesign.edgesV, List.filter_cons, CoreMemProc.isEdge, hfe, CoreMemDesign.edgesV_filter ps]
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

/-! Obligation wrapper for the memory-aware successor.  The caller supplies the
    evaluator frame receipt because the admission bit alone is a parser-side
    classification and does not assert that an executor run succeeded. -/
theorem CoreMemDesign.edgesV_order_memory {E : CoreMemDesign}
    (hO : E.oblEdgeOrderMemory = true)
    {ps : List CoreMemProc} (hσ : ps.Perm E.processes.toList)
    {before after v : SvState} {mv : MemV}
    (hv : (v.map Prod.fst).Nodup) {r : ExecV}
    (hnd : (E.processes.toList.flatMap CoreMemProc.targets).Nodup)
    (hlocal : ∀ (f : CoreMemEdge) (v' : SvState) (q : NbaQueue2) (mq : MemQV),
      E.execV E.env v mv f.body = .ok (v', q, mq) →
      v' = v ∧ (∀ u ∈ q, u.1 ∈ f.body.writes) ∧ (∀ u ∈ mq, u.1 ∈ f.body.writes))
    (h : E.edgesV before after v mv E.processes.toList = .ok r) :
    ∃ r', E.edgesV before after v mv ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      commitMemV mv r'.2.2 = commitMemV mv r.2.2 := by
  simp only [CoreMemDesign.oblEdgeOrderMemory, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hO
  rcases hO with h1 | hw
  · exact ⟨r, by rw [CoreMemDesign.edgesV_single hσ.symm h1]; exact h, rfl, rfl⟩
  · obtain ⟨hv1, r', h', hv1', hc, hm⟩ :=
      CoreMemDesign.edgesV_perm_memory hlocal hσ.symm hw hnd h
    exact ⟨r', h', by rw [hv1', hv1]; exact hc v hv, hm mv⟩

/-- **THE EDGE ORDER DOES NOT MATTER, under the obligations** (rule 4): for every permutation of the processes, the
edge pass succeeds when the route's (source order) succeeds and commits to the same views. -/
theorem CoreMemDesign.edgesV_order {E : CoreMemDesign} (hO : E.seqOblI = true)
    {ps : List CoreMemProc} (hσ : ps.Perm E.processes.toList) {before after v : SvState} {mv : MemV}
    (hv : (v.map Prod.fst).Nodup) {r : ExecV}
    (h : E.edgesV before after v mv E.processes.toList = .ok r) :
    ∃ r', E.edgesV before after v mv ps = .ok r' ∧ commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      commitMemV mv r'.2.2 = commitMemV mv r.2.2 := by
  obtain ⟨hdr, -, -, -, -, hord, -⟩ := CoreMemDesign.seqOblI_spec hO
  simp only [CoreMemDesign.oblDrivers, CoreMemDesign.driven, decide_eq_true_eq] at hdr
  simp only [CoreMemDesign.oblEdgeOrder, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at hord
  rcases hord with h1 | hw
  · exact ⟨r, by rw [CoreMemDesign.edgesV_single hσ.symm h1]; exact h, rfl, rfl⟩
  · obtain ⟨hv1, hm1, r', h', hv1', hm1', hc⟩ := CoreMemDesign.edgesV_perm hσ.symm hw (of_decide_eq_true hdr) h
    exact ⟨r', h', by rw [hv1', hv1]; exact hc v hv, by rw [hm1, hm1']⟩

#print axioms CoreMemDesign.edgesV_order

/-! ## What the obligations buy: the slot's loops stop after their first round (§4.4, §4.5)

The route's slot repeats the continuous-assign pass until its view stops changing (`settleCanonical`) and the edge
round while its commit causes another edge event (`edgeQuiesce`). Under the obligations both loops stop after their
first round. One settle pass is the fixpoint (`settleV_idem`), so the region's result has the single pass's view
(`settleCanonical_seq`). No process writes an event source (the clock or an asynchronous reset: `oblNoInputWrite`,
`oblReset`), and a slot changes only the names its processes drive (`edgesV_frame`, `settleRaw_frame`,
`commitNba2_frame`), so the committed and settled view agrees with the pre-edge view on every event source and no
follow-up event fires (`slot_noFollowup`). The step is then its first round (`step_of_onePass`, `SeqCycleStep.lean`).
This also excludes, by the same obligations, every edge produced inside one nonblocking commit or one blocking sequence
(an event source is never written at all). -/

/-- **The continuous-assign region on the clocked profile is one `settleV`**, under the topological obligation, from a
coherent state with a coherent memory; the memory is unchanged. -/
theorem CoreMemDesign.settleCanonical_seq {E : CoreMemDesign} (hP : E.SeqProfileI)
    (ht : E.topoC = true) {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory) {v' : SvState}
    (hv : E.settleV (E.memOf st.memory) (E.scalar.view st.scalar) = .ok v') :
    ∃ st', E.settleCanonical E.env E.elems st E.processes.toList = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.Coherent st' ∧ st'.memory = st.memory := by
  obtain ⟨s1, hs1, hv1, hc1, hm1⟩ := CoreMemDesign.settleAssign_seq hP hc hmc hv
  have hidem := CoreMemDesign.settleV_idem ht (CoreMemDesign.matV_view hP.names hP.four hc.typed) hv
  obtain ⟨s2, hs2, hv2, hc2, hm2⟩ := CoreMemDesign.settleAssign_seq hP hc1 (by rw [hm1]; exact hmc)
    (by rw [hv1, hm1]; exact hidem)
  obtain ⟨s, hs, hor⟩ := CoreMemDesign.settleCanonical_of_fixpoint hs1 hs2 (by rw [hv1, hv2])
  rcases hor with rfl | rfl
  · exact ⟨_, hs, hv1, hc1, hm1⟩
  · exact ⟨_, hs, hv2, hc2, by rw [hm2, hm1]⟩

#print axioms CoreMemDesign.settleCanonical_seq

/-! ### The frame: a slot changes only the names its processes drive -/

/-- A write-target leaf whose name is in `S` (not a concatenation). -/
abbrev seqLeafIn (S : List String) (l : Lhs2) : Prop := (∀ ps, l ≠ .concat ps) ∧ l.name ∈ S

/-- A write target whose leaves are `seqLeafIn S`: a leaf, or a concatenation of leaves. -/
abbrev seqLhsIn (S : List String) (l : Lhs2) : Prop :=
  seqLeafIn S l ∨ ∃ ps, l = .concat ps ∧ ∀ x ∈ ps, seqLeafIn S x

private theorem seq_except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

private theorem seq_mapM_ok_mem {ε α β : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, y, hy => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp at hy
  | x :: xs, ys, h, y, hy => by
      rw [List.mapM_cons] at h
      obtain ⟨b, hb, h⟩ := seq_except_bind_ok h
      obtain ⟨bs, hbs, h⟩ := seq_except_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨x, by simp, hb⟩
      · obtain ⟨x', hx', hfx⟩ := seq_mapM_ok_mem hbs y hy
        exact ⟨x', by simp [hx'], hfx⟩

private theorem seq_baseNames_mem_list : ∀ {parts : List PLhs} {p : PLhs}, p ∈ parts →
    ∀ x ∈ PLhs.baseNames p, x ∈ PLhs.baseNamesList parts
  | [], _, h, _, _ => by simp at h
  | q :: qs, p, h, x, hx => by
      simp only [List.mem_cons] at h
      simp only [PLhs.baseNamesList, List.mem_append]
      rcases h with rfl | h
      · exact Or.inl hx
      · exact Or.inr (seq_baseNames_mem_list h x hx)

/-- A leaf the target compiler lowers writes the target's own base name. -/
theorem seq_instLhsLeaf2_in {env : IEnv} {elems : List (String × Nat)} (t : PLhs) {l : Lhs2} {w : Nat}
    (h : instLhsLeaf2 env elems t = .ok (l, w)) : seqLeafIn (PLhs.baseNames t) l := by
  cases t <;> simp only [instLhsLeaf2, arrayElemTarget, arrayPartTarget] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       exact ⟨fun ps => by simp, by simp [Lhs2.name, PLhs.baseNames]⟩)

/-- **The target compiler keeps the base names**: every leaf of a compiled target writes a base name of the source
target. -/
theorem seq_instLhs2_in {env : IEnv} {elems : List (String × Nat)} (t : PLhs) {l : Lhs2} {w : Nat}
    (h : instLhs2 env elems t = .ok (l, w)) : seqLhsIn (PLhs.baseNames t) l := by
  cases t with
  | concat parts =>
      right
      simp only [instLhs2] at h
      split at h
      · obtain ⟨_, he, -⟩ := seq_except_bind_ok h
        cases he
      obtain ⟨lowered, hlow, h⟩ := seq_except_bind_ok h
      split at h
      · obtain ⟨_, he, -⟩ := seq_except_bind_ok h
        cases he
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine ⟨_, rfl, fun x hx => ?_⟩
      obtain ⟨⟨y, wy⟩, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨p, hp, hpy⟩ := seq_mapM_ok_mem hlow _ hy
      obtain ⟨hc, hn⟩ := seq_instLhsLeaf2_in p hpy
      exact ⟨hc, seq_baseNames_mem_list hp _ hn⟩
  | ident n => exact Or.inl (seq_instLhsLeaf2_in _ (by simpa [instLhs2] using h))
  | bitSel n i => exact Or.inl (seq_instLhsLeaf2_in _ (by simpa [instLhs2] using h))
  | partSel n a b => exact Or.inl (seq_instLhsLeaf2_in _ (by simpa [instLhs2] using h))
  | arrayElem n is => exact Or.inl (seq_instLhsLeaf2_in _ (by simpa [instLhs2] using h))
  | arrayPart n is m a b => exact Or.inl (seq_instLhsLeaf2_in _ (by simpa [instLhs2] using h))
  | aggregateMember base path =>
      exact False.elim (by simpa [instLhs2, instLhsLeaf2] using h)

/-- A leaf resolves to its own name. -/
theorem seq_resolveLhs2_name {fuel : Nat} {v : SvState} {l : Lhs2} (hl : ∀ ps, l ≠ .concat ps) {n : String}
    {w : Option (Nat × Nat)} (h : resolveLhs2 fuel v l = .ok (n, w)) : n = l.name := by
  cases l with
  | ident m =>
      simp only [resolveLhs2] at h
      cases hm : SvState.lookup v m with
      | none => rw [hm] at h; simp at h
      | some old =>
          rw [hm] at h
          simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
          exact h.1.symm
  | slice m lo w' =>
      simp only [resolveLhs2, Res.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  | index m idx ew =>
      simp only [resolveLhs2] at h
      obtain ⟨iv, -, h⟩ := Res.bind_eq_ok.mp h
      (repeat' split at h) <;> simp_all [Lhs2.name]
  | concat ps => exact absurd rfl (hl ps)

private theorem seq_foldlM_wins {g : Lhs2 → Res (List (String × Nat × Nat))} :
    ∀ (l : List Lhs2) (acc ws : List (String × Nat × Nat)),
      l.foldlM (fun acc part => do let w ← g part; pure (acc ++ w)) acc = .ok ws →
      ∀ x ∈ ws, x ∈ acc ∨ ∃ p ∈ l, ∃ w, g p = .ok w ∧ x ∈ w
  | [], acc, ws, h => by
      simp only [List.foldlM] at h
      cases h
      exact fun x hx => Or.inl hx
  | p :: ps, acc, ws, h => by
      simp only [List.foldlM] at h
      cases hg : g p with
      | ok w =>
        rw [hg] at h
        simp only [Res.ok_bind, Res.pure_eq] at h
        intro x hx
        rcases seq_foldlM_wins ps (acc ++ w) ws h x hx with h1 | ⟨q, hq, w', hw', hx'⟩
        · rcases List.mem_append.mp h1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨p, List.mem_cons_self .., w, hg, h1⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, w', hw', hx'⟩
      | timeout => rw [hg] at h; simp at h
      | unsupported m => rw [hg] at h; simp at h

/-- A leaf's windows are its own. -/
theorem seq_resolveConcatLhs2_leaf {fuel : Nat} {v : SvState} {l : Lhs2} (hl : ∀ ps, l ≠ .concat ps)
    {ws : List (String × Nat × Nat)} (h : resolveConcatLhs2 fuel v l = .ok ws) : ∀ u ∈ ws, u.1 = l.name := by
  have key : ∀ (name : String) (win : Option (Nat × Nat)), resolveLhs2 fuel v l = .ok (name, win) →
      (match win with
        | some (lo, width) => (pure [(name, lo, width)] : Res (List (String × Nat × Nat)))
        | none => .unsupported "continuous concatenation target has no fixed window") = .ok ws →
      ∀ u ∈ ws, u.1 = l.name := by
    intro name win hres hw u hu
    have hn := seq_resolveLhs2_name hl hres
    cases win with
    | none => simp at hw
    | some lw =>
        obtain ⟨lo, width⟩ := lw
        simp only [Res.pure_eq, Res.ok.injEq] at hw
        subst hw
        simp only [List.mem_singleton] at hu
        subst hu
        exact hn
  cases l with
  | ident m =>
      simp only [resolveConcatLhs2] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := Res.bind_eq_ok.mp h
      exact key name win hres h
  | slice m lo w =>
      simp only [resolveConcatLhs2] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := Res.bind_eq_ok.mp h
      exact key name win hres h
  | index m idx ew =>
      simp only [resolveConcatLhs2] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := Res.bind_eq_ok.mp h
      exact key name win hres h
  | concat ps => exact absurd rfl (hl ps)

/-- **The window resolver keeps the names**: every window of a target whose leaves write names in `S` is in `S`. -/
theorem seq_resolveConcatLhs2_in {fuel : Nat} {v : SvState} {S : List String} {l : Lhs2} (hl : seqLhsIn S l)
    {ws : List (String × Nat × Nat)} (h : resolveConcatLhs2 fuel v l = .ok ws) : ∀ u ∈ ws, u.1 ∈ S := by
  rcases hl with ⟨hc, hn⟩ | ⟨ps, rfl, hps⟩
  · intro u hu
    rw [seq_resolveConcatLhs2_leaf hc h u hu]
    exact hn
  · rw [resolveConcatLhs2.eq_1] at h
    intro u hu
    rcases seq_foldlM_wins ps [] ws h u hu with h1 | ⟨p, hp, w, hw, hu'⟩
    · simp at h1
    · obtain ⟨hpc, hpn⟩ := hps p hp
      rw [seq_resolveConcatLhs2_leaf hpc hw u hu']
      exact hpn

private theorem seq_writeConcat_go_frame (rep : LVec) : ∀ (ws : List (String × Nat × Nat)) (st st' : SvState)
    (rw : Nat), writeConcatLhs2.go rep st ws rw = .ok st' →
      ∀ x, x ∉ ws.map Prod.fst → SvState.lookup st' x = SvState.lookup st x
  | [], st, st', rw, h, x, _ => by
      simp only [writeConcatLhs2.go, Res.ok.injEq] at h
      subst h; rfl
  | (n, lo, w) :: rest, st, st', rw, h, x, hx => by
      simp only [writeConcatLhs2.go] at h
      have hxn : n ≠ x := fun h' => hx (by simp [h'])
      have hxr : x ∉ rest.map Prod.fst := fun h' => hx (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h')
      cases hs : SvState.lookup st n with
      | none => rw [hs] at h; simp at h
      | some old =>
          rw [hs] at h
          simp only at h
          rw [seq_writeConcat_go_frame rep rest _ st' _ h x hxr, lookup_set']
          simp [hxn]

/-- The concatenation writer changes only its windows' names. -/
theorem seq_writeConcatLhs2_frame {st st' : SvState} {value : LVec} {ws : List (String × Nat × Nat)}
    (h : writeConcatLhs2 st value ws = .ok st') : ∀ x, x ∉ ws.map Prod.fst → SvState.lookup st' x = SvState.lookup st x :=
  seq_writeConcat_go_frame _ ws st st' _ h

private theorem seq_scalarNbaWindows_go_names (rep : LVec) : ∀ (ws : List (String × Nat × Nat)) (rw : Nat),
    ∀ u ∈ scalarNbaWindows.go rep ws rw, u.1 ∈ ws.map Prod.fst
  | [], _, u, hu => by simp [scalarNbaWindows.go] at hu
  | (n, lo, w) :: rest, rw, u, hu => by
      simp only [scalarNbaWindows.go, List.mem_cons] at hu
      rcases hu with rfl | hu
      · simp
      · exact List.mem_cons_of_mem _ (seq_scalarNbaWindows_go_names rep rest _ u hu)

/-- The nonblocking updates of a select or concatenation target name its windows. -/
theorem seq_scalarNbaWindows_names (x : LVec) (ws : List (String × Nat × Nat)) :
    ∀ u ∈ scalarNbaWindows x ws, u.1 ∈ ws.map Prod.fst :=
  seq_scalarNbaWindows_go_names _ ws _

/-- The commit of a queue changes only the names it updates. -/
theorem commitNba2_frame (q : NbaQueue2) (st : SvState) (x : String) (h : ∀ u ∈ q, u.1 ≠ x) :
    SvState.lookup (commitNba2 st q) x = SvState.lookup st x := by
  unfold commitNba2
  induction q generalizing st with
  | nil => rfl
  | cons u q ih =>
      rw [List.foldl_cons, ih _ (fun u' hu' => h u' (List.mem_cons_of_mem _ hu'))]
      have hu : u.1 ≠ x := h u (by simp)
      split
      · rw [lookup_set']; simp [hu]
      · rfl

/-- `setV` changes only its name. -/
theorem CoreMemDesign.lookup_setV_ne {E : CoreMemDesign} {v : SvState} {n x : String} (h : n ≠ x) (y : LVec) :
    SvState.lookup (E.setV v n y) x = SvState.lookup v x := by
  unfold CoreMemDesign.setV
  split
  · split
    · rw [lookup_set']; simp [h]
    · rfl
  · rfl

/-- The materialization is idempotent (on distinct 4-state declarations). -/
theorem CoreMemDesign.matV_matV {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) (r : SvState) : E.matV (E.matV r) = E.matV r := by
  rw [← E.view_storeFromView r]
  exact CoreMemDesign.matV_view hnd h4 (E.typed_storeFromView r)

/-- An edge-body result that changes no name outside `S` (on the materialized view) and issues updates of names in `S`
only. -/
def CoreMemDesign.FrameV (E : CoreMemDesign) (S : List String) (v : SvState) (r : ExecV) : Prop :=
  (∀ x, x ∉ S → SvState.lookup (E.matV r.1) x = SvState.lookup (E.matV v) x) ∧ ∀ u ∈ r.2.1, u.1 ∈ S

theorem CoreMemDesign.FrameV.mono {E : CoreMemDesign} {S S' : List String} {v : SvState} {r : ExecV}
    (h : E.FrameV S v r) (hS : ∀ x ∈ S, x ∈ S') : E.FrameV S' v r :=
  ⟨fun x hx => h.1 x fun h' => hx (hS x h'), fun u hu => hS _ (h.2 u hu)⟩

/-- A select or concatenation write on a view changes only its target's names. -/
theorem CoreMemDesign.writeLhsV_frame {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {S : List String} {v v' : SvState} {l : Lhs2} {value : LVec} (hl : seqLhsIn S l)
    (h : E.writeLhsV v l value = .ok v') : ∀ x, x ∉ S → SvState.lookup (E.matV v') x = SvState.lookup (E.matV v) x := by
  intro x hx
  cases l with
  | concat ps =>
      simp only [CoreMemDesign.writeLhsV, Res.bind_eq_ok, Res.ok.injEq] at h
      obtain ⟨ws, hws, v'', hw, rfl⟩ := h
      rw [CoreMemDesign.matV_matV hnd h4]
      apply CoreMemDesign.lookup_matV_congr
      apply seq_writeConcatLhs2_frame hw x
      intro hxm
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hxm
      exact hx (seq_resolveConcatLhs2_in hl hws u hu)
  | _ =>
      have hleaf : ∀ {l' : Lhs2}, seqLhsIn S l' → (∀ ps, l' ≠ .concat ps) → seqLeafIn S l' := by
        intro l' h1 h2
        rcases h1 with h1 | ⟨ps, rfl, -⟩
        · exact h1
        · exact absurd rfl (h2 ps)
      simp only [CoreMemDesign.writeLhsV, Res.bind_eq_ok] at h
      obtain ⟨⟨name, win⟩, hres, h⟩ := h
      have hlf := hleaf hl (fun ps => by simp)
      have hname : name ∈ S := by rw [seq_resolveLhs2_name hlf.1 hres]; exact hlf.2
      have hnx : name ≠ x := fun h' => hx (h' ▸ hname)
      dsimp only at h
      (repeat' split at h) <;> simp only [Res.ok.injEq, reduceCtorEq] at h <;> (try subst h) <;>
        (try rfl) <;> exact CoreMemDesign.lookup_matV_congr (CoreMemDesign.lookup_setV_ne hnx _)

/-- The route's select-target compiler is the target compiler. -/
theorem CoreMemDesign.scalarLhs2_ok {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)} {t : PLhs}
    {l : Lhs2} {w : Nat} (h : E.scalarLhs2 env elems t = .ok (l, w)) : instLhs2 env elems t = .ok (l, w) := by
  unfold CoreMemDesign.scalarLhs2 at h
  cases hi : instLhs2 env elems t with
  | ok res => rw [hi] at h; simp only [Res.ok.injEq] at h; rw [h]
  | error e => rw [hi] at h; simp at h

/-- The nonblocking updates of a compiled select or concatenation target name the target's base names. -/
theorem CoreMemDesign.nbaWindows_in {E : CoreMemDesign} {env : IEnv} {t : PLhs} {l : Lhs2} {w : Nat}
    (hl : E.scalarLhs2 env E.elems t = .ok (l, w)) {v : SvState} {ws : List (String × Nat × Nat)}
    (hws : resolveConcatLhs2 4096 v l = .ok ws) (x : LVec) : ∀ u ∈ scalarNbaWindows x ws, u.1 ∈ PLhs.baseNames t := by
  intro u hu
  obtain ⟨u', hu', he⟩ := List.mem_map.mp (seq_scalarNbaWindows_names x ws u hu)
  rw [← he]
  exact seq_resolveConcatLhs2_in (seq_instLhs2_in t (CoreMemDesign.scalarLhs2_ok hl)) hws u' hu'

/-- The frame of the loop fold, from the frame of its body's runs. -/
theorem CoreMemDesign.execLoopV_frame {E : CoreMemDesign} {S : List String} {v : SvState} {step : Int → Res ExecV}
    (hstep : ∀ i r, step i = .ok r → E.FrameV S v r) :
    ∀ (values : List Int) (r : ExecV), execLoopV v step values = .ok r → E.FrameV S v r
  | [], r, h => by
      simp only [execLoopV, Res.ok.injEq] at h
      subst h
      exact ⟨fun _ _ => rfl, by simp⟩
  | i :: rest, r, h => by
      simp only [execLoopV, Res.bind_eq_ok, Res.ok.injEq] at h
      obtain ⟨a, h1, b, h2, rfl⟩ := h
      have ha := hstep i a h1
      have hb := CoreMemDesign.execLoopV_frame hstep rest b h2
      refine ⟨fun _ _ => rfl, fun u hu => ?_⟩
      rcases List.mem_append.mp hu with hu | hu
      · exact ha.2 u hu
      · exact hb.2 u hu

mutual

/-- **The frame of an edge body**: the view changes, on the materialized view, only at the names the body writes, and
the nonblocking updates name them. -/
theorem CoreMemDesign.execV_frame {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) (env : IEnv) (v : SvState) (mv : MemV) :
    ∀ (b : PStmt) (r : ExecV), E.execV env v mv b = .ok r → E.FrameV b.writes v r
  | .nbaAssign t e, r, h => by
      simp only [CoreMemDesign.execV] at h
      split at h
      · simp at h
      · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
        obtain ⟨x, -, rfl⟩ := h
        exact ⟨fun _ _ => rfl, by simp [PStmt.writes]⟩
  | .nbaAssignL lhs e, r, h => by
      cases lhs with
      | ident t =>
          simp only [CoreMemDesign.execV] at h
          split at h
          · simp at h
          · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
            obtain ⟨x, -, rfl⟩ := h
            exact ⟨fun _ _ => rfl, by simp [PStmt.writes, PLhs.baseNames]⟩
      | arrayElem name indices =>
          simp only [CoreMemDesign.execV] at h
          split at h
          · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
            obtain ⟨⟨l, w⟩, hl, x, -, ws, hws, rfl⟩ := h
            exact ⟨fun _ _ => rfl, CoreMemDesign.nbaWindows_in hl hws x⟩
          · split at h
            · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
              obtain ⟨x, -, iv, -, rfl⟩ := h
              exact ⟨fun _ _ => rfl, by simp⟩
            · simp at h
      | _ =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq] at h
          obtain ⟨⟨l, w⟩, hl, x, -, ws, hws, rfl⟩ := h
          exact ⟨fun _ _ => rfl, CoreMemDesign.nbaWindows_in hl hws x⟩
  | .blockingAssign n e, r, h => by
      simp only [CoreMemDesign.execV] at h
      split at h
      · simp at h
      · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
        obtain ⟨x, -, rfl⟩ := h
        refine ⟨fun y hy => CoreMemDesign.lookup_matV_congr (CoreMemDesign.lookup_setV_ne ?_ _), by simp⟩
        intro h'; subst h'; simp [PStmt.writes] at hy
  | .blockingAssignL lhs e, r, h => by
      cases lhs with
      | ident n =>
          simp only [CoreMemDesign.execV] at h
          split at h
          · simp at h
          · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
            obtain ⟨x, -, rfl⟩ := h
            refine ⟨fun y hy => CoreMemDesign.lookup_matV_congr (CoreMemDesign.lookup_setV_ne ?_ _), by simp⟩
            intro h'; subst h'; simp [PStmt.writes, PLhs.baseNames] at hy
      | arrayElem name indices =>
          simp only [CoreMemDesign.execV] at h
          split at h
          · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
            obtain ⟨⟨l, w⟩, hl, x, -, v', hw, rfl⟩ := h
            exact ⟨CoreMemDesign.writeLhsV_frame hnd h4 (seq_instLhs2_in _ (CoreMemDesign.scalarLhs2_ok hl)) hw,
              by simp⟩
          · simp at h
      | _ =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq] at h
          obtain ⟨⟨l, w⟩, hl, x, -, v', hw, rfl⟩ := h
          exact ⟨CoreMemDesign.writeLhsV_frame hnd h4 (seq_instLhs2_in _ (CoreMemDesign.scalarLhs2_ok hl)) hw, by simp⟩
  | .ifStmt c y n, r, h => by
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at h
      obtain ⟨cv, -, h⟩ := h
      split at h
      · exact (CoreMemDesign.execV_frame hnd h4 env v mv y r h).mono fun x hx => by
          simp only [PStmt.writes, List.mem_append]; exact Or.inl hx
      · cases n with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq] at h
            subst h
            exact ⟨fun _ _ => rfl, by simp⟩
        | some s =>
            simp only [CoreMemDesign.execOptV] at h
            exact (CoreMemDesign.execV_frame hnd h4 env v mv s r h).mono fun x hx => by
              simp only [PStmt.writes, PStmt.optWrites, List.mem_append]; exact Or.inr hx
  | .block body, r, h => by
      simp only [CoreMemDesign.execV] at h
      exact (CoreMemDesign.execListV_frame hnd h4 env v mv body r h).mono fun x hx => by simpa [PStmt.writes] using hx
  | .caseStmt subject items d mode check, r, h => by
      have hdflt : ∀ r', E.execOptV env v mv d = .ok r' → E.FrameV (PStmt.optWrites d) v r' := by
        intro r' hr
        cases d with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq] at hr
            subst hr
            exact ⟨fun _ _ => rfl, by simp⟩
        | some s =>
            simp only [CoreMemDesign.execOptV] at hr
            exact (CoreMemDesign.execV_frame hnd h4 env v mv s r' hr).mono fun x hx => by simpa [PStmt.optWrites] using hx
      have hitems : ∀ sv res, E.execItemsV env v mv sv mode items (E.execOptV env v mv d) = .ok res →
          E.FrameV (PStmt.caseStmt subject items d mode check).writes v res := by
        intro sv res hres
        exact (CoreMemDesign.execItemsV_frame hnd h4 env v mv sv mode items _ res hdflt hres).mono fun x hx => by
          simpa [PStmt.writes] using hx
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at h
      obtain ⟨sv, -, h⟩ := h
      cases check
      case none => exact hitems sv r h
      all_goals
        simp only [Res.bind_eq_ok] at h
        obtain ⟨n, -, h⟩ := h
        split at h
        · exact hitems sv r h
        · simp at h
  | .forLoop it init cond step body, r, h => by
      simp only [CoreMemDesign.execV] at h
      by_cases hlb : PStmt.loopBodyB body = true
      · simp only [hlb, ↓reduceIte] at h
        cases hvals : forValues2 env it init cond step with
        | timeout => simp [hvals] at h
        | unsupported e => simp [hvals] at h
        | ok values =>
            simp only [hvals] at h
            exact (CoreMemDesign.execLoopV_frame
              (fun i r' hr => CoreMemDesign.execV_frame hnd h4 (env.bindVal it i) v mv body r' hr) values r h).mono
              fun x hx => by simp only [PStmt.writes]; exact hx
      · simp [hlb] at h
  | .unsupported .., r, h => by simp [CoreMemDesign.execV] at h

/-- The list form of `execV_frame`. -/
theorem CoreMemDesign.execListV_frame {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) (env : IEnv) (v : SvState) (mv : MemV) :
    ∀ (bs : List PStmt) (r : ExecV), E.execListV env v mv bs = .ok r → E.FrameV (PStmt.listWrites bs) v r
  | [], r, h => by
      simp only [CoreMemDesign.execListV, Res.ok.injEq] at h
      subst h
      exact ⟨fun _ _ => rfl, by simp⟩
  | s :: ss, r, h => by
      simp only [CoreMemDesign.execListV, Res.bind_eq_ok, Res.ok.injEq] at h
      obtain ⟨a, h1, b, h2, rfl⟩ := h
      have ha := CoreMemDesign.execV_frame hnd h4 env v mv s a h1
      have hb := CoreMemDesign.execListV_frame hnd h4 env a.1 mv ss b h2
      refine ⟨fun x hx => ?_, fun u hu => ?_⟩
      · simp only [PStmt.listWrites, List.mem_append, not_or] at hx
        show SvState.lookup (E.matV b.1) x = _
        rw [hb.1 x hx.2, ha.1 x hx.1]
      · simp only [PStmt.listWrites, List.mem_append]
        rcases List.mem_append.mp hu with hu | hu
        · exact Or.inl (ha.2 u hu)
        · exact Or.inr (hb.2 u hu)

/-- The arms of a `case`: the frame of the arm that runs, or of the default. -/
theorem CoreMemDesign.execItemsV_frame {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) (env : IEnv) (v : SvState) (mv : MemV) (sv : LVec) (mode : CaseMode) :
    ∀ (items : List (List PExpr × PStmt)) (dflt : Res ExecV) (res : ExecV)
      {D : List String}, (∀ r, dflt = .ok r → E.FrameV D v r) →
      E.execItemsV env v mv sv mode items dflt = .ok res → E.FrameV (PStmt.itemsWrites items ++ D) v res
  | [], dflt, res, D, hd, h => by
      simp only [CoreMemDesign.execItemsV] at h
      exact (hd res h).mono fun x hx => by simp [PStmt.itemsWrites, hx]
  | (ps, b) :: rest, dflt, res, D, hd, h => by
      simp only [CoreMemDesign.execItemsV, Res.bind_eq_ok] at h
      obtain ⟨vals, -, h⟩ := h
      split at h
      · exact (CoreMemDesign.execV_frame hnd h4 env v mv b res h).mono fun x hx => by
          simp only [PStmt.itemsWrites, List.mem_append]; exact Or.inl (Or.inl hx)
      · exact (CoreMemDesign.execItemsV_frame hnd h4 env v mv sv mode rest dflt res hd h).mono fun x hx => by
          simp only [PStmt.itemsWrites, List.mem_append] at hx ⊢
          rcases hx with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'

end

/-- **The frame of the edge pass**: the threaded view changes, on the materialized view, only at the names the
processes drive, and the nonblocking updates name them. -/
theorem CoreMemDesign.edgesV_frame {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {before after : SvState} :
    ∀ (ps : List CoreMemProc) (v : SvState) (mv : MemV) (r : ExecV), E.edgesV before after v mv ps = .ok r →
      E.FrameV (ps.flatMap CoreMemProc.targets) v r
  | [], v, mv, r, h => by
      simp only [CoreMemDesign.edgesV, Res.ok.injEq] at h
      subst h
      exact ⟨fun _ _ => rfl, by simp⟩
  | p :: rest, v, mv, r, h => by
      have hmono : ∀ x ∈ rest.flatMap CoreMemProc.targets, x ∈ (p :: rest).flatMap CoreMemProc.targets :=
        fun x hx => by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr hx
      cases hpe : p.edge? with
      | none =>
          rw [CoreMemDesign.edgesV_cons_none hpe] at h
          exact (CoreMemDesign.edgesV_frame hnd h4 rest v mv r h).mono hmono
      | some f =>
          rw [CoreMemDesign.edgesV_cons_some hpe] at h
          split at h
          · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
            obtain ⟨a, h1, b, h2, rfl⟩ := h
            have ha := CoreMemDesign.execV_frame hnd h4 E.env v mv f.body a h1
            have hb := CoreMemDesign.edgesV_frame hnd h4 rest a.1 mv b h2
            have hfa : ∀ x ∈ f.body.writes, x ∈ (p :: rest).flatMap CoreMemProc.targets :=
              fun x hx => by
                simp only [List.flatMap_cons, List.mem_append, CoreMemProc.targets_of_edge? hpe, List.mem_eraseDups]
                exact Or.inl hx
            refine ⟨fun x hx => ?_, fun u hu => ?_⟩
            · show SvState.lookup (E.matV b.1) x = _
              rw [hb.1 x fun h' => hx (hmono x h'), ha.1 x fun h' => hx (hfa x h')]
            · rcases List.mem_append.mp hu with hu | hu
              · exact hfa _ (ha.2 u hu)
              · exact hmono _ (hb.2 u hu)
          · exact (CoreMemDesign.edgesV_frame hnd h4 rest v mv r h).mono hmono

/-- The continuous assigns' targets are driven names. -/
theorem CoreMemDesign.assignTargets_driven {E : CoreMemDesign} :
    ∀ x ∈ assignTargets E.processes.toList, x ∈ E.driven := by
  intro x hx
  simp only [assignTargets, List.mem_flatMap] at hx
  obtain ⟨p, hp, hx⟩ := hx
  simp only [CoreMemDesign.driven, List.mem_flatMap]
  refine ⟨p, hp, ?_⟩
  cases p with
  | assign t e =>
      cases t with
      | ident n => simpa [CoreMemProc.targets] using hx
      | _ => simp at hx
  | _ => simp at hx

/-- An edge's event does not occur between two views that agree on its clock and its reset (§9.4.2: an edge is a
change). -/
theorem CoreMemEdge.fires_of_agree {f : CoreMemEdge} {a b : SvState}
    (hc : SvState.lookup a f.clock = SvState.lookup b f.clock)
    (hr : ∀ r, f.reset = some r → SvState.lookup a r = SvState.lookup b r) : f.fires a b = false := by
  have hpos : ∀ x : Logic, isPosedge x x = false := by intro x; cases x <;> rfl
  have hneg : ∀ x : Logic, isNegedge x x = false := by intro x; cases x <;> rfl
  have hbc : SvState.bit0 a f.clock = SvState.bit0 b f.clock := by simp only [SvState.bit0, hc]
  unfold CoreMemEdge.fires
  rw [hbc]
  cases hrs : f.reset with
  | none => cases f.edge <;> simp [hpos, hneg]
  | some r =>
      have hbr : SvState.bit0 a r = SvState.bit0 b r := by simp only [SvState.bit0, hr r hrs]
      simp only [hbr]
      cases f.edge <;> cases f.resetHigh <;> simp [hpos, hneg]

/-- **The frame of a slot's edge round**: the view the round leaves (edges, commit, the region settled twice) agrees with
the pre-edge view on every name no process drives. -/
theorem CoreMemDesign.round_frame {E : CoreMemDesign} (hP : E.SeqProfileI) {v p s1 s2 : SvState} {mv mv' : MemV}
    {r : ExecV} (hp : E.matV p = p) (hr : E.edgesV v p p mv E.processes.toList = .ok r)
    (h1 : E.settleV mv' (commitNba2 r.1 r.2.1) = .ok s1) (h2 : E.settleV mv' s1 = .ok s2) :
    ∀ x, x ∉ E.driven → SvState.lookup s2 x = SvState.lookup p x := by
  have hfr := CoreMemDesign.edgesV_frame hP.names hP.four E.processes.toList p mv r hr
  intro x hx
  have hxa : x ∉ assignTargets E.processes.toList := fun h' => hx (CoreMemDesign.assignTargets_driven x h')
  simp only [CoreMemDesign.settleV, Res.bind_eq_ok, Res.ok.injEq] at h1 h2
  obtain ⟨raw1, hr1, rfl⟩ := h1
  obtain ⟨raw2, hr2, rfl⟩ := h2
  have e2 := CoreMemDesign.settleRaw_frame _ _ _ _ hr2 x hxa
  have e1 := CoreMemDesign.settleRaw_frame _ _ _ _ hr1 x hxa
  have ec : SvState.lookup (commitNba2 r.1 r.2.1) x = SvState.lookup r.1 x :=
    commitNba2_frame r.2.1 r.1 x fun u hu he => hx (he ▸ hfr.2 u hu)
  calc SvState.lookup (E.matV raw2) x = SvState.lookup (E.matV (E.matV raw1)) x :=
        CoreMemDesign.lookup_matV_congr e2
    _ = SvState.lookup (E.matV raw1) x := by rw [CoreMemDesign.matV_matV hP.names hP.four]
    _ = SvState.lookup (E.matV (commitNba2 r.1 r.2.1)) x := CoreMemDesign.lookup_matV_congr e1
    _ = SvState.lookup (E.matV r.1) x := CoreMemDesign.lookup_matV_congr ec
    _ = SvState.lookup (E.matV p) x := hfr.1 x hx
    _ = SvState.lookup p x := by rw [hp]

/-- **NO FOLLOW-UP EVENT**: under the obligations, the view a slot's first round leaves agrees with its pre-edge view
on every name no process drives, so no edge process's event occurs between them (no process drives an event source:
every clock and every reset is an undriven input port). The route's in-slot iteration therefore stops after the first
round. -/
theorem CoreMemDesign.slot_noFollowup {E : CoreMemDesign} (hP : E.SeqProfileI)
    (hO : E.seqOblI = true) {v p s1 s2 : SvState} {mv mv' : MemV} {r : ExecV} (hp : E.matV p = p)
    (hr : E.edgesV v p p mv E.processes.toList = .ok r)
    (h1 : E.settleV mv' (commitNba2 r.1 r.2.1) = .ok s1) (h2 : E.settleV mv' s1 = .ok s2) :
    E.firesAny p s2 = false := by
  -- the slot changes only driven names
  have hfix := CoreMemDesign.round_frame hP hp hr h1 h2
  simp only [CoreMemDesign.firesAny, List.any_eq_false]
  intro q hq
  cases q with
  | edge f =>
      have hclk : f.clock ∉ E.driven := CoreMemDesign.source_undriven hO (CoreMemDesign.clock_mem_sources (CoreMemDesign.edge_mem_edgeProcs hq))
      have hres : ∀ r, f.reset = some r → r ∉ E.driven := fun r hr' =>
        CoreMemDesign.source_undriven hO (CoreMemDesign.reset_mem_sources (CoreMemDesign.edge_mem_edgeProcs hq) hr')
      simp only [CoreMemProc.firesIn, Bool.not_eq_true]
      exact CoreMemEdge.fires_of_agree (hfix _ hclk).symm fun r hr' => (hfix r (hres r hr')).symm
  | event events body =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
      rw [Array.getElem?_toList] at hi
      have hproc := hP.procs i (.event events body) hi
      cases hfe : coreMemEventEdge? events body with
      | none =>
          rw [CoreMemDesign.ProcOkI, hfe] at hproc
          exact False.elim hproc
      | some f =>
          have hf : f ∈ E.edgeProcs := CoreMemDesign.mem_edgeProcs.mpr
            ⟨.event events body, hq, hfe⟩
          have hclk : f.clock ∉ E.driven := CoreMemDesign.source_undriven hO
            (CoreMemDesign.clock_mem_sources hf)
          have hres : ∀ r, f.reset = some r → r ∉ E.driven := fun r hr' =>
            CoreMemDesign.source_undriven hO (CoreMemDesign.reset_mem_sources hf hr')
          have heq := coreMemEventEdge?_spec hfe p s2
          simp only [CoreMemProc.firesIn, Bool.not_eq_true] at heq ⊢
          rw [heq.1]
          exact CoreMemEdge.fires_of_agree (hfix _ hclk).symm fun r hr' =>
            (hfix r (hres r hr')).symm
  | _ => simp [CoreMemProc.firesIn]

#print axioms CoreMemDesign.slot_noFollowup

/-! ## The refinement: the route's slot and cycle on views (under the obligations) -/

/-- **THE SLOT REFINEMENT, any number of events**: for a design of the clocked profile (any clocks, either edge) with
its obligations, from every coherent state with a coherent memory and every typed row (a data row or an instant, the
input discipline is not needed here), when the view-level slot succeeds the route's `step` succeeds, lands on exactly
that view and memory view, and stays coherent. The obligations are what make the route's in-slot loops stop
after their first round (`settleCanonical_seq`, `slot_noFollowup`); the step is read through `step_of_onePass` only. -/
theorem CoreMemDesign.step_seqI {E : CoreMemDesign} (hP : E.SeqProfileI)
    (hO : E.seqOblI = true) {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry) {v' : SvState} {mv' : MemV}
    (hv : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv')) :
    ∃ st', E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧ E.memOf st'.memory = mv' ∧
      E.Coherent st' ∧ E.MemCoherent st'.memory := by
  have ht : E.topoC = true := (CoreMemDesign.seqOblI_spec hO).2.1
  simp only [CoreMemDesign.slotV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
  obtain ⟨p0, h0, p, h1, ⟨pe, q, mq⟩, hq, s1, h2, s2, h3, rfl, rfl⟩ := hv
  dsimp only at h2 h3
  -- the inputs (no memory is an input port)
  have hmi : E.applyMemoryInputs entry st.memory = st.memory := E.applyMemoryInputs_id hP.mems entry st.memory
  have hTin : E.scalar.Typed (E.scalar.applyInputs st.scalar entry) := hc.typed.applyInputs entry
  have hvin : E.scalar.view (E.scalar.applyInputs st.scalar entry) =
      applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar) :=
    Elab.view_applyInputs hP.names hP.four hc.typed hty
  have hci : E.Coherent (E.inputState st entry) := E.normalizeScalar_coherent _ hTin
  have hvi : E.scalar.view (E.inputState st entry).scalar =
      applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar) := by
    rw [CoreMemDesign.inputState, E.normalizeScalar_view, hvin]
  have hmemi : (E.inputState st entry).memory = st.memory := hmi
  -- the region before the edge
  obtain ⟨st0, hs0, hv0, hc0, hm0⟩ := CoreMemDesign.settleCanonical_seq hP ht hci (by rw [hmemi]; exact hmc)
    (by rw [hvi, hmemi]; exact h0)
  rw [hmemi] at hm0
  obtain ⟨st1, hs1, hv1, hc1, hm1⟩ := CoreMemDesign.settleCanonical_seq hP ht hc0 (by rw [hm0]; exact hmc)
    (by rw [hv0, hm0]; exact h1)
  rw [hm0] at hm1
  -- the edge round
  obtain ⟨st2, hedge, hv2, hc2, hm2, hrec⟩ := CoreMemDesign.runEdges_V hP.names hP.four
    (E.scalar.view st.scalar) (E.scalar.view st1.scalar) E.processes.toList hP.shapes st1 pe q mq hc1
    (by rw [hm1]; exact hmc) (by rw [hv1, hm1]; exact hq)
  rw [hm1] at hm2
  -- the commit: scalar updates
  have hT2 : E.scalarEdge.base.Typed st2.scalar := by rw [hP.base]; exact hc2.typed
  have hTc : E.scalar.Typed (E.scalarEdge.commit st2.scalar q) := by
    have := Elab1.typed_commit (E := E.scalarEdge) q hT2
    rwa [hP.base] at this
  have hvc : E.scalar.view (E.scalarEdge.commit st2.scalar q) = commitNba2 pe q := by
    have := Elab1.view_commit (E := E.scalarEdge) (by rw [hP.base]; exact hP.four) q hT2
    rw [hP.base] at this
    rw [this, hv2]
  have hcc := E.normalizeScalar_coherent st2 hTc
  -- the commit: memory records
  obtain ⟨m', hcm, hmc', hvm⟩ := CoreMemDesign.commitNba_V hP.mems mq st2.memory (by rw [hm2]; exact hmc) hrec
  rw [hm2] at hvm
  have hcs : E.Coherent (E.committedState ⟨st2, q, mq.map E.memRec, []⟩ m') := hcc.with_memory m'
  have hvs : E.scalar.view (E.committedState ⟨st2, q, mq.map E.memRec, []⟩ m').scalar = commitNba2 pe q := by
    show E.scalar.view (E.normalizeScalar st2 (E.scalarEdge.commit st2.scalar q)).scalar = _
    rw [E.normalizeScalar_view, hvc]
  have hms : (E.committedState ⟨st2, q, mq.map E.memRec, []⟩ m').memory = m' := rfl
  -- the region after the edge
  obtain ⟨st3, hs3, hv3, hc3, hm3⟩ := CoreMemDesign.settleCanonical_seq hP ht hcs (by rw [hms]; exact hmc')
    (by rw [hvs, hms, hvm]; exact h2)
  rw [hms] at hm3
  obtain ⟨st4, hs4, hv4, hc4, hm4⟩ := CoreMemDesign.settleCanonical_seq hP ht hc3 (by rw [hm3]; exact hmc')
    (by rw [hv3, hm3, hvm]; exact h3)
  refine ⟨st4, ?_, hv4, by rw [hm4, hm3, hvm], hc4, by rw [hm4, hm3]; exact hmc'⟩
  -- no follow-up event: the step is its first round
  have hnf := CoreMemDesign.slot_noFollowup hP hO (CoreMemDesign.matV_settleV hP.names hP.four h1) hq h2 h3
  exact CoreMemDesign.step_of_onePass hP.hasComb hP.hasImplicit hs0 hs1 hedge hcm hs3 hs4
    (by rw [hv1, hv4]; exact hnf)

#print axioms CoreMemDesign.step_seqI

/-! The concrete confluence bridge for the first honest clocked class.  The
continuous-assignment region is settled before and after the edge, and the
only schedule choice is the order of the edge processes' NBA evaluations.
`edgesV_order` supplies the local commutation from `seqOblI`'s disjoint-driver
and edge-order guards.  The theorem below carries that result through the
actual `CoreMemDesign.step`, so it is not a statement about a detached
relation or a source-order surrogate.  The synthesis reading is the same
boundary as IEEE 1364.1-2002 §5.2.2 and Annex B.1: edge-sensitive storage uses
nonblocking updates, while independent procedural interleavings remain open
when blocking assignments create a dependency. -/
theorem CoreMemDesign.edge_schedule_refines_step {E : CoreMemDesign}
    (hP : E.SeqProfileI) (hO : E.seqOblI = true)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    {ps : List CoreMemProc} (hσ : ps.Perm E.processes.toList) :
    ∃ p r r' st',
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) E.processes.toList = .ok r ∧
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' := by
  obtain ⟨st', hstep, hvstep, hmstep, -, -⟩ :=
    CoreMemDesign.step_seqI hP hO hc hmc hty hslot
  have hslot' := hslot
  simp only [CoreMemDesign.slotV, Res.bind_eq_ok] at hslot'
  obtain ⟨p0, hp0, p, hp, r, hr, s1, hs1, s2, hs2, hout⟩ := hslot'
  have hmatp : E.matV p = p := CoreMemDesign.matV_settleV hP.names hP.four hp
  have hviewp : E.scalar.view (E.storeFromView p) = p := by
    rw [E.view_storeFromView, hmatp]
  have hnames : (p.map Prod.fst).Nodup := by
    rw [← hviewp, E.scalar.keys_view]
    exact hP.names
  obtain ⟨r', hr', hcommit, -⟩ :=
    CoreMemDesign.edgesV_order (v := p) hO hσ hnames hr
  exact ⟨p, r, r', st', hr, hr', hcommit, hstep, hvstep, hmstep⟩

#print axioms CoreMemDesign.edge_schedule_refines_step

/-! The same bridge with the individual admission guards exposed at the theorem
boundary.  This keeps the concrete class auditable: unique drivers, acyclic
continuous assignments, undriven event sources, source-read/self-read safety,
edge-order independence, and converted source nodes are separate premises. -/
theorem CoreMemDesign.edge_schedule_refines_step_guarded {E : CoreMemDesign}
    (hP : E.SeqProfileI)
    (hdrivers : E.oblDrivers = true) (htopo : E.topoC = true)
    (hinputs : E.oblInputsUndriven = true) (hsources : E.oblSources = true)
    (hreads : E.oblNoSourceRead = true) (hedge : E.oblEdgeOrder = true)
    (hconverted : E.oblConverted = true)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hslot : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv'))
    {ps : List CoreMemProc} (hσ : ps.Perm E.processes.toList) :
    ∃ p r r' st',
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) E.processes.toList = .ok r ∧
      E.edgesV (E.scalar.view st.scalar) p p (E.memOf st.memory) ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' := by
  have hO : E.seqOblI = true := by
    simp [CoreMemDesign.seqOblI, hdrivers, htopo, hinputs, hsources, hreads, hedge, hconverted]
  exact CoreMemDesign.edge_schedule_refines_step hP hO hc hmc hty hslot hσ

#print axioms CoreMemDesign.edge_schedule_refines_step_guarded

/-! A two-process local diamond, extracted from the admitted edge class.  The
source and swapped pair are both legal process orders, and `seqOblI` supplies
the disjoint-driver/whole-NBA guard that makes their committed scalar and
memory views equal.  This is the concrete commutation fact used when a
scheduler chooses either enabled edge process first. -/
theorem CoreMemDesign.edgesV_local_diamond {E : CoreMemDesign}
    (hO : E.seqOblI = true) {p q : CoreMemProc} {rest : List CoreMemProc}
    (hσ : (q :: p :: rest).Perm E.processes.toList)
    {before after v : SvState} {mv : MemV} (hv : (v.map Prod.fst).Nodup) {r : ExecV}
    (h : E.edgesV before after v mv E.processes.toList = .ok r) :
    ∃ r₁ r₂,
      E.edgesV before after v mv (p :: q :: rest) = .ok r₁ ∧
      E.edgesV before after v mv (q :: p :: rest) = .ok r₂ ∧
      commitNba2 r₁.1 r₁.2.1 = commitNba2 r₂.1 r₂.2.1 ∧
      commitMemV mv r₁.2.2 = commitMemV mv r₂.2.2 := by
  have hpσ : (p :: q :: rest).Perm E.processes.toList := by
    exact (List.Perm.swap p q rest).symm.trans hσ
  obtain ⟨r₁, h₁, hc₁, hm₁⟩ := CoreMemDesign.edgesV_order hO hpσ hv h
  obtain ⟨r₂, h₂, hc₂, hm₂⟩ := CoreMemDesign.edgesV_order hO hσ hv h
  exact ⟨r₁, r₂, h₁, h₂, hc₁.trans hc₂.symm, hm₁.trans hm₂.symm⟩

#print axioms CoreMemDesign.edgesV_local_diamond

/-- **THE SLOT REFINEMENT, single clock**: `step_seqI` at the single-clock profile and obligations. -/
theorem CoreMemDesign.step_seq {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (hO : E.seqOblB clk = true) {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry) {v' : SvState} {mv' : MemV}
    (hv : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv')) :
    ∃ st', E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧ E.memOf st'.memory = mv' ∧
      E.Coherent st' ∧ E.MemCoherent st'.memory :=
  CoreMemDesign.step_seqI hP.toSeqProfileI (CoreMemDesign.seqOblB_I hO) hc hmc hty hv

#print axioms CoreMemDesign.step_seq

/-- **THE CYCLE REFINEMENT (the cycle model derived from E)**: for a design of the clocked profile with its obligations,
from every coherent state with a coherent memory, for every typed data entry, when the view-level cycle gives
`(pre, post)` the route's two slots succeed, land on exactly `pre` and `post` (views and memory views), and stay
coherent. -/
theorem CoreMemDesign.cycleMV_refines {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (hO : E.seqOblB clk = true) {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    {data : SvState} (hlow : EntryTyped E.scalar.toDesign2 (lowEntry clk data))
    (hhigh : EntryTyped E.scalar.toDesign2 (highEntry clk)) {pre post : SvState × MemV}
    (hv : E.cycleMV clk (E.scalar.view st.scalar, E.memOf st.memory) data = .ok (pre, post)) :
    ∃ s1 s2, E.step st (lowEntry clk data) = .ok s1 ∧ E.step s1 (highEntry clk) = .ok s2 ∧
      (E.scalar.view s1.scalar, E.memOf s1.memory) = pre ∧ (E.scalar.view s2.scalar, E.memOf s2.memory) = post ∧
      E.Coherent s1 ∧ E.Coherent s2 ∧ E.MemCoherent s1.memory ∧ E.MemCoherent s2.memory := by
  simp only [CoreMemDesign.cycleMV_slots, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
  obtain ⟨⟨v1, m1⟩, h1, ⟨v2, m2⟩, h2, rfl, rfl⟩ := hv
  obtain ⟨s1, hs1, hv1, hm1, hc1, hmc1⟩ := CoreMemDesign.step_seq hP hO hc hmc hlow h1
  obtain ⟨s2, hs2, hv2, hm2, hc2, hmc2⟩ :=
    CoreMemDesign.step_seq hP hO hc1 hmc1 hhigh (by rw [hv1, hm1]; exact h2)
  exact ⟨s1, s2, hs1, hs2, by rw [hv1, hm1], by rw [hv2, hm2], hc1, hc2, hmc1, hmc2⟩

#print axioms CoreMemDesign.cycleMV_refines

/-- **THE CYCLE REFINEMENT, without memories**: from every coherent state, for every typed data entry, when the
view-level cycle gives `(pre, post)` the route's two slots succeed, land on exactly `pre` and `post`, and stay
coherent. -/
theorem CoreMemDesign.cycle_of_seqProfile {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (hO : E.seqOblB clk = true) (hm : E.memories.toList = []) {st : CoreMemState} (hc : E.Coherent st)
    {data : SvState} (hlow : EntryTyped E.scalar.toDesign2 (lowEntry clk data))
    (hhigh : EntryTyped E.scalar.toDesign2 (highEntry clk))
    {pre post : SvState} (hv : E.cycleV clk (E.scalar.view st.scalar) data = .ok (pre, post)) :
    ∃ s1 s2, E.step st (lowEntry clk data) = .ok s1 ∧ E.step s1 (highEntry clk) = .ok s2 ∧
      E.scalar.view s1.scalar = pre ∧ E.scalar.view s2.scalar = post ∧ E.Coherent s1 ∧ E.Coherent s2 := by
  simp only [CoreMemDesign.cycleV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
  obtain ⟨⟨⟨v1, m1⟩, ⟨v2, m2⟩⟩, h, rfl, rfl⟩ := hv
  obtain ⟨s1, s2, hs1, hs2, hp1, hp2, hc1, hc2, -, -⟩ := CoreMemDesign.cycleMV_refines hP hO hc
    (CoreMemDesign.memCoherent_noMem hm _) hlow hhigh (by rw [CoreMemDesign.memOf_noMem hm]; exact h)
  simp only [Prod.mk.injEq] at hp1 hp2
  exact ⟨s1, s2, hs1, hs2, hp1.1, hp2.1, hc1, hc2⟩

#print axioms CoreMemDesign.cycle_of_seqProfile

/-- **The route's time-zero state on the clocked profile** (no `$readmemh`) is the canonical quiescent settle of its continuous assigns
(§§4.5 and 10.3) from the x start `CoreMemDesign.initial` (`initialState_of_quiet`): when the view-level pass `settleV` gives `v`
on the x start, the time-zero state exists, its view is `v`, its memory is the x start's (every memory its typed x/z
block), and it is coherent with a coherent memory. So it is one of the run judgment's start states: every `SeqRunsOn`
claim (`SeqRunsI`, `SeqRunsM`, `SeqRuns`) holds from it. -/
theorem CoreMemDesign.SeqProfileI.initialState {E : CoreMemDesign} (hP : E.SeqProfileI) (ht : E.topoC = true)
    (hrm : E.readmemh = []) (hdi : E.declInitializers = [])
    {v : SvState} (hv : E.settleV (E.memOf E.initial.memory) (E.scalar.view E.initial.scalar) = .ok v) :
    ∃ st, E.initialState = .ok st ∧ E.scalar.view st.scalar = v ∧ st.memory = E.initial.memory ∧ E.Coherent st ∧
      E.MemCoherent st.memory := by
  have hmc := CoreMemDesign.initial_memCoherent hP.mems
  obtain ⟨st, hs, hvs, hc, hm⟩ := CoreMemDesign.settleCanonical_seq hP ht E.initial_coherent hmc hv
  refine ⟨st, ?_, hvs, hm, hc, by rw [hm]; exact hmc⟩
  rw [CoreMemDesign.initialState_of_quiet (fun p hp b h => by
    subst h; exact absurd (hP.shapes _ hp) (by simp [CoreMemDesign.ProcShapeI])) hP.hasComb hrm]
  simp only [hdi, CoreMemDesign.execDeclInitializers, Res.ok_bind]
  exact hs

#print axioms CoreMemDesign.SeqProfileI.initialState

/-- `SeqProfileI.initialState` on the single-clock profile. -/
theorem CoreMemDesign.SeqProfile.initialState {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (hO : E.seqOblB clk = true) (hrm : E.readmemh = []) (hdi : E.declInitializers = []) {v : SvState}
    (hv : E.settleV (E.memOf E.initial.memory) (E.scalar.view E.initial.scalar) = .ok v) :
    ∃ st, E.initialState = .ok st ∧ E.scalar.view st.scalar = v ∧ st.memory = E.initial.memory ∧ E.Coherent st ∧
      E.MemCoherent st.memory :=
  hP.toSeqProfileI.initialState (CoreMemDesign.seqOblI_spec (CoreMemDesign.seqOblB_I hO)).2.1 hrm hdi hv

#print axioms CoreMemDesign.SeqProfile.initialState

/-- **The time-zero state is settled** under the topological obligation (`topoC`, part of `seqOblI` and `seqOblB`):
one more view-level pass changes nothing (`settleV_idem`), and the route's own continuous-assign region
(`settleCanonical`, the slots' quiesce loop) run from the time-zero state lands on the same view. No continuous
assignment is out of date at time zero (§4.5, §10.3). -/
theorem CoreMemDesign.SeqProfileI.initialState_settled {E : CoreMemDesign} (hP : E.SeqProfileI)
    (ht : E.topoC = true) (hrm : E.readmemh = []) (hdi : E.declInitializers = []) {v : SvState}
    (hv : E.settleV (E.memOf E.initial.memory) (E.scalar.view E.initial.scalar) = .ok v) :
    ∃ st, E.initialState = .ok st ∧ E.scalar.view st.scalar = v ∧ E.settleV (E.memOf st.memory) v = .ok v ∧
      ∃ st', E.settleCanonical E.env E.elems st E.processes.toList = .ok st' ∧ E.scalar.view st'.scalar = v := by
  obtain ⟨st, hs, hvs, hm, hc, hmc⟩ := hP.initialState ht hrm hdi hv
  have hidem : E.settleV (E.memOf st.memory) v = .ok v := by
    rw [hm]
    exact CoreMemDesign.settleV_idem ht (CoreMemDesign.matV_view hP.names hP.four E.initial_coherent.typed) hv
  obtain ⟨st', hs', hv', -, -⟩ := CoreMemDesign.settleCanonical_seq hP ht hc hmc (by rw [hvs]; exact hidem)
  exact ⟨st, hs, hvs, hidem, st', hs', hv'⟩

#print axioms CoreMemDesign.SeqProfileI.initialState_settled

end LeanModels.Sv.Kernel
