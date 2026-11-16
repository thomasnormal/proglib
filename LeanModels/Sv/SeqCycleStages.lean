import Lean
import LeanModels.Sv.SeqCycleTactic
import LeanModels.Sv.CombTaskTactic

/-!
# The stage names on clocked goals (`sv_structure`, `sv_interface`, `sv_equations`)

One workflow for a prover: the comb stages' names also run the clocked stages when the goal is a clocked one. Each
name gets a further elaborator, tried first, that recognizes ONLY its clocked goal shape and otherwise throws
`unsupportedSyntax`, so every comb proof elaborates unchanged (the pattern of `CombProcTactic.lean`):

| name | clocked goal | what runs |
|---|---|---|
| `sv_structure` | `SeqDesign (X.e P…) clk` | the instantiation at symbolic parameters, the clocked profile, the obligations |
| `sv_interface` | `SeqPorts (X.e P…) ins outs` | the instantiation, the ports |
| `sv_equations` | `E.cycleV clk v d = rhs`, with `hE : X.e P… = .ok E` in the context | the cycle equations, computed (with the context's width facts `x.width = n`), then `rhs` checked against them |

A clocked stage that fails names its reason: the route's own refusal message, a process outside the clocked profile
(with its index, its kind and what puts it outside), or the obligation that does not hold. The macros of
`SeqCycleTactic.lean` (`sv_seq_inst`, `sv_seq_profile`, `sv_seq_obligations`, `sv_seq_ports`, `sv_seq_cycle`) are the
implementation and stay available.
-/

open Lean Elab Tactic Meta

namespace LeanModels.Sv.Kernel.SeqStage

/-- Once a clocked elaborator has recognized its goal it must not fall through to the comb elaborators (they would
report the comb goal shape); its error is logged here and the goal admitted, as `CombProcTactic.guardL` does. -/
def guardSeq (act : TacticM Unit) : TacticM Unit := do
  try act
  catch ex =>
    match ex with
    | .internal _ _ => throw ex
    | _ =>
        logException ex
        for g in ← getGoals do
          unless ← g.isAssigned do g.admit
        setGoals []

/-- The `e` and `pdesign` constants of a loaded family `X.e P…`. -/
def familyNames (stage : String) (r : Lean.Expr) : MetaM (Name × Name) := do
  let some eName := r.getAppFn.constName?
    | throwError "{stage}: the design is not a loaded family `X.e P…` (a `load_design_sv2` constant applied to its parameters)"
  return (eName, eName.getPrefix ++ `pdesign)

/-- The elements of a list literal. -/
partial def listElems (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return some []
  if e.isAppOfArity ``List.cons 3 then
    match ← listElems (e.getArg! 2) with
    | some rest => return some (e.getArg! 1 :: rest)
    | none => return none
  return none

/-- The elements of an array literal (`#[a, b, …]`). -/
def arrayElems (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``List.toArray 2 then return ← listElems (e.getArg! 1)
  let e ← whnf e
  if e.isAppOfArity ``Array.mk 2 then return ← listElems (e.getArg! 1)
  return none

/-- A string literal's value. -/
def strLit? (e : Lean.Expr) : Option String :=
  match e with
  | Lean.Expr.lit (Lean.Literal.strVal s) => some s
  | _ => none

/-- Why a process of the normal form is outside the clocked profile (the `procOkB` check failed on it). -/
def whyProc (clk : String) (i : Nat) (p : Lean.Expr) : MetaM String := do
  let p ← whnf p
  let at_ := s!"process {i}"
  if p.isAppOfArity ``CoreMemProc.edge 1 then
    let f ← whnf (p.getArg! 0)
    if f.isAppOfArity ``CoreMemEdge.mk 4 then
      let clock := strLit? (f.getArg! 0)
      if clock.isSome && clock != some clk then
        return s!"{at_} (an edge process) is clocked by `{clock.get!}`, not `{clk}`: two clocks are outside the clocked profile (the owner's to decide)"
      let body := f.getArg! 2
      if (body.find? (·.isConstOf ``PStmt.forLoop)).isSome then
        return s!"{at_} (an edge process) has a procedural `for` loop: the memories slice (next), refused"
      if (body.find? (·.isConstOf ``PExpr.functionCall)).isSome then
        return s!"{at_} (an edge process) calls a function: outside the clocked profile (U5)"
      if (body.find? (·.isConstOf ``PStmt.unsupported)).isSome then
        return s!"{at_} (an edge process) holds a statement ingestion kept unconverted"
      return s!"{at_} (an edge process): its body is outside the edge-body fragment the clocked stages mirror"
    return s!"{at_} (an edge process): outside the clocked profile"
  if p.isAppOfArity ``CoreMemProc.comb 1 then
    return s!"{at_} is an always_comb process: always_comb beside flip-flops is the next slice (T7), refused"
  if p.isAppOfArity ``CoreMemProc.implicit 1 then
    return s!"{at_} is an implicit-event process (`always @*` / `always @(a)`): outside the clocked profile"
  if p.isAppOfArity ``CoreMemProc.initial 1 then
    return s!"{at_} is an initial process: outside the clocked profile (the route admits elaboration checks only, U5)"
  if p.isAppOfArity ``CoreMemProc.unsupported 2 then
    return s!"{at_} is a member ingestion kept unconverted ({(strLit? (p.getArg! 0)).getD "?"})"
  if p.isAppOfArity ``CoreMemProc.assign 2 then
    let t ← whnf (p.getArg! 0)
    unless t.isAppOfArity ``PLhs.ident 1 do
      return s!"{at_} is a continuous assign to a select or concatenation target: outside the clocked profile"
    let v := p.getArg! 1
    if (v.find? fun e => e.isConstOf ``PExpr.arrayElem || e.isConstOf ``PExpr.arrayPart).isSome then
      return s!"{at_} (a continuous assign) reads a memory: the memories slice (next), refused"
    if (v.find? (·.isConstOf ``PExpr.functionCall)).isSome then
      return s!"{at_} (a continuous assign) calls a function: outside the clocked profile (U5)"
    return s!"{at_} (a continuous assign): its compiled expression is missing or its target is undeclared"
  return s!"{at_}: outside the clocked profile"

/-- Run a tactic on a goal; `true` when it closes it without an error (an error inside a nested `by`, which term
elaboration would log and replace by `sorry`, counts as a failure). The state is restored either way. -/
def closes (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    setGoals [g]
    Term.withoutErrToSorry (evalTactic tac)
    let ok := (← getGoals).isEmpty && !(← MonadLog.hasErrors)
    s.restore
    return ok
  catch _ =>
    s.restore
    return false

/-- The profile stage on `E.SeqProfile clk` (`E` the normal form), with a named refusal. -/
def runProfile (g : MVarId) : TacticM Unit := do
  if ← closes g (← `(tactic| sv_seq_profile)) then
    setGoals [g]
    evalTactic (← `(tactic| sv_seq_profile))
    return
  let ty ← instantiateMVars (← g.getType)
  let E := ty.getArg! 0
  let clk := (strLit? (← whnf (ty.getArg! 1))).getD "?"
  let mems ← arrayElems (← whnf (mkApp (mkConst ``CoreMemDesign.memories) E))
  if let some (_ :: _) := mems then
    throwError "sv_structure: the design has memories: the memories slice (next), refused"
  let some ps ← arrayElems (← whnf (mkApp (mkConst ``CoreMemDesign.processes) E))
    | throwError "sv_structure: the clocked profile does not hold (the processes are not a literal list at these parameters)"
  let mut i := 0
  for p in ps do
    let t := mkApp4 (mkConst ``CoreMemDesign.procOkB) E (toExpr clk) (toExpr i) p
    let gp ← mkFreshExprMVar (← mkEq t (toExpr true))
    unless ← closes gp.mvarId! (← `(tactic| simp (config := {decide := true}) [
        LeanModels.Sv.Kernel.CoreMemDesign.procOkB, LeanModels.Sv.PStmt.edgeOkB, LeanModels.Sv.PStmt.optEdgeOkB,
        LeanModels.Sv.PStmt.listEdgeOkB, LeanModels.Sv.PStmt.itemsEdgeOkB, LeanModels.Sv.PStmt.need,
        LeanModels.Sv.PStmt.optNeed, LeanModels.Sv.PStmt.listNeed, LeanModels.Sv.PStmt.itemsNeed,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCallList,
        LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?, LeanModels.Sv.Kernel.Elab.resolve,
        LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf])) do
      throwError "sv_structure: {← whyProc clk i p}"
    i := i + 1
  throwError "sv_structure: the clocked profile does not hold: the declarations are not distinct and 4-state, or the scalar and edge views differ"

/-- The named obligations, in the order they are checked, with the reason each refuses. -/
def obligations : List (Name × Bool × String) :=
  [(``CoreMemDesign.oblDrivers, false, "two processes drive the same signal (one driver per signal)"),
   (``CoreMemDesign.topoC, false,
     "a continuous assign reads its own target or a later assign's target: the route's settle would be stale (U1), refused"),
   (``CoreMemDesign.oblNoInputWrite, true, "a process drives an input or the clock"),
   (``CoreMemDesign.oblNoClockRead, true, "a process reads the clock"),
   (``CoreMemDesign.oblReset, true,
     "an asynchronous reset is not an input port other than the clock (F7: the route sees a reset the design drives only in a later slot), refused"),
   (``CoreMemDesign.oblEdgeOrder, false,
     "the design has several edge processes and one of them writes with a blocking assignment or to a select or concatenation: the edge order is not proved irrelevant for it (rule 4), refused"),
   (``CoreMemDesign.oblConverted, false,
     "an expression ingestion kept unconverted (a user function call, U5), refused")]

/-- The obligations stage on `E.seqOblB clk = true`, with a named refusal. -/
def runObligations (g : MVarId) : TacticM Unit := do
  if ← closes g (← `(tactic| sv_seq_obligations)) then
    setGoals [g]
    evalTactic (← `(tactic| sv_seq_obligations))
    return
  let ty ← instantiateMVars (← g.getType)
  let lhs := ty.getArg! 1
  let E := lhs.getArg! 0
  let clk := lhs.getArg! 1
  for (n, takesClk, msg) in obligations do
    let t := if takesClk then mkApp2 (mkConst n) E clk else mkApp (mkConst n) E
    let go ← mkFreshExprMVar (← mkEq t (toExpr true))
    unless ← closes go.mvarId! (← `(tactic| sv_seq_obligations)) do
      throwError "sv_structure: obligation `{n.componentsRev.head!}`: {msg}"
  throwError "sv_structure: the obligations do not hold (no single obligation identified)"

/-- The instantiation's three outcomes for `r = X.e P…`: the `ok` goal with `hSeq : <normal form> = E` substituted
away, the refused outcomes closed (or named). Returns the `ok` goal. -/
def runInst (stage : String) (r : Lean.Expr) : TacticM Unit := do
  let (eN, pN) ← familyNames stage r
  let eI := mkIdent eN
  let pI := mkIdent pN
  let hI := mkIdent `hSeqInst
  let rS ← Term.exprToSyntax r
  evalTactic (← `(tactic| cases $hI:ident : $rS:term))
  let gs ← getGoals
  let [gOk, gTo, gUn] := gs | throwError "{stage}: internal error: the instantiation's three outcomes expected"
  for g in [gTo, gUn] do
    setGoals [g]
    try
      evalTactic (← `(tactic| sv_seq_inst [$eI:ident, $pI:ident] at $hI:ident))
    catch _ => pure ()
    unless (← getGoals).isEmpty do
      let msg ← (do
        let h ← (← getMainGoal).withContext do getLocalDeclFromUserName `hSeqInst
        pure m!"{h.type}")
      throwError "{stage}: the route does not instantiate this design at these parameters; its outcome: {msg}"
  setGoals [gOk]
  try
    evalTactic (← `(tactic| sv_seq_inst [$eI:ident, $pI:ident] at $hI:ident))
  catch e =>
    throwError "{stage}: the instantiation does not normalize at these parameters (the clocked stages read the flat entry `X.e`; a module hierarchy is the later slice T9):\n{e.toMessageData}"
  evalTactic (← `(tactic| subst $hI:ident))

/-- `sv_structure` on `SeqDesign (X.e P…) clk`. -/
def runStructure (stx : Syntax) : TacticM Unit := do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOfArity ``SeqDesign 2 do throwUnsupportedSyntax
  guardSeq do
    unless stx[1].isNone && stx[2].isNone do
      throwError "sv_structure: a clocked goal takes no rank and no `using` clause"
    runInst "sv_structure" (ty.getArg! 0)
    evalTactic (← `(tactic| refine ⟨_, rfl, ?_, ?_⟩))
    let [gP, gO] ← getGoals | throwError "sv_structure: internal error: the profile and obligation goals expected"
    runProfile gP
    runObligations gO

/-- `sv_interface` on `SeqPorts (X.e P…) ins outs`. -/
def runInterface : TacticM Unit := do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOfArity ``SeqPorts 3 do throwUnsupportedSyntax
  guardSeq do
    runInst "sv_interface" (ty.getArg! 0)
    evalTactic (← `(tactic| refine ⟨_, rfl, ?_, ?_⟩))
    for g in ← getGoals do
      setGoals [g]
      try
        evalTactic (← `(tactic| sv_seq_ports))
      catch e =>
        throwError "sv_interface: the ports of the design differ from the statement's:\n{e.toMessageData}"

/-- `sv_equations` on `E.cycleV clk v d = rhs` with `hE : X.e P… = .ok E` in the context: the cycle computed, then `rhs`
checked against it. -/
def runEquations : TacticM Unit := do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).consumeMData.isAppOfArity ``CoreMemDesign.cycleV 4 do
    throwUnsupportedSyntax
  guardSeq do
    let lhs := (ty.getArg! 1).consumeMData
    let E := lhs.getArg! 0
    let mut hE? : Option (Name × Lean.Expr) := none
    for d in ← (← getMainGoal).getDecl <&> (·.lctx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``Eq 3 && (t.getArg! 2).isAppOfArity ``Res.ok 2 && (t.getArg! 2).appArg! == E then
        hE? := some (d.userName, t.getArg! 1)
    let some (hN, r) := hE?
      | throwError "sv_equations: no hypothesis `hE : X.e P… = .ok E` for the design of the cycle in the context"
    let (eN, pN) ← familyNames "sv_equations" r
    let eI := mkIdent eN
    let pI := mkIdent pN
    let hI := mkIdent hN
    let hC := mkIdent `hSeqCopy
    let cyc := mkIdent `hSeqCycle
    let lhsS ← Term.exprToSyntax lhs
    -- the width facts in the context (`x.width = n`) feed the evaluation pass
    let mut facts : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[← `(Lean.Parser.Tactic.simpLemma| List.length_nil)]
    let mut factNames : Array Name := #[]
    for d in ← (← getMainGoal).getDecl <&> (·.lctx) do
      if d.isImplementationDetail then continue
      let t := (← instantiateMVars d.type).consumeMData
      let isWidth : Bool :=
        t.isAppOfArity ``Eq 3 && (match (t.getArg! 1).consumeMData.getAppFn with
          | .const n _ => n == ``LeanModels.Sv.LVec.width
          | _ => false)
      if isWidth then
        facts := facts.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d.userName):ident))
        factNames := factNames.push d.userName
    evalTactic (← `(tactic| have $hC:ident := $hI:ident))
    evalTactic (← `(tactic| sv_seq_inst [$eI:ident, $pI:ident] at $hC:ident))
    evalTactic (← `(tactic| sv_seq_cycle $cyc : $lhsS using $hC [$facts,*]))
    let g0 ← getMainGoal
    let h ← g0.withContext do getLocalDeclFromUserName `hSeqCycle
    let computed := h.type
    try
      evalTactic (← `(tactic|
        (rw [$cyc:ident] <;> first | rfl | (simp [LeanModels.Sv.LVec.resizeU_of_width, $facts,*]; done))))
    catch _ =>
      throwError "sv_equations: the stated cycle differs from the computed one (width facts used: {factNames}); computed:\n{computed}"

end LeanModels.Sv.Kernel.SeqStage

open LeanModels.Sv.Kernel.SeqStage in
@[tactic svStructure] def evalSvStructureSeq : Tactic := fun stx => runStructure stx

open LeanModels.Sv.Kernel.SeqStage in
@[tactic svInterface] def evalSvInterfaceSeq : Tactic := fun _ => runInterface

open LeanModels.Sv.Kernel.SeqStage in
@[tactic svEquations] def evalSvEquationsSeq : Tactic := fun _ => runEquations
