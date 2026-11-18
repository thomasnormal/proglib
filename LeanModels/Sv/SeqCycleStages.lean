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
| `sv_structure` | `SeqDesign (X.e P…) clk` | the instantiation at symbolic parameters, the single-clock profile, the obligations |
| `sv_structure` | `SeqDesignI (X.e P…)` | the same for any number of events (any clocks, either edge): the instant profile and obligations |
| `sv_interface` | `SeqPorts (X.e P…) ins outs` | the instantiation, the ports |
| `sv_equations` | `E.cycleV clk v d = rhs` or `E.cycleMV clk σ d = rhs`, with `hE : X.e P… = .ok E` in the context | the cycle equations, computed (with the context's width facts `x.width = n`), then `rhs` checked against them |
| `sv_equations` | `E.tick i σ = rhs`, `E.dataV σ d = rhs` or `E.slotV v mv r = rhs` (any number of events), `hE` in the context | one instant's (or one row's) equations, computed and checked the same way: one equation set per event |
| `sv_domains` | any goal, `hE : X.e P… = .ok E` in the context | adds `hevents : E.events = …`, `hdomains : E.domains = …`, `hcrossings : E.crossings = …` (computed) and reports them |

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

/-- The svKind of the first statement ingestion kept unconverted (`PStmt.unsupported kind _`) inside a term. -/
def unsupportedStmtKind? (e : Lean.Expr) : Option String :=
  match e.find? (fun x => x.isAppOfArity ``PStmt.unsupported 2) with
  | some u => strLit? (u.getArg! 0)
  | none => none

/-- Why a process of the normal form is outside the clocked profile (the `procOkB` check failed on it; `clk? = some clk`
for the single-clock profile, `none` for the instant profile; `resolved` the design's nets with several continuous
drivers, `CoreMemDesign.resolvedNets`). -/
def whyProc (clk? : Option String) (i : Nat) (p : Lean.Expr) (resolved : List String := []) : MetaM String := do
  let p ← whnf p
  let at_ := s!"process {i}"
  if p.isAppOfArity ``CoreMemProc.edge 1 then
    let f ← whnf (p.getArg! 0)
    if f.isAppOf ``CoreMemEdge.mk then
      -- fields by projection, not by position: the record gains fields as the route grows
      if let some clk := clk? then
        let clock := strLit? (← whnf (← mkProjection f `clock))
        if clock.isSome && clock != some clk then
          return s!"{at_} (an edge process) is clocked by `{clock.get!}`, not `{clk}`: outside the single-clock profile `posedge {clk}`; state the design over instants (`SeqDesignI`, `SeqRunsI`)"
        let edge ← whnf (← mkProjection f `edge)
        if edge.isConstOf ``ClockEdge.negedge then
          return s!"{at_} (an edge process) is sensitive to the falling edge of `{clk}`: outside the single-clock profile `posedge {clk}`; over instants `\{negedge {clk}}` is an instant of its own (`SeqDesignI`, `SeqRunsI`)"
      let body ← whnf (← mkProjection f `body)
      if (body.find? (·.isConstOf ``PStmt.forLoop)).isSome then
        return s!"{at_} (an edge process) has a procedural `for` loop: the memories slice (next), refused"
      if (body.find? (·.isConstOf ``PExpr.functionCall)).isSome then
        return s!"{at_} (an edge process) calls a function: outside the clocked profile (U5)"
      if (body.find? (·.isConstOf ``PExpr.aggregateMember)).isSome then
        return s!"{at_} (an edge process) reads an unpacked aggregate member (a struct field or an aggregate element, §7.2, §7.4): the clocked views carry no aggregate store, refused"
      if (body.find? (·.isConstOf ``PStmt.unsupported)).isSome then
        match unsupportedStmtKind? body with
        | some k => return s!"{at_} (an edge process) holds a statement ingestion kept unconverted ({k}), refused"
        | none => return s!"{at_} (an edge process) holds a statement ingestion kept unconverted"
      return s!"{at_} (an edge process): its body is outside the edge-body fragment the clocked stages mirror"
    return s!"{at_} (an edge process): outside the clocked profile"
  if p.isAppOfArity ``CoreMemProc.event 2 then
    return s!"{at_} is a plain `always` with an explicit event list (`always @(a or b)`, kept as an event process): its event control is not one clock edge with an optional asynchronous reset, outside the clocked profile, refused"
  if p.isAppOfArity ``CoreMemProc.comb 1 then
    return s!"{at_} is an always_comb process: always_comb beside flip-flops is the next slice (T7), refused"
  if p.isAppOfArity ``CoreMemProc.latch 1 then
    return s!"{at_} is an always_latch process: a level-sensitive process is outside the clocked profile, refused"
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
    if (v.find? (·.isConstOf ``PExpr.functionCall)).isSome then
      return s!"{at_} (a continuous assign) calls a function: outside the clocked profile (U5)"
    if (v.find? (·.isConstOf ``PExpr.aggregateMember)).isSome then
      return s!"{at_} (a continuous assign) reads an unpacked aggregate member (a struct field or an aggregate element, §7.2, §7.4): the clocked views carry no aggregate store, refused"
    if let some n := strLit? (← whnf (t.getArg! 0)) then
      if resolved.contains n then
        return s!"{at_} (a continuous assign) drives `{n}`, a net with several continuous drivers: the clocked views do not model the §6.6 driver resolution (`resolvedNets`), refused"
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

/-- The profile stage on `E.SeqProfile clk` or `E.SeqProfileI` (`E` the normal form), with a named refusal. -/
def runProfile (g : MVarId) : TacticM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let single := ty.isAppOfArity ``CoreMemDesign.SeqProfile 2
  let tac ← if single then `(tactic| sv_seq_profile) else `(tactic| sv_seq_profileI)
  if ← closes g tac then
    setGoals [g]
    evalTactic tac
    return
  let E := ty.getArg! 0
  let clkE ← if single then whnf (ty.getArg! 1) else pure (ty.getArg! 0)
  let clk? : Option String := if single then some ((strLit? clkE).getD "?") else none
  let gm ← mkFreshExprMVar (← mkEq (mkApp (mkConst ``CoreMemDesign.memOkB) E) (toExpr true))
  unless ← closes gm.mvarId! (← `(tactic| sv_seq_prof_mems)) do
    throwError "sv_structure: a memory is outside the clocked profile (memories of distinct names and identities, 4-state elements, none a port), refused"
  let some ps ← arrayElems (← whnf (mkApp (mkConst ``CoreMemDesign.processes) E))
    | throwError "sv_structure: the clocked profile does not hold (the processes are not a literal list at these parameters)"
  let resolved : List String ← do
    match ← listElems (mkApp (mkConst ``CoreMemDesign.resolvedNets) E) with
    | some ns => pure (← ns.mapM fun n => do pure ((strLit? (← whnf n)).getD "?"))
    | none => pure []
  let mut i := 0
  for p in ps do
    let t := match clk? with
      | some clk => mkApp4 (mkConst ``CoreMemDesign.procOkB) E (toExpr clk) (toExpr i) p
      | none => mkApp3 (mkConst ``CoreMemDesign.procOkIB) E (toExpr i) p
    let gp ← mkFreshExprMVar (← mkEq t (toExpr true))
    unless ← closes gp.mvarId! (← `(tactic| simp (config := {decide := true}) [
        LeanModels.Sv.Kernel.CoreMemDesign.procOkB, LeanModels.Sv.Kernel.CoreMemDesign.procOkIB,
        LeanModels.Sv.PStmt.edgeOkB, LeanModels.Sv.PStmt.optEdgeOkB,
        LeanModels.Sv.PLhs.hasCall, LeanModels.Sv.PLhs.hasCallList,
        LeanModels.Sv.PStmt.listEdgeOkB, LeanModels.Sv.PStmt.itemsEdgeOkB, LeanModels.Sv.PStmt.need,
        LeanModels.Sv.PStmt.optNeed, LeanModels.Sv.PStmt.listNeed, LeanModels.Sv.PStmt.itemsNeed,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCallList,
        LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?, LeanModels.Sv.Kernel.Elab.resolve,
        LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf])) do
      throwError "sv_structure: {← whyProc clk? i p resolved}"
    i := i + 1
  let gr ← mkFreshExprMVar (← mkEq (mkApp (mkConst ``CoreMemDesign.resolvedNets) E)
    (← mkAppOptM ``List.nil #[mkConst ``String]))
  unless ← closes gr.mvarId! (← `(tactic| sv_seq_prof_resolved)) do
    throwError "sv_structure: the design has a net with several continuous drivers ({String.intercalate ", " resolved}): the clocked views do not model the §6.6 driver resolution (`resolvedNets` is not empty), refused"
  -- The memories, every process and the resolved nets pass: name the conjunct of the profile that does not close.
  let ofB ← if single then
      `(tactic| refine LeanModels.Sv.Kernel.CoreMemDesign.SeqProfile.of_B ?_ ?_ ?_ ?_ ?_ ?_)
    else `(tactic| refine LeanModels.Sv.Kernel.CoreMemDesign.SeqProfileI.of_B ?_ ?_ ?_ ?_ ?_ ?_)
  let procs ← if single then `(tactic| sv_seq_prof_procs) else `(tactic| sv_seq_prof_procsI)
  let procsName := if single then "procsOkFrom" else "procsOkIFrom"
  let s ← saveState
  let tRfl ← `(tactic| rfl)
  let tNames ← `(tactic| sv_seq_prof_names)
  let tFour ← `(tactic| sv_seq_prof_four)
  let reason : String ← tryCatch (do
      setGoals [g]
      evalTactic ofB
      match ← getGoals with
      | [_, gb, gn, g4, _, gp] =>
          if !(← closes gb tRfl) then
            pure "the edge view's declarations are not the scalar view's (`scalarEdge.base = scalar` does not hold by `rfl`)"
          else if !(← closes gn tNames) then
            pure "two declarations of the scalar view share a name"
          else if !(← closes g4 tFour) then
            pure "a declaration is 2-state (`bit`, `int`, …): the clocked views are 4-state (`AllFour`)"
          else if !(← closes gp procs) then
            pure s!"every process passes its own check, but the whole-list check (`{procsName}`) does not close on the normal form: a limit of the tactic, not a property of the design; report it"
          else
            pure "each conjunct closes alone, but not together: report it"
      | _ => pure "the profile's conjuncts could not be separated: report it")
    (fun _ => pure "the profile's conjuncts could not be separated: report it")
  s.restore
  throwError "sv_structure: the clocked profile does not hold: {reason}, refused"

/-- The named obligations, in the order they are checked, with the reason each refuses (`true`: the obligation takes
the clock: single clock only). -/
def obligations : List (Name × Bool × String) :=
  [(``CoreMemDesign.oblDrivers, false, "two processes drive the same signal (one driver per signal)"),
   (``CoreMemDesign.topoC, false,
     "a continuous assign reads its own target or a later assign's target: the route's settle would be stale (U1), refused"),
   (``CoreMemDesign.oblInputsUndriven, false,
     "a process drives an input port (an event source the design drives would cause an event inside the slot, which the clocked view does not model), refused"),
   (``CoreMemDesign.oblSources, false,
     "an event source (a clock or an asynchronous reset) is not a one-bit input port of the design (an internally generated clock or reset is the scheduler's), refused"),
   (``CoreMemDesign.oblNoSourceRead, false,
     "a process reads an event source as data (a continuous assign reading a clock or reset, or an edge body reading a clock or another process's reset: in an instant it could read either value, §4.7), refused"),
   (``CoreMemDesign.oblNoInputWrite, true, "a process drives an input or the clock (an event source the design drives is outside the clocked view), refused"),
   (``CoreMemDesign.oblNoClockRead, true, "a process reads the clock"),
   (``CoreMemDesign.oblReset, true,
     "an asynchronous reset is not an input port other than the clock (a reset the design drives would cause an event inside the slot, which the clocked view does not model), refused"),
   (``CoreMemDesign.oblEdgeOrder, false,
     "the design has several edge processes and one of them writes with a blocking assignment or to a select or concatenation: the edge order is not proved irrelevant for it (rule 4), refused"),
   (``CoreMemDesign.oblConverted, false,
     "an expression ingestion kept unconverted (a user function call, U5), refused"),
   (``CoreMemDesign.oblClockInput, true, "the clock is not an input port of the design, refused")]

/-- The obligations stage on `E.seqOblB clk = true` or `E.seqOblI = true`, with a named refusal. -/
def runObligations (g : MVarId) : TacticM Unit := do
  if ← closes g (← `(tactic| sv_seq_obligations)) then
    setGoals [g]
    evalTactic (← `(tactic| sv_seq_obligations))
    return
  let ty ← instantiateMVars (← g.getType)
  let lhs := ty.getArg! 1
  let E := lhs.getArg! 0
  let clk? := if lhs.isAppOfArity ``CoreMemDesign.seqOblB 2 then some (lhs.getArg! 1) else none
  for (n, takesClk, msg) in obligations do
    if takesClk && clk?.isNone then continue
    let t := match clk?, takesClk with
      | some clk, true => mkApp2 (mkConst n) E clk
      | _, _ => mkApp (mkConst n) E
    let go ← mkFreshExprMVar (← mkEq t (toExpr true))
    unless ← closes go.mvarId! (← `(tactic| sv_seq_obligations)) do
      throwError "sv_structure: obligation `{n.componentsRev.head!}`: {msg}"
  throwError "sv_structure: the obligations do not hold (no single obligation identified)"

/-- The cached instantiation of a family `X.e`, when `seq_mirror` made one: `X.mirror` and `X.mirror_eq`. -/
def mirrorOf (eN : Name) : MetaM (Option (Name × Name × Name)) := do
  let mN := eN.getPrefix ++ `mirror
  let mEq := eN.getPrefix ++ `mirror_eq
  let mDef := eN.getPrefix ++ `mirror_def
  if (← getEnv).contains mEq then return some (mN, mEq, mDef) else return none

/-- The instantiation's three outcomes for `r = X.e P…`: the `ok` goal with `hSeq : <normal form> = E` substituted
away, the refused outcomes closed (or named). Returns the `ok` goal. -/
def runInst (stage : String) (r : Lean.Expr) : TacticM Unit := do
  let (eN, pN) ← familyNames stage r
  let eI := mkIdent eN
  let pI := mkIdent pN
  let hI := mkIdent `hSeqInst
  let rS ← Term.exprToSyntax r
  -- a cached instantiation (`seq_mirror`): the family member IS its mirror, no instantiation pass
  if let some (mN, mEq, mDef) ← mirrorOf eN then
    let mS ← Term.exprToSyntax (mkAppN (mkConst mN) r.getAppArgs)
    evalTactic (← `(tactic| have $hI:ident : $rS:term = .ok $mS:term := by apply $(mkIdent mEq) <;> omega))
    evalTactic (← `(tactic| rw [$hI:ident, $(mkIdent mDef):ident]))
    return
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

/-- `sv_structure` on `SeqDesign (X.e P…) clk` or `SeqDesignI (X.e P…)`. -/
def runStructure (stx : Syntax) : TacticM Unit := do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOfArity ``SeqDesign 2 || ty.isAppOfArity ``SeqDesignI 1 do throwUnsupportedSyntax
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
  unless ty.isAppOfArity ``Eq 3 && ((ty.getArg! 1).consumeMData.isAppOfArity ``CoreMemDesign.cycleV 4 ||
      (ty.getArg! 1).consumeMData.isAppOfArity ``CoreMemDesign.cycleMV 4 ||
      (ty.getArg! 1).consumeMData.isAppOfArity ``CoreMemDesign.tick 3 ||
      (ty.getArg! 1).consumeMData.isAppOfArity ``CoreMemDesign.dataV 3 ||
      (ty.getArg! 1).consumeMData.isAppOfArity ``CoreMemDesign.slotV 4) do
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
    if let some (mN, mEq, mDef) ← mirrorOf eN then
      let rS ← Term.exprToSyntax r
      let mS ← Term.exprToSyntax (mkAppN (mkConst mN) r.getAppArgs)
      let hMI := mkIdent `hSeqMir
      evalTactic (← `(tactic| have $hMI:ident : $rS:term = .ok $mS:term := by apply $(mkIdent mEq) <;> omega))
      evalTactic (← `(tactic| rw [$hMI:ident, $(mkIdent mDef):ident] at $hC:ident))
      evalTactic (← `(tactic| replace $hC:ident := Res.ok.inj $hC:ident))
    else
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

/-- `sv_domains`: the events, the domains and the crossings of the design of `hE : X.e P… = .ok E`, computed on its
normal form, added as hypotheses and reported. -/
def runDomains : TacticM Unit := do
  let goal ← getMainGoal
  let mut hE? : Option (Name × Lean.Expr × Lean.Expr) := none
  for d in ← goal.getDecl <&> (·.lctx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Eq 3 && (t.getArg! 2).isAppOfArity ``Res.ok 2 &&
        ((t.getArg! 1).getAppFn.constName?.map (·.toString.endsWith ".e")).getD false then
      hE? := some (d.userName, t.getArg! 1, (t.getArg! 2).appArg!)
  let some (hN, r, E) := hE?
    | throwError "sv_domains: no hypothesis `hE : X.e P… = .ok E` in the context"
  let (eN, pN) ← familyNames "sv_domains" r
  let hC := mkIdent `hSeqDom
  evalTactic (← `(tactic| have $hC:ident := $(mkIdent hN):ident))
  if let some (mN, mEq, mDef) ← mirrorOf eN then
    let rS ← Term.exprToSyntax r
    let mS ← Term.exprToSyntax (mkAppN (mkConst mN) r.getAppArgs)
    let hMI := mkIdent `hSeqDomMir
    evalTactic (← `(tactic| have $hMI:ident : $rS:term = .ok $mS:term := by apply $(mkIdent mEq) <;> omega))
    evalTactic (← `(tactic| rw [$hMI:ident, $(mkIdent mDef):ident] at $hC:ident))
    evalTactic (← `(tactic| replace $hC:ident := Res.ok.inj $hC:ident))
  else
    evalTactic (← `(tactic| sv_seq_inst [$(mkIdent eN):ident, $(mkIdent pN):ident] at $hC:ident))
  let ES ← Term.exprToSyntax E
  for (nm, fn) in [(`hevents, ``CoreMemDesign.events), (`hdomains, ``CoreMemDesign.domains),
      (`hcrossings, ``CoreMemDesign.crossings)] do
    let h := mkIdent nm
    let fI := mkIdent fn
    evalTactic (← `(tactic| have $h:ident := (rfl : $fI $ES = $fI $ES)))
    evalTactic (← `(tactic| conv at $h:ident => rhs; rw [← $hC:ident]; simp (config := {maxSteps := 4000000, decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.events,
      LeanModels.Sv.Kernel.CoreMemProc.events, LeanModels.Sv.Kernel.CoreMemEdge.events,
      LeanModels.Sv.Kernel.CoreMemEdge.clockEvent, LeanModels.Sv.Kernel.CoreMemEdge.resetEvent?,
      LeanModels.Sv.Kernel.CoreMemDesign.domains, LeanModels.Sv.Kernel.CoreMemDesign.domainOf,
      LeanModels.Sv.Kernel.CoreMemDesign.stateReads, LeanModels.Sv.Kernel.CoreMemDesign.crossings,
      LeanModels.Sv.Kernel.CoreMemProc.domain?, LeanModels.Sv.Kernel.dedupL, LeanModels.Sv.Kernel.CoreMemProc.targets,
      LeanModels.Sv.Kernel.CoreMemProc.isEdge, LeanModels.Sv.PStmt.writes, LeanModels.Sv.PStmt.optWrites,
      LeanModels.Sv.PStmt.listWrites, LeanModels.Sv.PStmt.itemsWrites, LeanModels.Sv.PLhs.baseNames,
      LeanModels.Sv.PLhs.baseNamesList, LeanModels.Sv.PStmt.readNames, LeanModels.Sv.PStmt.optReadNames,
      LeanModels.Sv.PStmt.listReadNames, LeanModels.Sv.PStmt.itemsReadNames, LeanModels.Sv.PLhs.indexNames,
      LeanModels.Sv.PLhs.indexNamesList, LeanModels.Sv.PExpr.sigNames, LeanModels.Sv.PExpr.sigNamesList,
      List.filterMap_cons, List.filterMap_nil, List.eraseDups_cons, List.eraseDups_nil]))
    let g ← getMainGoal
    let hd ← g.withContext do getLocalDeclFromUserName nm
    logInfo m!"sv_domains: {nm}: {hd.type}"

end LeanModels.Sv.Kernel.SeqStage

/-- **`sv_domains`**: the events, the domains (each clock event with the registers it writes) and the crossings (reads
of another domain's registers, directly or through continuous assigns) of the design of `hE : X.e P… = .ok E`,
computed on its normal form, added as hypotheses `hevents`, `hdomains`, `hcrossings` and reported. -/
syntax (name := svDomains) "sv_domains" : tactic

open LeanModels.Sv.Kernel.SeqStage in
@[tactic svDomains] def evalSvDomains : Tactic := fun _ => runDomains

/-- **`seq_mirror (P : Nat) (h : …) … : X.e P…`**: the instantiation of a loaded family at its symbolic parameters,
computed ONCE: defines `X.mirror P… : CoreMemDesign` (the normal form the instantiation pass computes), states its
unfolding `X.mirror_def` (by definition; a declaration added this way has no equation lemma for `simp`) and proves
`X.mirror_eq : ∀ P… h…, X.e P… = .ok (X.mirror P…)`. The clocked stages (`sv_structure`, `sv_interface`,
`sv_equations`) read the mirror when it exists, so a file stops re-running the instantiation pass per theorem; a proof
uses it as `rw [X.mirror_eq …]`. Nothing is trusted: the theorem is proved by the instantiation pass, kernel-checked. -/
syntax (name := seqMirrorCmd) "seq_mirror" bracketedBinder* " : " term : command

open Lean Elab Command Term Meta in
@[command_elab seqMirrorCmd] def elabSeqMirror : CommandElab := fun stx => do
  let bs := stx[1].getArgs
  let fam := stx[3]
  liftTermElabM do
    Term.elabBinders bs fun xs => do
      let famE ← Term.elabTerm fam (some (mkApp (Lean.mkConst ``LeanModels.Sv.Res)
        (Lean.mkConst ``LeanModels.Sv.Kernel.CoreMemDesign)))
      Term.synthesizeSyntheticMVarsNoPostponing
      let famE ← instantiateMVars famE
      let some eName := famE.getAppFn.constName?
        | throwError "seq_mirror: the family is not a loaded `X.e P…`"
      let pName := eName.getPrefix ++ `pdesign
      let mName := eName.getPrefix ++ `mirror
      let mEqName := eName.getPrefix ++ `mirror_eq
      let eI := mkIdent eName
      let pI := mkIdent pName
      -- the normal form: the instantiation pass on `hE : X.e P… = .ok E`
      let cmd := Lean.mkConst ``LeanModels.Sv.Kernel.CoreMemDesign
      let goalTy ← withLocalDeclD `E cmd fun E => do
        let eq ← mkEq famE (← mkAppM ``LeanModels.Sv.Res.ok #[E])
        mkForallFVars #[E] (← mkArrow eq (Lean.mkConst ``True))
      let g ← mkFreshExprMVar goalTy
      let nfRef ← IO.mkRef (none : Option Lean.Expr)
      let _ ← Tactic.run g.mvarId! do
        let hEI := mkIdent `hSeqMirE
        Tactic.evalTactic (← `(tactic| intro E $hEI:ident))
        Tactic.evalTactic (← `(tactic| sv_seq_inst [$eI:ident, $pI:ident] at $hEI:ident))
        let h ← (← Tactic.getMainGoal).withContext do getLocalDeclFromUserName `hSeqMirE
        let t ← instantiateMVars h.type
        unless t.isAppOfArity ``Eq 3 do throwError "seq_mirror: the instantiation did not normalize: {t}"
        nfRef.set (some (t.getArg! 1))
        Tactic.evalTactic (← `(tactic| trivial))
      let some nf ← nfRef.get | throwError "seq_mirror: no normal form"
      let natXs ← xs.filterM fun x => do return !(← isProp (← inferType x))
      let propXs ← xs.filterM fun x => do return (← isProp (← inferType x))
      if propXs.any (fun p => nf.containsFVar p.fvarId!) then
        throwError "seq_mirror: the normal form depends on a hypothesis"
      let val ← instantiateMVars (← mkLambdaFVars natXs nf)
      let vty ← instantiateMVars (← inferType val)
      let dv : DefinitionVal :=
        { name := mName, levelParams := [], type := vty, value := val, hints := .regular 0, safety := .safe }
      addDecl (Declaration.defnDecl dv)
      -- its unfolding, by definition
      let mDefName := eName.getPrefix ++ `mirror_def
      let defTy ← instantiateMVars (← mkForallFVars natXs (← mkEq (mkAppN (Lean.mkConst mName) natXs) nf))
      let defVal ← instantiateMVars (← mkLambdaFVars natXs (← mkEqRefl nf))
      let dtv : TheoremVal := { name := mDefName, levelParams := [], type := defTy, value := defVal }
      addDecl (Declaration.thmDecl dtv)
      -- the theorem, proved by the instantiation pass once more
      let stmt ← mkEq famE (← mkAppM ``LeanModels.Sv.Res.ok #[mkAppN (Lean.mkConst mName) natXs])
      let pf ← mkFreshExprMVar stmt
      let rS ← Term.exprToSyntax famE
      let mDefI := mkIdent (eName.getPrefix ++ `mirror_def)
      let rest ← Tactic.run pf.mvarId! do
        Tactic.evalTactic (← `(tactic| cases hSeqM : $rS:term with
          | ok E => (sv_seq_inst [$eI:ident, $pI:ident] at hSeqM; subst hSeqM; rw [$mDefI:ident])
          | timeout => sv_seq_inst [$eI:ident, $pI:ident] at hSeqM
          | unsupported m => sv_seq_inst [$eI:ident, $pI:ident] at hSeqM))
      unless rest.isEmpty do throwError "seq_mirror: the instantiation's equation was not proved"
      let pf ← instantiateMVars pf
      if pf.hasMVar then throwError "seq_mirror: the instantiation's proof has metavariables"
      Term.synthesizeSyntheticMVarsNoPostponing
      let thmTy ← instantiateMVars (← mkForallFVars xs stmt)
      let thmVal ← instantiateMVars (← mkLambdaFVars xs pf)
      if thmTy.hasMVar || thmVal.hasMVar || thmTy.hasLevelMVar || thmVal.hasLevelMVar then
        throwError "seq_mirror: the statement has unassigned metavariables (state the binders' types fully)"
      let tv : TheoremVal := { name := mEqName, levelParams := [], type := thmTy, value := thmVal }
      addDecl (Declaration.thmDecl tv)

/-- **`sv_seq_use [X.mirror_eq P… h…, X.mirror_def] at hE`**: `hE : X.e P… = .ok E` becomes `hE : <normal form> = E`
from the cached instantiation (`seq_mirror`), the form `sv_seq_inst` leaves, without an instantiation pass. -/
macro "sv_seq_use " "[" rs:Lean.Parser.Tactic.rwRule,* "]" " at " h:ident : tactic =>
  `(tactic| (rw [$rs,*] at $h:ident; replace $h:ident := LeanModels.Sv.Res.ok.inj $h:ident))

open LeanModels.Sv.Kernel.SeqStage in
@[tactic svStructure] def evalSvStructureSeq : Tactic := fun stx => runStructure stx

open LeanModels.Sv.Kernel.SeqStage in
@[tactic svInterface] def evalSvInterfaceSeq : Tactic := fun _ => runInterface

open LeanModels.Sv.Kernel.SeqStage in
@[tactic svEquations] def evalSvEquationsSeq : Tactic := fun _ => runEquations
