import Lean
import LeanModels.Sv.CombViewTactic

/-!
# Plumbing for large obligation sets: closing in isolation, `omega` on the connected context

Two tools a player's closer needs on a design with many large obligations, moved here from the Dadda record's example
(`Examples/system-verilog/mul_dadda`), where they were written; both are opt in (new tactics), so no existing call
changes.

* `sv_isolated t` closes the main goal by `t` and keeps only the finished proof: it becomes an auxiliary lemma (checked
  by the kernel at its creation), and every intermediate state of the closing (assigned metavariables, the hypotheses
  of each split) is dropped. Closing 99 goals of up to 64 000 characters in one theorem kept those states alive until
  its end: memory grew by about 85 MB per goal and passed 8 GB; in isolation it stayed flat at about 3.1 GB.
* `sv_omega_connected [x, …]` is `omega` on the part of the context connected to the goal: the hypotheses that share a
  local with it, transitively, through every local but the named hubs (the parameters and localparams, which every
  hypothesis mentions), plus those about the hubs alone; an implication is never part of it. Where `omega` fails, the
  goal's own `if-then-else` conditions are split (decided in the goal only, so that its terms keep their form), then
  the hypotheses' (`iteGoalOmega`). On a two-site goal of the Dadda record the row-major rewriting with `omega` over the
  whole context took 3.4M heartbeats, with the connected part 95k. `sv_rowmajor_connected [x, …]` is `sv_rowmajor`'s
  rewriting with it as the discharger. A side condition that needs a hypothesis connected to it only through a hub is
  NOT shown by it: the reason it is a tactic of its own, not `sv_rowmajor`'s discharger.
-/

namespace LeanModels.Sv.CombView

open Lean Meta Elab Tactic

/-- Close the main goal by `tac`, keeping only the finished proof: it becomes an auxiliary lemma (checked by the kernel
there), and every intermediate state of the closing is dropped. The environment is kept across the restore: the proof
names the auxiliary lemmas `omega` added. -/
def closeIsolated (tac : TacticM Unit) : TacticM Unit := do
  let g ← getMainGoal
  let s ← saveState
  tac
  unless (← getGoals).isEmpty do throwError "isolated: goals left"
  let p ← instantiateMVars (mkMVar g)
  if p.hasMVar then throwError "isolated: the proof has metavariables"
  let ty ← instantiateMVars (← g.getType)
  let fvars ← g.withContext do
    return (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d.toExpr
  -- drop the closing's metavariables, keep its environment: the proof names the auxiliary lemmas `omega` added
  let env ← getEnv
  s.restore
  setEnv env
  let (t, v) ← g.withContext do pure (← mkForallFVars fvars ty, ← mkLambdaFVars fvars p)
  let n ← mkAuxLemma [] t v
  g.assign (mkAppN (mkConst n) fvars)
  replaceMainGoal []

/-- `sv_isolated t`: close the main goal by `t` in isolation (`closeIsolated`), without info trees. -/
elab "sv_isolated " t:tactic : tactic => withEnableInfoTree false <| closeIsolated (evalTactic t)

/-- `omega`; failing that, a split on the first condition of an `if-then-else` of the goal (decided in the goal only, so
that its terms keep their form), at most `fuel` deep; with the goal free of them, a split on a condition of the
hypotheses' (decided everywhere at once), at most `hfuel` deep. -/
partial def iteGoalOmega (fuel : Nat) (hfuel : Nat := 2) : TacticM Unit := do
  let saved ← saveState
  try
    evalTactic (← `(tactic| omega))
    return
  catch e =>
    saved.restore
    if fuel = 0 then throw e
  let g ← getMainGoal
  let goalT ← instantiateMVars (← g.getType)
  match (iteConds goalT #[])[0]? with
  | some c =>
    let cStx ← g.withContext (Term.exprToSyntax c)
    evalTactic (← `(tactic| by_cases hdi : $cStx))
    for g' in ← getGoals do
      setGoals [g']
      try evalTactic (← `(tactic| first | simp only [eq_true hdi, ↓reduceIte] at ⊢ | simp only [eq_false hdi, ↓reduceIte] at ⊢))
      catch _ => pure ()
      unless (← getGoals).isEmpty do iteGoalOmega (fuel - 1) hfuel
    setGoals []
  | none =>
    -- the conditions of the hypotheses' `if-then-else` terms (the context is the side condition's connected part
    -- already), decided everywhere at once so that the atoms stay consistent
    if hfuel = 0 then throwError "iteGoalOmega: no condition left"
    let c? ← g.withContext do
      let mut cs : Array Lean.Expr := #[]
      for d in ← getLCtx do
        unless d.isImplementationDetail do cs := iteConds (← instantiateMVars d.type) cs
      pure cs[0]?
    let some c := c? | throwError "iteGoalOmega: no condition left"
    let cStx ← g.withContext (Term.exprToSyntax c)
    evalTactic (← `(tactic| by_cases hdi : $cStx))
    for g' in ← getGoals do
      setGoals [g']
      try evalTactic (← `(tactic| simp only [hdi, if_true, if_false, ↓reduceIte, not_false_eq_true] at *))
      catch _ => pure ()
      unless (← getGoals).isEmpty do iteGoalOmega fuel (hfuel - 1)
    setGoals []

/-- The main goal with every hypothesis cleared that is not connected to it: connected through a local other than the
`hubs` (by user name), transitively, or about the hubs alone; implications are never kept. -/
def connectedPart (g : MVarId) (hubs : Array Name) : MetaM MVarId := g.withContext do
  let lctx ← getLCtx
  let isHub (f : FVarId) : Bool := hubs.contains (lctx.get! f).userName.eraseMacroScopes
  let fvs (e : Lean.Expr) : Array FVarId := (Lean.collectFVars {} e).fvarIds
  let mut reach : Std.HashSet FVarId := {}
  for f in fvs (← instantiateMVars (← g.getType)) do reach := reach.insert f
  let decls := lctx.foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
  let mut keep : Std.HashSet FVarId := {}
  let mut props : Array (FVarId × Array FVarId) := #[]
  for d in decls do
    let ty ← instantiateMVars d.type
    if ← Meta.isProp ty then
      unless ty.isForall do props := props.push (d.fvarId, (fvs ty).filter (!isHub ·))
    else keep := keep.insert d.fvarId
  let mut changed := true
  while changed do
    changed := false
    for (h, nonHub) in props do
      if keep.contains h then continue
      if nonHub.isEmpty || nonHub.any reach.contains then
        keep := keep.insert h
        for f in nonHub do reach := reach.insert f
        changed := true
  g.tryClearMany (decls.filter (fun d => !keep.contains d.fvarId) |>.map (·.fvarId))

/-- `sv_omega_connected [x, …]`: `omega` on the connected part of the context (`connectedPart`, the named locals as
hubs), with the `if-then-else` splits of `iteGoalOmega` (at most 4 deep), within 200k heartbeats. -/
syntax (name := svOmegaConnected) "sv_omega_connected" " [" ident,* "]" : tactic

@[tactic svOmegaConnected] def evalSvOmegaConnected : Tactic := fun stx => do
  -- by user name: an identifier from a quotation carries macro scopes
  let hubs := stx[2].getSepArgs.map (·.getId.eraseMacroScopes)
  let g ← getMainGoal
  setGoals [← connectedPart g hubs]
  let now ← IO.getNumHeartbeats
  let ok ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := 200000 * 1000, initHeartbeats := now }) do
      iteGoalOmega 4
      pure true)
    (fun _ => pure false)
  unless ok do throwError "sv_omega_connected: not shown"

/-- `sv_rowmajor`'s rewriting (the same lemmas, `CombViewTactic.lean`) with `sv_omega_connected [x, …]` as the
discharger of its side conditions. -/
macro "sv_rowmajor_connected" " [" hubs:ident,* "]" : tactic =>
  `(tactic| (try simp (disch := sv_omega_connected [$hubs,*]) only [LeanModels.Sv.CombView.rmN_add_col,
      LeanModels.Sv.CombView.rmN_lt_iff, LeanModels.Sv.CombView.rmN_le_iff,
      LeanModels.Sv.CombView.rmN_cast_lt_iff, LeanModels.Sv.CombView.rmN_cast_le_iff,
      LeanModels.Sv.CombView.rmN_cast_eq_iff, ↓LeanModels.Sv.CombView.rmN3_plane_end,
      ↓LeanModels.Sv.CombView.rmN3_plane_end_k,
      and_true, true_and] at *))

end LeanModels.Sv.CombView
