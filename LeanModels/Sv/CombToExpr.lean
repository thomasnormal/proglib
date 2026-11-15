import LeanModels.Sv.CombView

/-!
# The summary as a literal (`ToExpr`), for the `sv_comb` tactics

The tactics evaluate the recognizer's summary natively (`evalSummary`) and close `d.summary = .ok ?s` once per run. Closed
by `rfl`, the metavariable `?s` becomes whatever the unifier's lazy weak-head evaluation of `d.summary` left: the
summary's constructor applied to unevaluated fields (`List.map (·.name) d.params ++ …`, `{ name := "a", … }.isInput`,
`(Aff.var "N").sub (Aff.const 1)`), and every later normalization (`simp` over the obligations of `sv_structure` and
`sv_equations`) evaluates those fields again, in every obligation. Measured on the Kogge-Stone adder of
`Examples/system-verilog/prefix_ks` (tac5 round): the summary term was 28 520 characters of such residue.

Here: `ToExpr` for the summary and every type it holds (the envelope's `PExpr`, `PProcess`, … included, derived here
because the tactics need them, without touching the files that define those types). With it the tactics instantiate
`?s` with the LITERAL of the natively evaluated summary and close `d.summary = .ok <literal>` by `Eq.refl`, checked by
the elaborator's `isDefEq` (one evaluation, about a thousand heartbeat units on that adder) and by the kernel. Nothing
is trusted: a literal that differed from `d.summary` would fail both checks (the tactic then falls back to `rfl`).
-/

open Lean LeanModels.Sv LeanModels.Sv.CombView

deriving instance ToExpr for Logic
deriving instance ToExpr for LVec
deriving instance ToExpr for BinOp
deriving instance ToExpr for UnaryOp
deriving instance ToExpr for SymBinOp
deriving instance ToExpr for SymUnaryOp
deriving instance ToExpr for SysFn
deriving instance ToExpr for PartMode
deriving instance ToExpr for RedOp
deriving instance ToExpr for PExpr
deriving instance ToExpr for PLhs
deriving instance ToExpr for CaseMode
deriving instance ToExpr for CaseCheck
deriving instance ToExpr for PStmt
deriving instance ToExpr for PProcess
deriving instance ToExpr for PDim
deriving instance ToExpr for CCmp
deriving instance ToExpr for LeanModels.Sv.CombView.CL
deriving instance ToExpr for XAt
deriving instance ToExpr for Aff
deriving instance ToExpr for LeanModels.Sv.CombView.Acc
deriving instance ToExpr for TSite
deriving instance ToExpr for DeclT
deriving instance ToExpr for GCmp
deriving instance ToExpr for Guard
deriving instance ToExpr for Hdr
deriving instance ToExpr for TItem
deriving instance ToExpr for TFam
deriving instance ToExpr for CECmp
deriving instance ToExpr for CE
deriving instance ToExpr for Summary

namespace LeanModels.Sv.CombView

open Meta in
/-- Close the goal `g : d.summary = .ok ?s` (`d` the design expression `pd`, `?s` unassigned) with the literal of the
summary `sv` that native evaluation of `fn pd` produced (`fn` the recognizer: `PDesign.summary`, or the proc-aware
`PDesign.summaryP`): `?s := toExpr sv`, `g := Eq.refl _`, after the
elaborator's `isDefEq` has checked the equation (the kernel checks it again). `false`, with nothing assigned, when the
goal has another shape (another design, another recognizer) or the check fails. -/
def closeSummaryLit (g : MVarId) (pd : Lean.Expr) (sv : Summary)
    (fn : Name := ``LeanModels.Sv.PDesign.summary) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? | return false
  unless lhs.isAppOfArity fn 1 && lhs.appArg! == pd do return false
  unless rhs.isAppOfArity ``Except.ok 3 do return false
  let sM := rhs.appArg!
  unless sM.isMVar do return false
  if ← sM.mvarId!.isAssigned then return false
  let saved ← saveState
  let lit := toExpr sv
  -- `?s` is a named hole (synthetic opaque: `isDefEq` would not assign it), so it is assigned directly, and the
  -- equation is then checked
  sM.mvarId!.assign lit
  let ok ← try withTransparency .default (isDefEq lhs (← instantiateMVars rhs))
    catch _ => pure false
  unless ok do
    saved.restore
    return false
  g.assign (← mkEqRefl (← instantiateMVars rhs))
  return true

end LeanModels.Sv.CombView
