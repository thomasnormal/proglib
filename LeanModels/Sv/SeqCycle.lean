import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Kernel.Core0Obs
import LeanModels.Sv.Kernel.Core1Edge

/-!
# The clock cycle of the ordinary E route, derived (`LeanModels.Sv.Kernel`, the clocked tactics' theory)

**Status: derived from the ordinary E route** (the loader's `X.e`, `PDesign.instantiateE2`, and its slot function
`CoreMemDesign.step`). Nothing here is a semantics: every definition is a function of the route's own data, and every
theorem relates it to `CoreMemDesign.step`.

A clock cycle is two slots under the rising-edge clocking discipline (`Core1Disc`, `Core1Obs.slotEntry1`): the LOW slot
carries the cycle's data inputs with the clock at 0 (`lowEntry`), the HIGH slot raises the clock and changes nothing
else (`highEntry`). The pre sample is the state after the low slot, the post sample the state after the high slot.

* `CoreMemDesign.evalV`, `evalIdxV`, `evalListV`: the route's expression evaluator (`evalExprLocals`) with the store
  replaced by its VIEW (the name-to-value list `evalPure2` reads), for a design without memories; equal to it
  (`evalExprLocals_eq_evalV`) on function-free expressions.
* `CoreMemDesign.nbaQ`: the nonblocking updates an NBA-only edge body issues on a view; `execStmtFuel_nba`: the route's
  edge-body executor leaves the state alone and issues exactly them, at every fuel from the body's need on.
* `SeqProfile E clk`: the clocked profile (slice 1): one clock, edge processes with NBA-only bodies over whole scalars,
  continuous assigns with their compiled expressions, no memory, no always_comb, no initial, no asynchronous reset,
  4-state declarations with distinct names.
* `CoreMemDesign.Coherent`: a state whose store is its cache's, one typed value per declaration.
* `CoreMemDesign.settleV`, `slotV`, `cycleV`: the slot and the cycle on views, mirroring `CoreMemDesign.step` pass for
  pass (four continuous-assign passes per slot, as the route makes them).
* **`CoreMemDesign.step_low`, `step_high`, `cycle_of_seqProfile`**: the refinement theorems: from every coherent state,
  the route's two slots exist, stay coherent, and land exactly on the views `cycleV` computes.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## The clocking discipline's slot entries -/

/-- The low slot of a cycle: the cycle's data inputs, the clock at 0. -/
def lowEntry (clk : String) (data : SvState) : SvState := (clk, ⟨#[.l0]⟩) :: data

/-- The high slot of a cycle: the clock raised, nothing else changed. -/
def highEntry (clk : String) : SvState := [(clk, ⟨#[.l1]⟩)]

/-- The slot entries of a run of cycles, two per cycle. -/
def cycleRows (clk : String) : List SvState → List SvState
  | [] => []
  | d :: ds => lowEntry clk d :: highEntry clk :: cycleRows clk ds

/-! ## The route's expression evaluator on a view -/

/-- The evaluation width table `evalScalarLocals` uses. -/
def CoreMemDesign.widthsOf (E : CoreMemDesign) (elems : List (String × Nat)) : List (String × Nat) :=
  if elems.isEmpty then E.elems else elems

/-- `evalScalarLocals` without locals, on a view. -/
def CoreMemDesign.evalScalarV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (v : SvState)
    (ctx : Option Nat) (e : PExpr) : Res LVec :=
  evalPure2 v (instExpr2 env (E.widthsOf elems) ctx e)

mutual

/-- `evalIndexLocals` on a view. -/
def CoreMemDesign.evalIdxV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (v : SvState)
    (e : PExpr) : Res LVec :=
  match evalInt env e with
  | .ok i => .ok (LVec.ofInt 32 i)
  | .error _ => E.evalV env elems v none e

/-- `evalExprLocals` on a view, for a design without memories: the same arms, every memory lookup absent. -/
def CoreMemDesign.evalV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (v : SvState)
    (ctx : Option Nat) : PExpr → Res LVec
  | e@(.bitSel base index) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let bv ← E.evalV env elems v none base
        let iv ← E.evalIdxV env elems v index
        let position? := if index.signedCast then iv.toInt? else iv.toNat?.map Int.ofNat
        match position? with
        | some position =>
            if 0 ≤ position && position < bv.width then .ok (bv.extract position.toNat 1)
            else .ok (LVec.xVec 1)
        | none => .ok (LVec.xVec 1)
      else E.evalScalarV env elems v ctx e
  | .functionCall _ _ => .unsupported "evalV: a function call is outside the clocked profile"
  | e@(.unary op a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        evalMemUnary op (← E.evalV env elems v ctx a)
      else E.evalScalarV env elems v ctx e
  | e@(.binary op a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        evalMemBin op (← E.evalV env elems v ctx a) (← E.evalV env elems v ctx b)
      else E.evalScalarV env elems v ctx e
  | e@(.ternary c a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let cv ← E.evalV env elems v none c
        let tv ← E.evalV env elems v ctx a
        let fv ← E.evalV env elems v ctx b
        .ok (LVec.ternary cv tv fv)
      else E.evalScalarV env elems v ctx e
  | e@(.concat xs) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let vs ← E.evalListV env elems v xs
        .ok (LVec.concatMany vs.toArray)
      else E.evalScalarV env elems v ctx e
  | e@(.resize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let x ← E.evalV env elems v ctx a
        .ok (x.resizeU (ctx.getD x.width))
      else E.evalScalarV env elems v ctx e
  | e@(.signedResize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let x ← E.evalV env elems v ctx a
        .ok (x.resizeSigned (ctx.getD x.width))
      else E.evalScalarV env elems v ctx e
  | e@(.squash2 _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        return (← E.evalV env elems v ctx a).toTwoState
      else E.evalScalarV env elems v ctx e
  | e => E.evalScalarV env elems v ctx e

/-- `evalMemExprListLocals` on a view. -/
def CoreMemDesign.evalListV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (v : SvState) :
    List PExpr → Res (List LVec)
  | [] => .ok []
  | e :: es => do
      let x ← E.evalV env elems v none e
      let xs ← E.evalListV env elems v es
      .ok (x :: xs)

end

theorem CoreMemDesign.memDecl?_none {E : CoreMemDesign} (hm : E.memories.toList = []) (n : String) :
    E.memDecl? n = none := by
  simp [CoreMemDesign.memDecl?, hm]

mutual

theorem CoreMemDesign.evalIdx_eq {E : CoreMemDesign} (hm : E.memories.toList = []) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) :
    ∀ (e : PExpr), LeanModels.Sv.PExpr.hasFunctionCall e = false →
      E.evalIndexLocals env elems st [] e = E.evalIdxV env elems (E.scalar.view st.scalar) e
  | e, h => by
      unfold CoreMemDesign.evalIndexLocals CoreMemDesign.evalIdxV
      cases evalInt env e with
      | ok i => rfl
      | error m => exact CoreMemDesign.evalExprLocals_eq_evalV hm env elems st none e h

/-- **The route's evaluator is `evalV` on the view**, for a design without memories and a function-free expression. -/
theorem CoreMemDesign.evalExprLocals_eq_evalV {E : CoreMemDesign} (hm : E.memories.toList = []) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) :
    ∀ (ctx : Option Nat) (e : PExpr), LeanModels.Sv.PExpr.hasFunctionCall e = false →
      E.evalExprLocals env elems st ctx [] e = E.evalV env elems (E.scalar.view st.scalar) ctx e
  | ctx, .lit _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .ident _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .paramRef _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .genvarRef _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .enumRef _ _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .int _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .fill _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .unsupported _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .sysCall _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .partSel _ _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .repl _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .reduce _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .cast _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .functionCall _ _, h => by simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | ctx, .arrayElem name indices, _ => by
      cases indices with
      | nil => simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.memDecl?_none hm,
          CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
      | cons i is =>
          cases is with
          | nil => simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.memDecl?_none hm,
              CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
          | cons j js => simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.memDecl?_none hm,
              CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .arrayPart name indices mode a b, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.memDecl?_none hm,
        CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .bitSel base index, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hm env elems st none base h.1,
          CoreMemDesign.evalIdx_eq hm env elems st index h.2]
        rfl
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .unary op a, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hm env elems st ctx a h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .binary op a b, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hm env elems st ctx a h.1,
          CoreMemDesign.evalExprLocals_eq_evalV hm env elems st ctx b h.2]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .ternary c a b, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hm env elems st none c h.1.1,
          CoreMemDesign.evalExprLocals_eq_evalV hm env elems st ctx a h.1.2,
          CoreMemDesign.evalExprLocals_eq_evalV hm env elems st ctx b h.2]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .concat xs, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalList_eq hm env elems st xs h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .resize w a, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hm env elems st ctx a h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .signedResize w a, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hm env elems st ctx a h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .squash2 w a, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hm env elems st ctx a h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]

theorem CoreMemDesign.evalList_eq {E : CoreMemDesign} (hm : E.memories.toList = []) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) :
    ∀ (xs : List PExpr), LeanModels.Sv.PExpr.hasFunctionCallList xs = false →
      E.evalMemExprListLocals env elems st [] xs = E.evalListV env elems (E.scalar.view st.scalar) xs
  | [], _ => by simp [CoreMemDesign.evalMemExprListLocals, CoreMemDesign.evalListV]
  | x :: xs, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCallList, Bool.or_eq_false_iff] at h
      simp only [CoreMemDesign.evalMemExprListLocals, CoreMemDesign.evalListV,
        CoreMemDesign.evalExprLocals_eq_evalV hm env elems st none x h.1, CoreMemDesign.evalList_eq hm env elems st xs h.2]

end

#print axioms CoreMemDesign.evalExprLocals_eq_evalV

/-! ## NBA-only edge bodies -/

mutual

/-- An edge body of the clocked profile: nonblocking assignments to whole declared scalars under `if`/`else` and
`begin … end`, every expression function-free. (An unqualified `case` is the next slice; a qualified `case` refuses on
an x subject, the declared departure sv-div-5.) -/
def _root_.LeanModels.Sv.PStmt.nbaWholeB : PStmt → Bool
  | .nbaAssign _ e => !LeanModels.Sv.PExpr.hasFunctionCall e
  | .nbaAssignL t e =>
      match t with
      | .ident _ => !LeanModels.Sv.PExpr.hasFunctionCall e
      | _ => false
  | .ifStmt c y n => !LeanModels.Sv.PExpr.hasFunctionCall c && PStmt.nbaWholeB y && PStmt.optNbaWholeB n
  | .block body => PStmt.listNbaWholeB body
  | _ => false

/-- `nbaWholeB` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optNbaWholeB : Option PStmt → Bool
  | none => true
  | some s => PStmt.nbaWholeB s

/-- `nbaWholeB` of every statement of a list. -/
def _root_.LeanModels.Sv.PStmt.listNbaWholeB : List PStmt → Bool
  | [] => true
  | s :: ss => PStmt.nbaWholeB s && PStmt.listNbaWholeB ss

end

mutual

/-- The fuel the route's statement executor (`execStmtFuel`) needs for a body: one per nesting level and per list
element. -/
def _root_.LeanModels.Sv.PStmt.need : PStmt → Nat
  | .ifStmt _ y n => 1 + max (PStmt.need y) (PStmt.optNeed n)
  | .block body => 1 + PStmt.listNeed body
  | _ => 1

/-- `need` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optNeed : Option PStmt → Nat
  | none => 0
  | some s => PStmt.need s

/-- The fuel `execStmtsFuel` needs for a list. -/
def _root_.LeanModels.Sv.PStmt.listNeed : List PStmt → Nat
  | [] => 1
  | s :: ss => 1 + max (PStmt.need s) (PStmt.listNeed ss)

end

mutual

/-- **The nonblocking updates an NBA-only body issues on a view**, in issue order (`execStmtFuel` on the view). -/
def CoreMemDesign.nbaQ (E : CoreMemDesign) (v : SvState) : PStmt → Res NbaQueue2
  | .nbaAssign t e =>
      match E.scalarTarget t with
      | none => .unsupported s!"11.5.1: scalar NBA target '{t}' is undeclared"
      | some w => do
          let x ← E.evalV E.env E.elems v (some w) e
          .ok [(t, 0, x)]
  | .nbaAssignL lhs e =>
      match lhs with
      | .ident t =>
          match E.scalarTarget t with
          | none => .unsupported s!"11.5.1: scalar NBA target '{t}' is undeclared"
          | some w => do
              let x ← E.evalV E.env E.elems v (some w) e
              .ok [(t, 0, x)]
      | _ => .unsupported "nbaQ: a select or concatenated NBA target is outside the clocked profile"
  | .ifStmt c y n => do
      let cv ← E.evalV E.env E.elems v (some 1) c
      if cv.condTrue then E.nbaQ v y else E.nbaQOpt v n
  | .block body => E.nbaQList v body
  | _ => .unsupported "nbaQ: a statement outside the NBA-only profile"

/-- `nbaQ` of an optional statement (none issues nothing). -/
def CoreMemDesign.nbaQOpt (E : CoreMemDesign) (v : SvState) : Option PStmt → Res NbaQueue2
  | none => .ok []
  | some s => E.nbaQ v s

/-- `nbaQ` of a statement list, concatenated in order. -/
def CoreMemDesign.nbaQList (E : CoreMemDesign) (v : SvState) : List PStmt → Res NbaQueue2
  | [] => .ok []
  | s :: ss => do
      let a ← E.nbaQ v s
      let b ← E.nbaQList v ss
      .ok (a ++ b)

end

/-- The edge-body result whose state is `st` and whose scalar queue is `q`. -/
def CoreMemExec.ofQ (st : CoreMemState) : Res NbaQueue2 → CoreMemExec
  | .ok q => .ok { state := st, scalarQ := q, memoryQ := [] }
  | .timeout => .timeout
  | .unsupported m => .unsupported m

theorem CoreMemDesign.evalExpr_eq {E : CoreMemDesign} (hm : E.memories.toList = []) (st : CoreMemState)
    (ctx : Option Nat) (e : PExpr) (h : LeanModels.Sv.PExpr.hasFunctionCall e = false) :
    E.evalExpr E.env E.elems st ctx e = E.evalV E.env E.elems (E.scalar.view st.scalar) ctx e :=
  CoreMemDesign.evalExprLocals_eq_evalV hm E.env E.elems st ctx e h

mutual

/-- **An NBA-only body leaves the state alone and issues `nbaQ`**, at every fuel from its need on. -/
theorem CoreMemDesign.execStmtFuel_nba {E : CoreMemDesign} (hm : E.memories.toList = []) (st : CoreMemState) :
    ∀ (b : PStmt) (fuel : Nat), b.nbaWholeB = true → b.need ≤ fuel →
      E.execStmtFuel E.env E.elems st fuel b = CoreMemExec.ofQ st (E.nbaQ (E.scalar.view st.scalar) b)
  | .nbaAssign t e, fuel, hb, hf => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.nbaWholeB, Bool.not_eq_true'] at hb
      simp only [CoreMemDesign.execStmtFuel, CoreMemDesign.nbaQ]
      cases hw : E.scalarTarget t with
      | none => rfl
      | some w =>
          simp only [CoreMemDesign.evalExpr_eq hm st (some w) e hb]
          cases E.evalV E.env E.elems (E.scalar.view st.scalar) (some w) e with
          | ok x => simp [CoreMemDesign.issueTarget, hw, CoreMemExec.fromQueue, CoreMemExec.ofQ]
          | timeout => rfl
          | unsupported m => rfl
  | .nbaAssignL lhs e, fuel, hb, hf => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      cases lhs with
      | ident t =>
          simp only [PStmt.nbaWholeB, Bool.not_eq_true'] at hb
          simp only [CoreMemDesign.execStmtFuel, CoreMemDesign.nbaQ]
          cases hw : E.scalarTarget t with
          | none => rfl
          | some w =>
              simp only [CoreMemDesign.evalExpr_eq hm st (some w) e hb]
              cases E.evalV E.env E.elems (E.scalar.view st.scalar) (some w) e with
              | ok x => simp [CoreMemDesign.issueTarget, hw, CoreMemExec.fromQueue, CoreMemExec.ofQ]
              | timeout => rfl
              | unsupported m => rfl
      | _ => simp [PStmt.nbaWholeB] at hb
  | .ifStmt c y n, fuel, hb, hf => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.nbaWholeB, Bool.and_eq_true, Bool.not_eq_true'] at hb
      obtain ⟨⟨hc, hy⟩, hn⟩ := hb
      simp only [PStmt.need] at hf
      have hfy : y.need ≤ f := by omega
      have hfn : PStmt.optNeed n ≤ f := by omega
      simp only [CoreMemDesign.execStmtFuel, CoreMemDesign.nbaQ, CoreMemDesign.evalExpr_eq hm st (some 1) c hc]
      cases E.evalV E.env E.elems (E.scalar.view st.scalar) (some 1) c with
      | ok cv =>
          simp only [Res.ok_bind]
          by_cases hct : cv.condTrue = true
          · simp only [hct, ite_true]
            exact CoreMemDesign.execStmtFuel_nba hm st y f hy hfy
          · simp only [hct, Bool.false_eq_true, ite_false]
            cases n with
            | none => simp [CoreMemDesign.nbaQOpt, CoreMemExec.ofQ]
            | some s =>
                simp only [PStmt.optNbaWholeB] at hn
                simp only [PStmt.optNeed] at hfn
                simp only [CoreMemDesign.nbaQOpt]
                exact CoreMemDesign.execStmtFuel_nba hm st s f hn hfn
      | timeout => rfl
      | unsupported m => rfl
  | .block body, fuel, hb, hf => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.nbaWholeB] at hb
      simp only [PStmt.need] at hf
      simp only [CoreMemDesign.execStmtFuel, CoreMemDesign.nbaQ]
      exact CoreMemDesign.execStmtsFuel_nba hm st body f hb (by omega)
  | .blockingAssign _ _, _, hb, _ => by simp [PStmt.nbaWholeB] at hb
  | .blockingAssignL _ _, _, hb, _ => by simp [PStmt.nbaWholeB] at hb
  | .forLoop _ _ _ _ _, _, hb, _ => by simp [PStmt.nbaWholeB] at hb
  | .caseStmt _ _ _ _ _, _, hb, _ => by simp [PStmt.nbaWholeB] at hb
  | .unsupported _ _, _, hb, _ => by simp [PStmt.nbaWholeB] at hb

theorem CoreMemDesign.execStmtsFuel_nba {E : CoreMemDesign} (hm : E.memories.toList = []) (st : CoreMemState) :
    ∀ (bs : List PStmt) (fuel : Nat), PStmt.listNbaWholeB bs = true → PStmt.listNeed bs ≤ fuel →
      E.execStmtsFuel E.env E.elems st fuel bs = CoreMemExec.ofQ st (E.nbaQList (E.scalar.view st.scalar) bs)
  | [], fuel, _, hf => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.listNeed] at hf; omega⟩
      simp [CoreMemDesign.execStmtsFuel, CoreMemDesign.nbaQList, CoreMemExec.ofQ]
  | s :: ss, fuel, hb, hf => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.listNeed] at hf; omega⟩
      simp only [PStmt.listNbaWholeB, Bool.and_eq_true] at hb
      simp only [PStmt.listNeed] at hf
      simp only [CoreMemDesign.execStmtsFuel, CoreMemDesign.nbaQList,
        CoreMemDesign.execStmtFuel_nba hm st s f hb.1 (by omega)]
      cases E.nbaQ (E.scalar.view st.scalar) s with
      | ok a =>
          simp only [CoreMemExec.ofQ, Res.ok_bind]
          rw [CoreMemDesign.execStmtsFuel_nba hm st ss f hb.2 (by omega)]
          cases E.nbaQList (E.scalar.view st.scalar) ss with
          | ok b => simp [CoreMemExec.ofQ, CoreMemExec.append]
          | timeout => rfl
          | unsupported m => rfl
      | timeout => rfl
      | unsupported m => rfl

end

#print axioms CoreMemDesign.execStmtFuel_nba

/-! ## The clocked profile and coherent states -/

/-- A process of the clocked profile, at index `i` of the design: a continuous assign to a whole declared scalar whose
compiled expression is present (memory- and function-free source), or an edge process on `clk` without a reset whose
body is NBA-only and within the route's statement fuel. -/
def CoreMemDesign.ProcOk (E : CoreMemDesign) (clk : String) (i : Nat) : CoreMemProc → Prop
  | .assign (.ident n) v => LeanModels.Sv.PExpr.hasMemoryRead v = false ∧
      LeanModels.Sv.PExpr.hasFunctionCall v = false ∧ (∃ c, E.compiledAssigns[i]? = some (some c)) ∧
      (E.scalarWidth? n).isSome = true
  | .edge f => f.clock = clk ∧ f.reset = none ∧ f.body.nbaWholeB = true ∧ f.body.need ≤ 4096
  | _ => False

/-- **The clocked profile** (slice 1) of a canonical-E design: no memory, the scalar edge view's declarations are the
scalar view's, distinct names, every declaration 4-state, every process `ProcOk`. -/
structure CoreMemDesign.SeqProfile (E : CoreMemDesign) (clk : String) : Prop where
  noMem : E.memories.toList = []
  base : E.scalarEdge.base = E.scalar
  names : (E.scalar.decls.toList.map Decl.name).Nodup
  four : AllFour E.scalar
  procs : ∀ (i : Nat) (p : CoreMemProc), E.processes[i]? = some p → E.ProcOk clk i p

/-- A coherent state: the store is its cache's, the cache has one value per declaration, every value of its
declaration's type. -/
structure CoreMemDesign.Coherent (E : CoreMemDesign) (st : CoreMemState) : Prop where
  store : st.scalar = E.scalarStore st.scalarCache
  size : st.scalarCache.size = E.scalar.decls.size
  typed : E.scalar.Typed st.scalar

theorem viewAux_congr_lt {s s' : Store} : ∀ (ds : List Decl) (i : Nat),
    (∀ j, i ≤ j → j < i + ds.length → s { decl := j } = s' { decl := j }) → viewAux s ds i = viewAux s' ds i
  | [], _, _ => rfl
  | dc :: ds, i, h => by
      simp only [viewAux, h i (Nat.le_refl _) (by simp),
        viewAux_congr_lt ds (i + 1) fun j hj hj' => h j (by omega) (by simp at hj' ⊢; omega)]

/-- Two stores that agree on the declared variables have one view. -/
theorem Elab.view_congr_decls {E : Elab} {s s' : Store}
    (h : ∀ j, j < E.decls.size → s { decl := j } = s' { decl := j }) : E.view s = E.view s' :=
  viewAux_congr_lt _ 0 fun j _ hj => h j (by simpa using hj)

theorem Elab.declOf_some {E : Elab} {x : VarId} {dc : Decl} (h : E.declOf x = some dc) :
    x = { decl := x.decl } ∧ x.decl < E.decls.size := by
  unfold Elab.declOf at h
  split at h
  · rename_i hp
    refine ⟨by cases x; simp_all, ?_⟩
    exact (Array.getElem?_eq_some_iff.mp h).1
  · cases h

/-- Two stores that agree on the declared variables are typed together. -/
theorem Elab.typed_congr_decls {E : Elab} {s s' : Store}
    (h : ∀ j, j < E.decls.size → s { decl := j } = s' { decl := j }) (hT : E.Typed s) : E.Typed s' := by
  intro x dc hx
  obtain ⟨hxe, hlt⟩ := Elab.declOf_some hx
  rw [hxe, ← h x.decl hlt, ← hxe]
  exact hT x dc hx

theorem CoreMemDesign.scalarStore_cacheOf (E : CoreMemDesign) (s : Store) :
    ∀ j, j < E.scalar.decls.size → E.scalarStore (E.scalarCacheOf s) { decl := j } = s { decl := j } := by
  intro j hj
  simp [CoreMemDesign.scalarStore, CoreMemDesign.scalarCacheOf, hj]

/-- `normalizeScalar` keeps the view of the store it is given, and is coherent when that store is typed. -/
theorem CoreMemDesign.normalizeScalar_view (E : CoreMemDesign) (st : CoreMemState) (s : Store) :
    E.scalar.view (E.normalizeScalar st s).scalar = E.scalar.view s :=
  Elab.view_congr_decls (E.scalarStore_cacheOf s)

theorem CoreMemDesign.normalizeScalar_coherent (E : CoreMemDesign) (st : CoreMemState) {s : Store}
    (hT : E.scalar.Typed s) : E.Coherent (E.normalizeScalar st s) :=
  { store := rfl
    size := by simp [CoreMemDesign.normalizeScalar, CoreMemDesign.scalarCacheOf]
    typed := Elab.typed_congr_decls (fun j hj => (E.scalarStore_cacheOf s j hj).symm) hT }

/-- `setScalarState` on a coherent state: `SvState.set` on the view, converted to the declaration's type. -/
theorem CoreMemDesign.setScalarState_spec {E : CoreMemDesign} {st : CoreMemState} (hc : E.Coherent st)
    {n : String} {x : VarId} (hx : E.scalar.resolve n = some x) (v : LVec) :
    E.scalar.view (E.setScalarState st n v).scalar =
        SvState.set (E.scalar.view st.scalar) n (Val.ofLVec (st.scalar x).ty v).bits ∧
      E.Coherent (E.setScalarState st n v) := by
  obtain ⟨dc, hdc, -, -, -⟩ := Elab.resolve_some hx
  obtain ⟨hxe, hlt⟩ := Elab.declOf_some hdc
  have hagree : ∀ j, j < E.scalar.decls.size →
      E.scalarStore (st.scalarCache.set! x.decl (Val.ofLVec (st.scalar x).ty v)) { decl := j } =
        (st.scalar.set x (Val.ofLVec (st.scalar x).ty v)) { decl := j } := by
    intro j hj
    have hjc : j < st.scalarCache.size := by rw [hc.size]; exact hj
    by_cases hjx : j = x.decl
    · subst hjx
      rw [hxe]
      simp [CoreMemDesign.scalarStore, Store.set, Array.set!, hjc]
    · have hne : ({ decl := j } : VarId) ≠ x := by
        intro h'; rw [← h'] at hjx; exact hjx rfl
      simp only [CoreMemDesign.scalarStore, Store.set, hne, ↓reduceIte, Array.set!]
      rw [hc.store]
      simp [CoreMemDesign.scalarStore, Array.getElem?_setIfInBounds_ne (Ne.symm hjx)]
  simp only [CoreMemDesign.setScalarState, hx]
  refine ⟨?_, ?_⟩
  · rw [Elab.view_congr_decls hagree, Elab.view_set _ _ hx]
  · exact { store := rfl
            size := by simp [hc.size]
            typed := Elab.typed_congr_decls (fun j hj => (hagree j hj).symm) (hc.typed.set rfl) }

#print axioms CoreMemDesign.setScalarState_spec

/-! ## The continuous-assign settle on views -/

/-- The value `storeFromView` gives a declaration the view lacks. -/
def declFallback (dc : Decl) : LVec := if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width

/-- The view `storeFromView` materializes: each declaration's value from `raw`, converted to its type. -/
def CoreMemDesign.matV (E : CoreMemDesign) (raw : SvState) : SvState :=
  E.scalar.decls.toList.map fun dc =>
    (dc.name, (Val.ofLVec (VType.ofDecl dc) ((SvState.lookup raw dc.name).getD (declFallback dc))).bits)

/-- One source-order pass of the continuous assigns on a RAW view (each target set to its compiled expression's value,
unconverted, as `settleAssignAt` threads it); edge processes are skipped. -/
def CoreMemDesign.settleRaw (E : CoreMemDesign) (raw : SvState) (idx : Nat) : List CoreMemProc → Res SvState
  | [] => .ok raw
  | .assign (.ident n) _ :: rest =>
      match E.compiledAssigns[idx]? with
      | some (some c) => do
          let x ← evalPure2 raw c
          E.settleRaw (SvState.set raw n x) (idx + 1) rest
      | _ => .unsupported "settleRaw: a continuous assign without its compiled expression"
  | .edge _ :: rest => E.settleRaw raw (idx + 1) rest
  | _ :: _ => .unsupported "settleRaw: a process outside the clocked profile"

/-- **One `settleAssign` on a view**: the pass on the raw view, then the materialization. -/
def CoreMemDesign.settleV (E : CoreMemDesign) (v : SvState) : Res SvState := do
  let raw ← E.settleRaw v 0 E.processes.toList
  .ok (E.matV raw)

private theorem lookup_set' (st : SvState) (n : String) (v : LVec) (m : String) :
    SvState.lookup (SvState.set st n v) m = if n = m then some v else SvState.lookup st m := by
  induction st with
  | nil => simp [SvState.set, SvState.lookup]
  | cons kv rest ih =>
      obtain ⟨k, w⟩ := kv
      by_cases hk : k = n
      · subst hk
        by_cases hkm : k = m <;> simp [SvState.set, SvState.lookup, hkm]
      · have hk' : (k == n) = false := by simpa using hk
        simp only [SvState.set, hk', Bool.false_eq_true, ↓reduceIte, SvState.lookup, ih]
        by_cases hkm : k = m
        · subst hkm; simp [Ne.symm hk]
        · have hkm' : (k == m) = false := by simpa using hkm
          simp [hkm']

private theorem set_map_of_mem {f : Decl → LVec} {n : String} {v : LVec} :
    ∀ (l : List Decl), (l.map Decl.name).Nodup → n ∈ l.map Decl.name →
      SvState.set (l.map fun d => (d.name, f d)) n v =
        l.map fun d => (d.name, if d.name = n then v else f d)
  | [], _, h => by simp at h
  | d :: l, hnd, hmem => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      by_cases hd : d.name = n
      · have hrest : ∀ d' ∈ l, d'.name ≠ n := fun d' hd' h => hnd.1 d' hd' (h.trans hd.symm)
        simp only [SvState.set, hd, beq_self_eq_true, ↓reduceIte, List.map_cons, List.cons.injEq, true_and]
        exact (List.map_congr_left fun d' hd' => by simp [hrest d' hd']).symm
      · have hd' : (d.name == n) = false := by simpa using hd
        have hmem' : n ∈ l.map Decl.name := by
          simp only [List.map_cons, List.mem_cons] at hmem
          rcases hmem with h | h
          · exact absurd h.symm hd
          · exact h
        simp only [SvState.set, hd', Bool.false_eq_true, ↓reduceIte, List.map_cons, hd]
        exact congrArg _ (set_map_of_mem l hnd.2 hmem')

private theorem resolveAux_of_nodup {dc : Decl} : ∀ (ds : List Decl) (i k : Nat), (ds.map Decl.name).Nodup →
    ds[k]? = some dc → resolveAux dc.name ds i = some { decl := i + k }
  | [], _, _, _, h => by simp at h
  | d :: ds, i, k, hnd, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp only [resolveAux, beq_self_eq_true, ↓reduceIte, Nat.add_zero]
      | succ k =>
          simp only [List.getElem?_cons_succ] at h
          have hne : (d.name == dc.name) = false := by
            have := hnd.1 dc (List.mem_of_getElem? h)
            exact beq_eq_false_iff_ne.mpr (fun h' => this h'.symm)
          simp only [resolveAux, hne, Bool.false_eq_true, ↓reduceIte]
          rw [resolveAux_of_nodup ds (i + 1) k hnd.2 h]
          congr 2
          omega

theorem Val.ext_bits {a b : Val} (hty : a.ty = b.ty) (hb : a.bits = b.bits) : a = b := by
  cases a; cases b; simp_all

/-- The view of `storeFromView raw` is the materialization of `raw`. -/
theorem CoreMemDesign.view_storeFromView (E : CoreMemDesign) (raw : SvState) :
    E.scalar.view (E.storeFromView raw) = E.matV raw := by
  unfold CoreMemDesign.matV Elab.view
  suffices h : ∀ (ds : List Decl) (i : Nat), (∀ k (hk : k < ds.length), E.scalar.decls[i + k]? = some ds[k]) →
      viewAux (E.storeFromView raw) ds i = ds.map (fun dc => (dc.name, (Val.ofLVec (VType.ofDecl dc)
        ((SvState.lookup raw dc.name).getD (declFallback dc))).bits)) by
    exact h _ 0 fun k hk => by simp
  intro ds
  induction ds with
  | nil => intro _ _; rfl
  | cons d ds ih =>
      intro i hi
      have h0 := hi 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      simp only [List.map_cons, viewAux]
      congr 1
      · simp only [CoreMemDesign.storeFromView, Elab.declOf, h0, declFallback]
      · exact ih (i + 1) fun k hk => by
          have := hi (k + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- The materialization of a coherent state's own view is that view. -/
theorem CoreMemDesign.matV_view {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {s : Store} (hT : E.scalar.Typed s) : E.matV (E.scalar.view s) = E.scalar.view s := by
  have hpt : ∀ j, j < E.scalar.decls.size → E.storeFromView (E.scalar.view s) { decl := j } = s { decl := j } := by
    intro j hj
    have hd : E.scalar.decls.toList[j]? = some E.scalar.decls[j] := by simp [hj]
    have hres : E.scalar.resolve E.scalar.decls[j].name = some { decl := j } := by
      simpa [Elab.resolve] using resolveAux_of_nodup E.scalar.decls.toList 0 j hnd hd
    have hdecl : E.scalar.declOf { decl := j } = some E.scalar.decls[j] := by
      simp [Elab.declOf, hj]
    have hty := hT { decl := j } E.scalar.decls[j] hdecl
    have hw : (s { decl := j }).bits.width = E.scalar.decls[j].width := by
      rw [(s { decl := j }).width_eq, hty]; rfl
    have h4j : E.scalar.decls[j].twoState = false := h4 _ (by simp)
    simp only [CoreMemDesign.storeFromView, hdecl, Elab.lookup_view, hres, Option.map_some, Option.getD_some]
    refine Val.ext_bits (by rw [hty]; rfl) ?_
    simp [Val.ofLVec, VType.conv, VType.ofDecl, h4j, LVec.resizeU_of_width hw]
  rw [← E.view_storeFromView]
  exact Elab.view_congr_decls hpt

#print axioms CoreMemDesign.matV_view

theorem CoreMemDesign.typed_storeFromView (E : CoreMemDesign) (raw : SvState) : E.scalar.Typed (E.storeFromView raw) := by
  intro x dc hx
  simp only [CoreMemDesign.storeFromView, hx]
  rfl

theorem CoreMemDesign.scalarWidth?_some {E : CoreMemDesign} {n : String} (h : (E.scalarWidth? n).isSome = true) :
    ∃ x, E.scalar.resolve n = some x := by
  unfold CoreMemDesign.scalarWidth? at h
  split at h
  · rename_i x hx; exact ⟨x, hx⟩
  · simp at h

private theorem eq_of_mem_of_name : ∀ {l : List Decl}, (l.map Decl.name).Nodup → ∀ {a b : Decl},
    a ∈ l → b ∈ l → a.name = b.name → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | d :: l, hnd, a, b, ha, hb, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · exact absurd h.symm (hnd.1 b hb)
      · exact absurd h (hnd.1 a ha)
      · exact eq_of_mem_of_name hnd.2 ha hb h

/-- The materialization after one more assign: `SvState.set` of the converted value. -/
theorem CoreMemDesign.matV_set {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    {n : String} {x : VarId} {dc : Decl} (hx : E.scalar.resolve n = some x) (hdc : E.scalar.declOf x = some dc)
    (raw : SvState) (val : LVec) :
    E.matV (SvState.set raw n val) = SvState.set (E.matV raw) n (Val.ofLVec (VType.ofDecl dc) val).bits := by
  obtain ⟨dc', hdc', hname, hmem, -⟩ := Elab.resolve_some hx
  rw [hdc] at hdc'
  cases hdc'
  subst hname
  unfold CoreMemDesign.matV
  rw [set_map_of_mem _ hnd (List.mem_map_of_mem (f := Decl.name) hmem)]
  refine List.map_congr_left fun d hd => ?_
  by_cases hdn : d.name = dc.name
  · have hdd : d = dc := eq_of_mem_of_name hnd hd hmem hdn
    subst hdd
    simp
  · have hne : ¬ dc.name = d.name := fun h => hdn h.symm
    simp [lookup_set', hdn, hne]

/-- **`settleAssignAt` on the clocked profile is `settleRaw`**, keeping coherence and the materialized view. -/
theorem CoreMemDesign.settleAssignAt_seq {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) :
    ∀ (procs : List CoreMemProc) (idx : Nat), (∀ k p, procs[k]? = some p → E.processes[idx + k]? = some p) →
    ∀ (st : CoreMemState) (raw raw' : SvState), E.Coherent st → E.scalar.view st.scalar = E.matV raw →
      E.settleRaw raw idx procs = .ok raw' →
      ∃ st', E.settleAssignAt E.env E.elems st raw idx procs = .ok (st', raw') ∧ E.Coherent st' ∧
        E.scalar.view st'.scalar = E.matV raw'
  | [], idx, _, st, raw, raw', hc, hv, hs => by
      simp only [CoreMemDesign.settleRaw, Res.ok.injEq] at hs
      subst hs
      exact ⟨st, rfl, hc, hv⟩
  | p :: rest, idx, hidx, st, raw, raw', hc, hv, hs => by
      have hp : E.processes[idx]? = some p := by simpa using hidx 0 p rfl
      have hrest : ∀ k q, rest[k]? = some q → E.processes[idx + 1 + k]? = some q := by
        intro k q hq
        have := hidx (k + 1) q (by simpa using hq)
        rwa [show idx + (k + 1) = idx + 1 + k by omega] at this
      have hok := hP.procs idx p hp
      cases p with
      | assign target value =>
          cases target with
          | ident n =>
              obtain ⟨hmr, hfc, ⟨c, hcomp⟩, hw⟩ := hok
              obtain ⟨xid, hxid⟩ := CoreMemDesign.scalarWidth?_some hw
              obtain ⟨dc, hdc, hname, -, -⟩ := Elab.resolve_some hxid
              have hsw : E.scalarWidth? n = some dc.width := by
                simp [CoreMemDesign.scalarWidth?, hxid, hdc]
              simp only [CoreMemDesign.settleRaw, hcomp, Res.bind_eq_ok] at hs
              obtain ⟨x, hx, hs⟩ := hs
              have hset := CoreMemDesign.setScalarState_spec hc hxid x
              have hty : (st.scalar xid).ty = VType.ofDecl dc := hc.typed xid dc hdc
              have hv' : E.scalar.view (E.setScalarState st n x).scalar = E.matV (SvState.set raw n x) := by
                rw [hset.1, hv, CoreMemDesign.matV_set hP.names hxid hdc, hty]
              obtain ⟨st', hrun, hc', hv''⟩ :=
                CoreMemDesign.settleAssignAt_seq hP rest (idx + 1) hrest _ _ _ hset.2 hv' hs
              refine ⟨st', ?_, hc', hv''⟩
              simp only [CoreMemDesign.settleAssignAt, hsw, Res.ok_bind, CoreMemDesign.evalScalarAssignAtView,
                hmr, hfc, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hcomp, hx]
              exact hrun
          | _ => exact absurd hok (by simp [CoreMemDesign.ProcOk])
      | edge f =>
          simp only [CoreMemDesign.settleRaw] at hs
          obtain ⟨st', hrun, hc', hv'⟩ := CoreMemDesign.settleAssignAt_seq hP rest (idx + 1) hrest st raw raw' hc hv hs
          exact ⟨st', by simpa [CoreMemDesign.settleAssignAt] using hrun, hc', hv'⟩
      | initial _ => exact absurd hok (by simp [CoreMemDesign.ProcOk])
      | comb _ => exact absurd hok (by simp [CoreMemDesign.ProcOk])
      | implicit _ => exact absurd hok (by simp [CoreMemDesign.ProcOk])
      | unsupported _ _ => exact absurd hok (by simp [CoreMemDesign.ProcOk])

/-- `compactScalar` after a settle pass: the materialized view, coherent. -/
theorem CoreMemDesign.compactScalar_spec {E : CoreMemDesign} {st : CoreMemState} (hc : E.Coherent st)
    {raw : SvState} (hv : E.scalar.view st.scalar = E.matV raw) :
    E.scalar.view (E.compactScalar st raw).scalar = E.matV raw ∧ E.Coherent (E.compactScalar st raw) := by
  unfold CoreMemDesign.compactScalar
  split
  · exact ⟨hv, hc⟩
  · refine ⟨?_, E.normalizeScalar_coherent st (E.typed_storeFromView raw)⟩
    show E.scalar.view (E.normalizeScalar st (E.storeFromView raw)).scalar = _
    rw [E.normalizeScalar_view, E.view_storeFromView]

/-- **One `settleAssign` of the route is `settleV` on the view**, on the clocked profile, from a coherent state. -/
theorem CoreMemDesign.settleAssign_seq {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    {st : CoreMemState} (hc : E.Coherent st) {v' : SvState} (hv : E.settleV (E.scalar.view st.scalar) = .ok v') :
    ∃ st', E.settleAssign E.env E.elems st E.processes.toList = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.Coherent st' := by
  simp only [CoreMemDesign.settleV, Res.bind_eq_ok, Res.ok.injEq] at hv
  obtain ⟨raw', hs, rfl⟩ := hv
  obtain ⟨st', hrun, hc', hv'⟩ := CoreMemDesign.settleAssignAt_seq hP E.processes.toList 0
    (fun k p hk => by simpa using hk) st _ raw' hc (CoreMemDesign.matV_view hP.names hP.four hc.typed).symm hs
  obtain ⟨hvc, hcc⟩ := CoreMemDesign.compactScalar_spec hc' hv'
  exact ⟨_, by simp [CoreMemDesign.settleAssign, hrun], hvc, hcc⟩

#print axioms CoreMemDesign.settleAssign_seq

/-! ## The edge pass and the slot -/

/-- Every edge process's nonblocking updates on a view, in process order. -/
def CoreMemDesign.edgeQV (E : CoreMemDesign) (v : SvState) : List CoreMemProc → Res NbaQueue2
  | [] => .ok []
  | .edge p :: rest => do
      let a ← E.nbaQ v p.body
      let b ← E.edgeQV v rest
      .ok (a ++ b)
  | _ :: rest => E.edgeQV v rest

/-- The shape of a process of the clocked profile, without its index. -/
def CoreMemDesign.ProcShape (clk : String) : CoreMemProc → Prop
  | .assign _ _ => True
  | .edge f => f.clock = clk ∧ f.reset = none ∧ f.body.nbaWholeB = true ∧ f.body.need ≤ 4096
  | _ => False

theorem CoreMemDesign.ProcOk.shape {E : CoreMemDesign} {clk : String} {i : Nat} {p : CoreMemProc}
    (h : E.ProcOk clk i p) : CoreMemDesign.ProcShape clk p := by
  cases p with
  | assign t v => trivial
  | edge f => exact h
  | initial _ => exact absurd h (by simp [CoreMemDesign.ProcOk])
  | comb _ => exact absurd h (by simp [CoreMemDesign.ProcOk])
  | implicit _ => exact absurd h (by simp [CoreMemDesign.ProcOk])
  | unsupported _ _ => exact absurd h (by simp [CoreMemDesign.ProcOk])

theorem CoreMemDesign.SeqProfile.shapes {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) :
    ∀ p ∈ E.processes.toList, CoreMemDesign.ProcShape clk p := by
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  rw [Array.getElem?_toList] at hi
  exact (hP.procs i p hi).shape

theorem CoreMemDesign.SeqProfile.hasComb {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) :
    E.hasComb = false := by
  simp only [CoreMemDesign.hasComb, List.any_eq_false]
  intro p hp
  have := hP.shapes p hp
  cases p <;> simp_all [CoreMemDesign.ProcShape]

theorem CoreMemDesign.SeqProfile.hasImplicit {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) :
    E.hasImplicit = false := by
  simp only [CoreMemDesign.hasImplicit, List.any_eq_false]
  intro p hp
  have := hP.shapes p hp
  cases p <;> simp_all [CoreMemDesign.ProcShape]

/-- **The edge pass of the clocked profile**: if the clock rose every edge process issues its `nbaQ` on the state's
view and leaves the state alone; otherwise nothing runs. -/
theorem CoreMemDesign.runEdges_seq {E : CoreMemDesign} (hm : E.memories.toList = []) (clk : String)
    (st : CoreMemState) (before after : SvState) :
    ∀ (procs : List CoreMemProc), (∀ p ∈ procs, CoreMemDesign.ProcShape clk p) →
      E.runEdges E.env E.elems st before after procs =
        if isPosedge (before.bit0 clk) (after.bit0 clk) then
          CoreMemExec.ofQ st (E.edgeQV (E.scalar.view st.scalar) procs)
        else .ok { state := st, scalarQ := [], memoryQ := [] }
  | [], _ => by split <;> simp [CoreMemDesign.runEdges, CoreMemDesign.edgeQV, CoreMemExec.ofQ]
  | p :: rest, h => by
      have ih := CoreMemDesign.runEdges_seq hm clk st before after rest (fun q hq => h q (by simp [hq]))
      have hp := h p (by simp)
      cases p with
      | edge f =>
          obtain ⟨hclk, hrst, hb, hn⟩ := hp
          simp only [CoreMemDesign.runEdges, CoreMemEdge.fires, hclk, hrst, Bool.or_false, CoreMemDesign.edgeQV]
          by_cases hf : isPosedge (before.bit0 clk) (after.bit0 clk) = true
          · simp only [hf, ↓reduceIte] at ih ⊢
            simp only [CoreMemDesign.execStmt, CoreMemDesign.execStmtFuel_nba hm st f.body 4096 hb hn]
            cases E.nbaQ (E.scalar.view st.scalar) f.body with
            | ok a =>
                simp only [CoreMemExec.ofQ, Res.ok_bind, ih]
                cases E.edgeQV (E.scalar.view st.scalar) rest with
                | ok b => simp [CoreMemExec.append]
                | timeout => rfl
                | unsupported m => rfl
            | timeout => rfl
            | unsupported m => rfl
          · simp only [hf, Bool.false_eq_true, ↓reduceIte] at ih ⊢
            exact ih
      | assign t v =>
          simp only [CoreMemDesign.runEdges, CoreMemDesign.edgeQV]
          exact ih
      | initial _ => exact absurd hp (by simp [CoreMemDesign.ProcShape])
      | comb _ => exact absurd hp (by simp [CoreMemDesign.ProcShape])
      | implicit _ => exact absurd hp (by simp [CoreMemDesign.ProcShape])
      | unsupported _ _ => exact absurd hp (by simp [CoreMemDesign.ProcShape])

/-- The edge updates of a slot from the view `v` before it to the pre-edge view `p`: every edge process's if `clk`
rose, none otherwise. -/
def CoreMemDesign.edgeQIf (E : CoreMemDesign) (clk : String) (v p : SvState) : Res NbaQueue2 :=
  if isPosedge (v.bit0 clk) (p.bit0 clk) then E.edgeQV p E.processes.toList else .ok []

/-- **One slot of the route, on views**: the inputs applied, two settle passes (the pre-edge state), the edge
processes' updates if `clk` rose (each body on the pre-edge view), their commit, two settle passes. -/
def CoreMemDesign.slotV (E : CoreMemDesign) (clk : String) (v entry : SvState) : Res SvState := do
  let p0 ← E.settleV (applyInputs2 E.scalar.toDesign2 entry v)
  let p ← E.settleV p0
  let q ← E.edgeQIf clk v p
  let s1 ← E.settleV (commitNba2 p q)
  E.settleV s1

/-- **THE SLOT REFINEMENT**: for a design of the clocked profile, from every coherent state and every typed stimulus
entry, when the view-level slot succeeds the route's `step` succeeds, lands on exactly that view, and stays coherent. -/
theorem CoreMemDesign.step_seq {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) {st : CoreMemState}
    (hc : E.Coherent st) {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry) {v' : SvState}
    (hv : E.slotV clk (E.scalar.view st.scalar) entry = .ok v') :
    ∃ st', E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧ E.Coherent st' := by
  simp only [CoreMemDesign.slotV, Res.bind_eq_ok] at hv
  obtain ⟨p0, h0, p, h1, q, hq, s1, h2, h3⟩ := hv
  -- the inputs
  have hTin : E.scalar.Typed (E.scalar.applyInputs st.scalar entry) := hc.typed.applyInputs entry
  have hvin : E.scalar.view (E.scalar.applyInputs st.scalar entry) =
      applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar) :=
    Elab.view_applyInputs hP.names hP.four hc.typed hty
  have hci := E.normalizeScalar_coherent { st with memory := E.applyMemoryInputs entry st.memory } hTin
  have hvi : E.scalar.view (E.normalizeScalar { st with memory := E.applyMemoryInputs entry st.memory }
      (E.scalar.applyInputs st.scalar entry)).scalar = applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar) := by
    rw [E.normalizeScalar_view, hvin]
  -- the two pre-edge settle passes
  obtain ⟨st0, hs0, hv0, hc0⟩ := CoreMemDesign.settleAssign_seq hP hci (by rw [hvi]; exact h0)
  obtain ⟨st1, hs1, hv1, hc1⟩ := CoreMemDesign.settleAssign_seq hP hc0 (by rw [hv0]; exact h1)
  -- the edge pass
  have hedge : E.runEdges E.env E.elems st1 (E.scalar.view st.scalar) (E.scalar.view st1.scalar)
      E.processes.toList = .ok { state := st1, scalarQ := q, memoryQ := [] } := by
    rw [CoreMemDesign.runEdges_seq hP.noMem clk st1 _ _ _ hP.shapes, hv1]
    unfold CoreMemDesign.edgeQIf at hq
    by_cases hf : isPosedge ((E.scalar.view st.scalar).bit0 clk) (p.bit0 clk) = true
    · simp only [hf, ↓reduceIte] at hq ⊢
      rw [hq]
      rfl
    · simp only [hf, Bool.false_eq_true, ↓reduceIte, Res.ok.injEq] at hq ⊢
      rw [hq]
  -- the commit
  have hT1 : E.scalarEdge.base.Typed st1.scalar := by rw [hP.base]; exact hc1.typed
  have hTc : E.scalar.Typed (E.scalarEdge.commit st1.scalar q) := by
    have := Elab1.typed_commit (E := E.scalarEdge) q hT1
    rwa [hP.base] at this
  have hvc : E.scalar.view (E.scalarEdge.commit st1.scalar q) = commitNba2 p q := by
    have := Elab1.view_commit (E := E.scalarEdge) (by rw [hP.base]; exact hP.four) q hT1
    rw [hP.base] at this
    rw [this, hv1]
  have hcc := E.normalizeScalar_coherent st1 hTc
  have hvcc : E.scalar.view (E.normalizeScalar st1 (E.scalarEdge.commit st1.scalar q)).scalar = commitNba2 p q := by
    rw [E.normalizeScalar_view, hvc]
  -- the two post-edge settle passes
  obtain ⟨st2, hs2, hv2, hc2⟩ := CoreMemDesign.settleAssign_seq hP
    (st := { E.normalizeScalar st1 (E.scalarEdge.commit st1.scalar q) with memory := st1.memory })
    hcc (by rw [show E.scalar.view ({ E.normalizeScalar st1 (E.scalarEdge.commit st1.scalar q) with
      memory := st1.memory } : CoreMemState).scalar = commitNba2 p q from hvcc]; exact h2)
  obtain ⟨st3, hs3, hv3, hc3⟩ := CoreMemDesign.settleAssign_seq hP hc2 (by rw [hv2]; exact h3)
  refine ⟨st3, ?_, hv3, hc3⟩
  simp only [CoreMemDesign.step, hs0, Res.ok_bind, hP.hasComb, Bool.false_eq_true, ↓reduceIte, hs1, hedge,
    MemState.commitNba_nil, hs2, hP.hasImplicit, hs3]

#print axioms CoreMemDesign.step_seq

/-! ## The cycle -/

/-- **One clock cycle on views**: the low slot (`clk` = 0 and the data), then the high slot (`clk` raised); the pre
sample and the post sample. -/
def CoreMemDesign.cycleV (E : CoreMemDesign) (clk : String) (v data : SvState) : Res (SvState × SvState) := do
  let pre ← E.slotV clk v (lowEntry clk data)
  let post ← E.slotV clk pre (highEntry clk)
  .ok (pre, post)

/-- **THE CYCLE REFINEMENT (the cycle model derived from E)**: for a design of the clocked profile, from every coherent
state, for every typed data entry, when the view-level cycle gives `(pre, post)` the route's two slots succeed, land on
exactly `pre` and `post`, and stay coherent. -/
theorem CoreMemDesign.cycle_of_seqProfile {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    {st : CoreMemState} (hc : E.Coherent st) {data : SvState}
    (hlow : EntryTyped E.scalar.toDesign2 (lowEntry clk data)) (hhigh : EntryTyped E.scalar.toDesign2 (highEntry clk))
    {pre post : SvState} (hv : E.cycleV clk (E.scalar.view st.scalar) data = .ok (pre, post)) :
    ∃ s1 s2, E.step st (lowEntry clk data) = .ok s1 ∧ E.step s1 (highEntry clk) = .ok s2 ∧
      E.scalar.view s1.scalar = pre ∧ E.scalar.view s2.scalar = post ∧ E.Coherent s1 ∧ E.Coherent s2 := by
  simp only [CoreMemDesign.cycleV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
  obtain ⟨pre', h1, post', h2, rfl, rfl⟩ := hv
  obtain ⟨s1, hs1, hv1, hc1⟩ := CoreMemDesign.step_seq hP hc hlow h1
  obtain ⟨s2, hs2, hv2, hc2⟩ := CoreMemDesign.step_seq hP hc1 hhigh (by rw [hv1]; exact h2)
  exact ⟨s1, s2, hs1, hs2, hv1, hv2, hc1, hc2⟩

#print axioms CoreMemDesign.cycle_of_seqProfile

/-! ## Runs: every run of the route, from every coherent state -/

/-- The x start of the route (`CoreMemDesign.initial`: every variable x, every net z) is coherent. -/
theorem CoreMemDesign.initial_coherent (E : CoreMemDesign) : E.Coherent E.initial :=
  { store := rfl
    size := by simp [CoreMemDesign.initial, CoreMemDesign.scalarCacheOf]
    typed := Elab.typed_congr_decls (fun j hj => (E.scalarStore_cacheOf _ j hj).symm) E.scalar.typed_initStore }

/-- A data entry of a cycle is typed: every input port it binds gets a value of its declared width. -/
def CoreMemDesign.DataTyped (E : CoreMemDesign) (clk : String) (d : SvState) : Prop :=
  EntryTyped E.scalar.toDesign2 (lowEntry clk d)

theorem CoreMemDesign.highEntry_typed {E : CoreMemDesign} {clk : String}
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) : EntryTyped E.scalar.toDesign2 (highEntry clk) := by
  intro n v _ hv
  simp only [highEntry] at hv
  unfold SvState.lookup at hv
  split at hv
  · rename_i h
    simp only [Option.some.injEq] at hv
    subst hv
    have : clk = n := by simpa using h
    subst this
    exact hclk
  · simp [SvState.lookup] at hv

theorem CoreMemDesign.DataTyped.of_entry {E : CoreMemDesign} {clk : String}
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) {d : SvState} (hd : EntryTyped E.scalar.toDesign2 d) :
    E.DataTyped clk d := by
  intro n v hn hv
  simp only [lowEntry, SvState.lookup] at hv
  split at hv
  · rename_i h
    simp only [Option.some.injEq] at hv
    subst hv
    have : clk = n := by simpa using h
    subst this
    exact hclk
  · exact hd n v hn hv

/-- The view-level run: each cycle's pre and post sample, the next cycle from the post sample. -/
def CoreMemDesign.runV (E : CoreMemDesign) (clk : String) : SvState → List SvState → Res (List (SvState × SvState))
  | _, [] => .ok []
  | v, d :: ds => do
      let pp ← E.cycleV clk v d
      let rest ← E.runV clk pp.2 ds
      .ok (pp :: rest)

/-- The pre and post samples of a run of cycles: the slot states two by two. -/
def cyclePairs {α : Type} : List α → List (α × α)
  | a :: b :: rest => (a, b) :: cyclePairs rest
  | _ => []

/-- **THE RUN REFINEMENT**: from every coherent state and every typed data list, when the view-level run succeeds the
route's own run of the cycles (`runCoreMemRows` on `cycleRows`) succeeds and its samples, two per cycle, are exactly
the view-level run's. -/
theorem CoreMemDesign.runRows_seq {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) :
    ∀ (ins : List SvState) (st : CoreMemState) (tr : List (SvState × SvState)), E.Coherent st →
      (∀ d ∈ ins, E.DataTyped clk d) → E.runV clk (E.scalar.view st.scalar) ins = .ok tr →
      ∃ rows, runCoreMemRows E st (cycleRows clk ins) = .ok rows ∧
        cyclePairs (rows.map fun s => E.scalar.view s.scalar) = tr
  | [], st, tr, _, _, hv => by
      simp only [CoreMemDesign.runV, Res.ok.injEq] at hv
      subst hv
      exact ⟨[], rfl, rfl⟩
  | d :: ds, st, tr, hc, hd, hv => by
      simp only [CoreMemDesign.runV, Res.bind_eq_ok, Res.ok.injEq] at hv
      obtain ⟨⟨pre, post⟩, hcyc, rest, hrest, rfl⟩ := hv
      obtain ⟨s1, s2, hs1, hs2, hv1, hv2, hc1, hc2⟩ :=
        CoreMemDesign.cycle_of_seqProfile hP hc (hd d (by simp)) (CoreMemDesign.highEntry_typed hclk) hcyc
      obtain ⟨rows, hrows, hpairs⟩ :=
        CoreMemDesign.runRows_seq hP hclk ds s2 rest hc2 (fun d' hd' => hd d' (by simp [hd'])) (by rw [hv2]; exact hrest)
      refine ⟨s1 :: s2 :: rows, ?_, ?_⟩
      · simp only [cycleRows, runCoreMemRows, hs1, hs2, Res.ok_bind,
          show (lowEntry clk d).isEmpty = false from rfl, show (highEntry clk).isEmpty = false from rfl,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, hrows]
      · simp [cyclePairs, hv1, hv2, hpairs]

#print axioms CoreMemDesign.runRows_seq


/-- A cycle reads its data entry only through the inputs it applies: two entries applying the same inputs give the same
cycle. (How a cycle equation is computed once for every entry that binds an input or leaves it.) -/
theorem CoreMemDesign.cycleV_congr_data (E : CoreMemDesign) (clk : String) (v d d' : SvState)
    (h : applyInputs2 E.scalar.toDesign2 (lowEntry clk d) v = applyInputs2 E.scalar.toDesign2 (lowEntry clk d') v) :
    E.cycleV clk v d = E.cycleV clk v d' := by
  simp only [CoreMemDesign.cycleV, CoreMemDesign.slotV, h]


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

/-- The names an NBA-only body writes. -/
def _root_.LeanModels.Sv.PStmt.nbaTargets : PStmt → List String
  | .nbaAssign t _ => [t]
  | .nbaAssignL (.ident t) _ => [t]
  | .ifStmt _ y n => PStmt.nbaTargets y ++ PStmt.optNbaTargets n
  | .block body => PStmt.listNbaTargets body
  | _ => []

/-- `nbaTargets` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optNbaTargets : Option PStmt → List String
  | none => []
  | some s => PStmt.nbaTargets s

/-- `nbaTargets` of a list. -/
def _root_.LeanModels.Sv.PStmt.listNbaTargets : List PStmt → List String
  | [] => []
  | s :: ss => PStmt.nbaTargets s ++ PStmt.listNbaTargets ss

end

mutual

/-- The names a body reads (conditions and right-hand sides). -/
def _root_.LeanModels.Sv.PStmt.readNames : PStmt → List String
  | .nbaAssign _ e | .blockingAssign _ e | .nbaAssignL _ e | .blockingAssignL _ e => PExpr.sigNames e
  | .ifStmt c y n => PExpr.sigNames c ++ PStmt.readNames y ++ PStmt.optReadNames n
  | .block body => PStmt.listReadNames body
  | _ => []

/-- `readNames` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optReadNames : Option PStmt → List String
  | none => []
  | some s => PStmt.readNames s

/-- `readNames` of a list. -/
def _root_.LeanModels.Sv.PStmt.listReadNames : List PStmt → List String
  | [] => []
  | s :: ss => PStmt.readNames s ++ PStmt.listReadNames ss

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

/-- The unconverted expression nodes of a body (conditions and right-hand sides). -/
def _root_.LeanModels.Sv.PStmt.unconverted : PStmt → List String
  | .nbaAssign _ e | .blockingAssign _ e | .nbaAssignL _ e | .blockingAssignL _ e => PExpr.unconverted e
  | .ifStmt c y n => PExpr.unconverted c ++ PStmt.unconverted y ++ PStmt.optUnconverted n
  | .block body => PStmt.listUnconverted body
  | _ => []

/-- `unconverted` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optUnconverted : Option PStmt → List String
  | none => []
  | some s => PStmt.unconverted s

/-- `unconverted` of a list. -/
def _root_.LeanModels.Sv.PStmt.listUnconverted : List PStmt → List String
  | [] => []
  | s :: ss => PStmt.unconverted s ++ PStmt.listUnconverted ss

end

/-- The unconverted expression nodes of a process. -/
def CoreMemProc.unconverted : CoreMemProc → List String
  | .assign _ v => PExpr.unconverted v
  | .edge f => f.body.unconverted
  | _ => []

/-- The names a process drives. -/
def CoreMemProc.targets : CoreMemProc → List String
  | .assign (.ident n) _ => [n]
  | .edge f => f.body.nbaTargets.eraseDups
  | _ => []

/-- The names a process reads. -/
def CoreMemProc.reads : CoreMemProc → List String
  | .assign _ v => PExpr.sigNames v
  | .edge f => f.body.readNames
  | _ => []

/-- The targets of the continuous assigns of a list. -/
def assignTargets (ps : List CoreMemProc) : List String :=
  ps.flatMap fun p => match p with
    | .assign (.ident n) _ => [n]
    | _ => []

/-- Each continuous assign reads no target of itself or of a LATER assign (topological source order). -/
def topoB : List CoreMemProc → Bool
  | [] => true
  | p :: rest => (match p with
      | .assign _ v => (PExpr.sigNames v).all fun x => !(assignTargets (p :: rest)).contains x
      | _ => true) && topoB rest

/-- **The obligations of the clocked profile**, decided: one driver per signal (the targets of distinct processes are
disjoint, and an assign's target is driven by no other process), the continuous assigns in topological source order
(each reads no target of itself or of a later assign), no process writes an input or the clock, and no process reads
the clock, and no expression of a process holds a node ingestion kept unconverted (`PExpr.unsupported`: the route
refuses it when it is evaluated, so the structure refuses it first). Under them the route's one-pass settle is the
fixpoint of the assigns and the commit of the edge processes' updates does not depend on their order (the cheap
sufficient conditions of rule 4 for this slice). -/
def CoreMemDesign.seqOblB (E : CoreMemDesign) (clk : String) : Bool :=
  let ps := E.processes.toList
  let ts := ps.flatMap CoreMemProc.targets
  let ins := E.scalar.decls.toList.filterMap fun dc => if dc.isInput then some dc.name else none
  ts.Nodup && topoB ps && ts.all (fun t => !ins.contains t && t != clk) &&
    ps.all (fun p => !p.reads.contains clk) && ps.all (fun p => p.unconverted.isEmpty)

/-- **The structure of a clocked family member**: it instantiates, in the clocked profile, with its obligations. -/
def SeqDesign (r : Res CoreMemDesign) (clk : String) : Prop :=
  ∃ E, r = .ok E ∧ E.SeqProfile clk ∧ E.seqOblB clk = true

/-! ## The prover's judgment: every run of a family member -/

/-- **Every clocked run of a canonical-E family member**: the instantiation succeeds and, from every coherent state
(the x start included), on every typed data list, the route's own run of the cycles exists and its samples (pre, post;
one pair per cycle) satisfy `P`. Never vacuous: the run's existence is part of the claim. -/
def SeqRuns (r : Res CoreMemDesign) (clk : String) (P : List (SvState × SvState) → Prop) : Prop :=
  ∃ E, r = .ok E ∧ ∀ (st : CoreMemState) (ins : List SvState), E.Coherent st → (∀ d ∈ ins, E.DataTyped clk d) →
    ∃ rows, runCoreMemRows E st (cycleRows clk ins) = .ok rows ∧
      P (cyclePairs (rows.map fun s => E.scalar.view s.scalar))

/-- The shape of a view: one value per declaration, in declaration order, of its declared width. -/
def CoreMemDesign.ShapeV (E : CoreMemDesign) (v : SvState) : Prop :=
  v.map Prod.fst = E.scalar.decls.toList.map Decl.name ∧
    v.map (fun p => p.2.width) = E.scalar.decls.toList.map Decl.width

private theorem viewAux_widths {s : Store} {E : Elab} (hT : E.Typed s) :
    ∀ (ds : List Decl) (i : Nat), (∀ k (hk : k < ds.length), E.decls[i + k]? = some ds[k]) →
      (viewAux s ds i).map (fun p => p.2.width) = ds.map Decl.width
  | [], _, _ => rfl
  | d :: ds, i, h => by
      have h0 := h 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      have hdecl : E.declOf { decl := i } = some d := by simp [Elab.declOf, h0]
      simp only [viewAux, List.map_cons]
      congr 1
      · rw [(s { decl := i }).width_eq, hT _ d hdecl]; rfl
      · exact viewAux_widths hT ds (i + 1) fun k hk => by
          have := h (k + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- A coherent state's view has the shape. -/
theorem CoreMemDesign.Coherent.shape {E : CoreMemDesign} {st : CoreMemState} (hc : E.Coherent st) :
    E.ShapeV (E.scalar.view st.scalar) :=
  ⟨E.scalar.keys_view st.scalar, viewAux_widths hc.typed E.scalar.decls.toList 0 fun k hk => by simp⟩

/-- **How a `SeqRuns` claim is proved**: from the profile, an invariant every shaped view has, the cycle's success from
the invariant keeping it (the cycle equations), and the claim about every view-level run from the invariant (the
prover's mathematics). -/
theorem SeqRuns.intro {r : Res CoreMemDesign} {E : CoreMemDesign} {clk : String}
    {P : List (SvState × SvState) → Prop} (hr : r = .ok E) (hP : E.SeqProfile clk)
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) (Inv : SvState → Prop)
    (hinv : ∀ v, E.ShapeV v → Inv v)
    (hstep : ∀ v d, Inv v → E.DataTyped clk d → ∃ pre post, E.cycleV clk v d = .ok (pre, post) ∧ Inv post)
    (hrun : ∀ v ins tr, Inv v → (∀ d ∈ ins, E.DataTyped clk d) → E.runV clk v ins = .ok tr → P tr) :
    SeqRuns r clk P := by
  refine ⟨E, hr, fun st ins hc hd => ?_⟩
  have hex : ∀ (ins : List SvState) (v : SvState), Inv v → (∀ d ∈ ins, E.DataTyped clk d) →
      ∃ tr, E.runV clk v ins = .ok tr := by
    intro ins
    induction ins with
    | nil => intro v _ _; exact ⟨[], rfl⟩
    | cons d ds ih =>
        intro v hv hd
        obtain ⟨pre, post, hcyc, hpost⟩ := hstep v d hv (hd d (by simp))
        obtain ⟨tr, htr⟩ := ih post hpost fun d' hd' => hd d' (by simp [hd'])
        exact ⟨(pre, post) :: tr, by simp [CoreMemDesign.runV, hcyc, htr]⟩
  have hv0 := hinv _ hc.shape
  obtain ⟨tr, htr⟩ := hex ins _ hv0 hd
  obtain ⟨rows, hrows, hpairs⟩ := CoreMemDesign.runRows_seq hP hclk ins st tr hc hd htr
  exact ⟨rows, hrows, hpairs ▸ hrun _ ins tr hv0 hd htr⟩

#print axioms SeqRuns.intro








end LeanModels.Sv.Kernel
