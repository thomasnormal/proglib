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
else (`highEntry`). The pre sample is the state after the low slot, the post sample the state after the high slot. An
asynchronous reset is a data input: its fall in the low slot fires its processes there (§9.4.2), so the pre sample
already shows the reset.

* `CoreMemDesign.evalV`, `evalIdxV`, `evalListV`: the route's expression evaluator (`evalExprLocals`) with the store
  replaced by its VIEW (the name-to-value list `evalPure2` reads), for a design without memories; equal to it
  (`evalExprLocals_eq_evalV`) on function-free expressions.
* `CoreMemDesign.execV`: the route's edge-body executor (`execStmtFuel`) on a view: blocking and nonblocking writes to
  whole signals, selects and concatenations, `if`, `case` (every mode, plain and qualified), blocks;
  `execStmtFuel_V`: the route's executor lands on its view and issues exactly its updates, from the body's need on.
* `CoreMemDesign.edgesV`: the route's edge pass on views, each process firing by `CoreMemEdge.fires` (the clock's rise or
  the asynchronous reset's fall, x/z rows included); `runEdges_V`.
* `SeqProfile E clk`: the clocked profile: one clock, edge processes whose bodies `execV` mirrors, continuous assigns
  with their compiled expressions, no memory, no always_comb, no initial, 4-state declarations with distinct names.
* `CoreMemDesign.Coherent`: a state whose store is its cache's, one typed value per declaration.
* `CoreMemDesign.settleV`, `slotV`, `cycleV`: the slot and the cycle on views, mirroring `CoreMemDesign.step` pass for
  pass (four continuous-assign passes per slot, as the route makes them).
* **`CoreMemDesign.step_seq`, `cycle_of_seqProfile`, `runRows_seq`**: the refinement theorems: from every coherent
  state, the route's slots exist, stay coherent, and land exactly on the views `cycleV` computes.
* `seqOblB`: the obligations, and the theorems that USE them: `settleV_idem` (one settle pass is the fixpoint: no
  continuous assignment is out of date when a slot closes), `slotV_eq_slot1V` (the slot is one pass before the edge and
  one after), `edgesV_perm` (every order of the edge processes commits to the same view: rule 4).
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

theorem CoreMemDesign.evalExpr_eq {E : CoreMemDesign} (hm : E.memories.toList = []) (st : CoreMemState)
    (ctx : Option Nat) (e : PExpr) (h : LeanModels.Sv.PExpr.hasFunctionCall e = false) :
    E.evalExpr E.env E.elems st ctx e = E.evalV E.env E.elems (E.scalar.view st.scalar) ctx e :=
  CoreMemDesign.evalExprLocals_eq_evalV hm E.env E.elems st ctx e h

/-! ## Edge bodies: the route's executor on views

`execV` is `execStmtFuel` for a design without memories with the state replaced by its view: the same arms in the same
order, the same refusal messages. A blocking write changes the view (`setV`: `setScalarState`'s conversion to the
declaration's type; a select or concatenation target through the route's own window resolver), a nonblocking write
issues queue entries (the whole signal, or `scalarNbaWindows` of the resolved windows), `case` selects by the §12.5
matcher (`caseHit` per mode) with the route's qualified-case claim check. A `for` loop is the memories slice. -/

mutual

/-- An edge body the view-level executor mirrors: blocking and nonblocking writes (whole signals, selects,
concatenations), `if`, `case` (every mode, plain and qualified), blocks, every expression function-free. A procedural
`for` loop and a statement ingestion kept unconverted are outside. -/
def _root_.LeanModels.Sv.PStmt.edgeOkB : PStmt → Bool
  | .nbaAssign _ e => !LeanModels.Sv.PExpr.hasFunctionCall e
  | .blockingAssign _ e => !LeanModels.Sv.PExpr.hasFunctionCall e
  | .nbaAssignL _ e => !LeanModels.Sv.PExpr.hasFunctionCall e
  | .blockingAssignL _ e => !LeanModels.Sv.PExpr.hasFunctionCall e
  | .ifStmt c y n => !LeanModels.Sv.PExpr.hasFunctionCall c && PStmt.edgeOkB y && PStmt.optEdgeOkB n
  | .block body => PStmt.listEdgeOkB body
  | .caseStmt s items d _ _ =>
      !LeanModels.Sv.PExpr.hasFunctionCall s && PStmt.itemsEdgeOkB items && PStmt.optEdgeOkB d
  | .forLoop .. => false
  | .unsupported .. => false
termination_by structural s => s

/-- `edgeOkB` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optEdgeOkB : Option PStmt → Bool
  | none => true
  | some s => PStmt.edgeOkB s
termination_by structural o => o

/-- `edgeOkB` of every statement of a list. -/
def _root_.LeanModels.Sv.PStmt.listEdgeOkB : List PStmt → Bool
  | [] => true
  | s :: ss => PStmt.edgeOkB s && PStmt.listEdgeOkB ss
termination_by structural xs => xs

/-- `edgeOkB` of the arms of a `case`, their patterns function-free. -/
def _root_.LeanModels.Sv.PStmt.itemsEdgeOkB : List (List PExpr × PStmt) → Bool
  | [] => true
  | (ps, b) :: rest =>
      !LeanModels.Sv.PExpr.hasFunctionCallList ps && PStmt.edgeOkB b && PStmt.itemsEdgeOkB rest
termination_by structural xs => xs

end

mutual

/-- The fuel the route's statement executor (`execStmtFuel`) needs for a body: one per nesting level and per list
element. -/
def _root_.LeanModels.Sv.PStmt.need : PStmt → Nat
  | .ifStmt _ y n => 1 + max (PStmt.need y) (PStmt.optNeed n)
  | .block body => 1 + PStmt.listNeed body
  | .caseStmt _ items d _ _ => 1 + max (PStmt.itemsNeed items) (PStmt.optNeed d)
  | _ => 1
termination_by structural s => s

/-- `need` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optNeed : Option PStmt → Nat
  | none => 0
  | some s => PStmt.need s
termination_by structural o => o

/-- The fuel `execStmtsFuel` needs for a list. -/
def _root_.LeanModels.Sv.PStmt.listNeed : List PStmt → Nat
  | [] => 1
  | s :: ss => 1 + max (PStmt.need s) (PStmt.listNeed ss)
termination_by structural xs => xs

/-- The largest `need` of the arms of a `case`. -/
def _root_.LeanModels.Sv.PStmt.itemsNeed : List (List PExpr × PStmt) → Nat
  | [] => 0
  | (_, b) :: rest => max (PStmt.need b) (PStmt.itemsNeed rest)
termination_by structural xs => xs

end

/-- The value `storeFromView` gives a declaration the view lacks. -/
def declFallback (dc : Decl) : LVec := if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width

/-- The view `storeFromView` materializes: each declaration's value from `raw`, converted to its type. -/
def CoreMemDesign.matV (E : CoreMemDesign) (raw : SvState) : SvState :=
  E.scalar.decls.toList.map fun dc =>
    (dc.name, (Val.ofLVec (VType.ofDecl dc) ((SvState.lookup raw dc.name).getD (declFallback dc))).bits)

/-- `setScalarState` on a view: the value converted to its declaration's type (a name the scalar view does not resolve
is left alone, as the route leaves the state). -/
def CoreMemDesign.setV (E : CoreMemDesign) (v : SvState) (n : String) (x : LVec) : SvState :=
  match E.scalar.resolve n with
  | some id =>
      match E.scalar.declOf id with
      | some dc => SvState.set v n (Val.ofLVec (VType.ofDecl dc) x).bits
      | none => v
  | none => v

/-- `writeScalarLhs2` on a view: a concatenation written window by window (`writeConcatLhs2`) and materialized as
`compactScalar` does; a select written into its window of the old value; a no-write window (an x/z or out-of-range
index, §11.5.1) changes nothing. -/
def CoreMemDesign.writeLhsV (E : CoreMemDesign) (v : SvState) (lhs : Lhs2) (value : LVec) : Res SvState :=
  match lhs with
  | .concat _ => do
      let windows ← resolveConcatLhs2 4096 v lhs
      let v' ← writeConcatLhs2 v value windows
      .ok (E.matV v')
  | _ => do
      let (name, window) ← resolveLhs2 4096 v lhs
      match window with
      | none => .ok v
      | some (lo, width) =>
          match E.scalar.resolve name with
          | none => .unsupported s!"11.5.1: scalar select target '{name}' is undeclared"
          | some _ => .ok (E.setV v name (((SvState.lookup v name).getD ⟨#[]⟩).insertAt lo (value.resizeU width)))

/-- `coreMemCaseHits` on a view: how many arms have a pattern that hits the subject. -/
def CoreMemDesign.caseHitsV (E : CoreMemDesign) (v : SvState) (subject : LVec) (mode : CaseMode) :
    List (List PExpr × PStmt) → Res Nat
  | [] => .ok 0
  | (patterns, _) :: rest => do
      let values ← E.evalListV E.env E.elems v patterns
      let n ← E.caseHitsV v subject mode rest
      .ok (if values.any (fun value => caseHit mode subject value) then n + 1 else n)

mutual

/-- **The route's edge-body executor on a view** (`execStmtFuel` for a design without memories): the view after the
body's blocking writes, and the nonblocking updates it issues, in issue order. -/
def CoreMemDesign.execV (E : CoreMemDesign) (v : SvState) : PStmt → Res (SvState × NbaQueue2)
  | .nbaAssign t e =>
      match E.scalarTarget t with
      | none => .unsupported s!"11.5.1: scalar NBA target '{t}' is undeclared"
      | some w => do
          let x ← E.evalV E.env E.elems v (some w) e
          .ok (v, [(t, 0, x)])
  | .nbaAssignL lhs e =>
      match lhs with
      | .ident t =>
          match E.scalarTarget t with
          | none => .unsupported s!"11.5.1: scalar NBA target '{t}' is undeclared"
          | some w => do
              let x ← E.evalV E.env E.elems v (some w) e
              .ok (v, [(t, 0, x)])
      | target => do
          let lw ← E.scalarLhs2 E.env E.elems target
          let x ← E.evalV E.env E.elems v (some lw.2) e
          let windows ← resolveConcatLhs2 4096 v lw.1
          .ok (v, scalarNbaWindows x windows)
  | .blockingAssign n e =>
      match E.scalarTarget n with
      | none => .unsupported s!"9.2.2.1: scalar edge target '{n}' is undeclared"
      | some w => do
          let x ← E.evalV E.env E.elems v (some w) e
          .ok (E.setV v n x, [])
  | .blockingAssignL lhs e =>
      match lhs with
      | .ident n =>
          match E.scalarTarget n with
          | none => .unsupported s!"9.2.2.1: scalar edge target '{n}' is undeclared"
          | some w => do
              let x ← E.evalV E.env E.elems v (some w) e
              .ok (E.setV v n x, [])
      | target => do
          let lw ← E.scalarLhs2 E.env E.elems target
          let x ← E.evalV E.env E.elems v (some lw.2) e
          let v' ← E.writeLhsV v lw.1 x
          .ok (v', [])
  | .ifStmt c y n => do
      let cv ← E.evalV E.env E.elems v (some 1) c
      if cv.condTrue then E.execV v y else E.execOptV v n
  | .block body => E.execListV v body
  | .caseStmt subject items d mode check => do
      let sv ← E.evalV E.env E.elems v none subject
      match check with
      | .none => E.execItemsV v sv mode items (E.execOptV v d)
      | qualifier => do
          let n ← E.caseHitsV v sv mode items
          if caseClaimOk qualifier d.isSome n then E.execItemsV v sv mode items (E.execOptV v d)
          else .unsupported s!"12.5.3: {caseCheckName qualifier}"
  | .forLoop .. =>
      .unsupported "9.4.2: a procedural `for` loop in an edge body is outside the clocked profile (the memories slice)"
  | .unsupported kind text => .unsupported s!"{kind}: {text}"
termination_by structural s => s

/-- `execV` of an optional statement (none changes nothing). -/
def CoreMemDesign.execOptV (E : CoreMemDesign) (v : SvState) : Option PStmt → Res (SvState × NbaQueue2)
  | none => .ok (v, [])
  | some s => E.execV v s
termination_by structural o => o

/-- `execV` of a statement list: the view threaded, the queues concatenated in order. -/
def CoreMemDesign.execListV (E : CoreMemDesign) (v : SvState) : List PStmt → Res (SvState × NbaQueue2)
  | [] => .ok (v, [])
  | s :: ss => do
      let a ← E.execV v s
      let b ← E.execListV a.1 ss
      .ok (b.1, a.2 ++ b.2)
termination_by structural xs => xs

/-- The arms of a `case`: the first item one of whose patterns hits the subject (§12.5, `caseHit` per mode) runs;
when no item hits, `dflt` (the caller passes the default's run: a value, so a pure function may take it whether or not
it is selected). -/
def CoreMemDesign.execItemsV (E : CoreMemDesign) (v : SvState) (sv : LVec) (mode : CaseMode) :
    List (List PExpr × PStmt) → Res (SvState × NbaQueue2) → Res (SvState × NbaQueue2)
  | [], dflt => dflt
  | (patterns, body) :: rest, dflt => do
      let values ← E.evalListV E.env E.elems v patterns
      if values.any (fun value => caseHit mode sv value) then E.execV v body
      else E.execItemsV v sv mode rest dflt
termination_by structural xs => xs

end

/-! ## The clocked profile and coherent states -/

/-- A process of the clocked profile, at index `i` of the design: a continuous assign to a whole declared scalar whose
compiled expression is present (memory- and function-free source), or an edge process on `clk` (with or without an
asynchronous reset) whose body the view-level executor mirrors, within the route's statement fuel. -/
def CoreMemDesign.ProcOk (E : CoreMemDesign) (clk : String) (i : Nat) : CoreMemProc → Prop
  | .assign (.ident n) v => LeanModels.Sv.PExpr.hasMemoryRead v = false ∧
      LeanModels.Sv.PExpr.hasFunctionCall v = false ∧ (∃ c, E.compiledAssigns[i]? = some (some c)) ∧
      (E.scalarWidth? n).isSome = true
  | .edge f => f.clock = clk ∧ f.body.edgeOkB = true ∧ f.body.need ≤ 4096
  | _ => False

/-- **The clocked profile** (slice 1) of a canonical-E design: no memory, the scalar edge view's declarations are the
scalar view's, distinct names, every declaration 4-state, every process `ProcOk`. -/
structure CoreMemDesign.SeqProfile (E : CoreMemDesign) (clk : String) : Prop where
  noMem : E.memories.toList = []
  base : E.scalarEdge.base = E.scalar
  names : (E.scalar.decls.toList.map Decl.name).Nodup
  four : AllFour E.scalar
  procs : ∀ (i : Nat) (p : CoreMemProc), E.processes[i]? = some p → E.ProcOk clk i p

/-- `ProcOk`, decided (the structure stage decides the profile through it, for any number of processes). -/
def CoreMemDesign.procOkB (E : CoreMemDesign) (clk : String) (i : Nat) : CoreMemProc → Bool
  | .assign (.ident n) v => !LeanModels.Sv.PExpr.hasMemoryRead v && !LeanModels.Sv.PExpr.hasFunctionCall v &&
      (match E.compiledAssigns[i]? with
        | some (some _) => true
        | _ => false) && (E.scalarWidth? n).isSome
  | .edge f => f.clock == clk && f.body.edgeOkB && decide (f.body.need ≤ 4096)
  | _ => false

theorem CoreMemDesign.procOkB_spec {E : CoreMemDesign} {clk : String} {i : Nat} {p : CoreMemProc}
    (h : E.procOkB clk i p = true) : E.ProcOk clk i p := by
  cases p with
  | assign t v =>
      cases t with
      | ident n =>
          simp only [CoreMemDesign.procOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
          refine ⟨h1, h2, ?_, h4⟩
          split at h3
          · rename_i c hc; exact ⟨c, hc⟩
          · simp at h3
      | _ => simp [CoreMemDesign.procOkB] at h
  | edge f =>
      simp only [CoreMemDesign.procOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
  | initial _ => simp [CoreMemDesign.procOkB] at h
  | comb _ => simp [CoreMemDesign.procOkB] at h
  | implicit _ => simp [CoreMemDesign.procOkB] at h
  | unsupported _ _ => simp [CoreMemDesign.procOkB] at h

/-- Every process from index `i` on is `ProcOk`, decided. -/
def CoreMemDesign.procsOkFrom (E : CoreMemDesign) (clk : String) : Nat → List CoreMemProc → Bool
  | _, [] => true
  | i, p :: ps => E.procOkB clk i p && E.procsOkFrom clk (i + 1) ps

theorem CoreMemDesign.procsOkFrom_spec {E : CoreMemDesign} {clk : String} :
    ∀ (ps : List CoreMemProc) (i : Nat), E.procsOkFrom clk i ps = true →
      ∀ k p, ps[k]? = some p → E.ProcOk clk (i + k) p
  | [], _, _, k, p, hk => by simp at hk
  | q :: ps, i, h, k, p, hk => by
      simp only [CoreMemDesign.procsOkFrom, Bool.and_eq_true] at h
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          simpa using CoreMemDesign.procOkB_spec h.1
      | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          have := CoreMemDesign.procsOkFrom_spec ps (i + 1) h.2 k p hk
          rwa [show i + 1 + k = i + (k + 1) by omega] at this

/-- The profile from its decided parts (how the structure stage proves it). -/
theorem CoreMemDesign.SeqProfile.of_B {E : CoreMemDesign} {clk : String} (hm : E.memories.toList = [])
    (hb : E.scalarEdge.base = E.scalar) (hn : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar)
    (hp : E.procsOkFrom clk 0 E.processes.toList = true) : E.SeqProfile clk :=
  ⟨hm, hb, hn, h4, fun i p hi => by
    have := CoreMemDesign.procsOkFrom_spec _ 0 hp i p (by rw [Array.getElem?_toList]; exact hi)
    simpa using this⟩

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

/-! ## The edge-body executor on views refines the route's -/

/-- `setScalarState` on a coherent state is `setV` on its view, and stays coherent. -/
theorem CoreMemDesign.setV_spec {E : CoreMemDesign} {st : CoreMemState} (hc : E.Coherent st) {n : String}
    {x : VarId} (hx : E.scalar.resolve n = some x) (v : LVec) :
    E.scalar.view (E.setScalarState st n v).scalar = E.setV (E.scalar.view st.scalar) n v ∧
      E.Coherent (E.setScalarState st n v) := by
  obtain ⟨dc, hdc, -, -, -⟩ := Elab.resolve_some hx
  have hty : (st.scalar x).ty = VType.ofDecl dc := hc.typed x dc hdc
  obtain ⟨h1, h2⟩ := CoreMemDesign.setScalarState_spec hc hx v
  refine ⟨?_, h2⟩
  rw [h1, hty]
  simp [CoreMemDesign.setV, hx, hdc]

/-- `compactScalar` on a coherent state: the materialized view, coherent. -/
theorem CoreMemDesign.compactScalar_view {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {st : CoreMemState} (hc : E.Coherent st) (w : SvState) :
    E.scalar.view (E.compactScalar st w).scalar = E.matV w ∧ E.Coherent (E.compactScalar st w) := by
  unfold CoreMemDesign.compactScalar
  split
  · rename_i h
    refine ⟨?_, hc⟩
    rw [← h, CoreMemDesign.matV_view hnd h4 hc.typed]
  · refine ⟨?_, E.normalizeScalar_coherent st (E.typed_storeFromView w)⟩
    show E.scalar.view (E.normalizeScalar st (E.storeFromView w)).scalar = _
    rw [E.normalizeScalar_view, E.view_storeFromView]

/-- `writeScalarLhs2` on a coherent state is `writeLhsV` on its view. -/
theorem CoreMemDesign.writeLhs_V {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {st : CoreMemState} (hc : E.Coherent st) (lhs : Lhs2) (x : LVec) {v' : SvState}
    (h : E.writeLhsV (E.scalar.view st.scalar) lhs x = .ok v') :
    ∃ st', E.writeScalarLhs2 st lhs x = .ok st' ∧ E.scalar.view st'.scalar = v' ∧ E.Coherent st' := by
  cases lhs
  case concat parts =>
    simp only [CoreMemDesign.writeLhsV, Res.bind_eq_ok, Res.ok.injEq] at h
    obtain ⟨ws, hws, w', hw', rfl⟩ := h
    obtain ⟨h1, h2⟩ := CoreMemDesign.compactScalar_view hnd h4 hc w'
    exact ⟨_, by simp [CoreMemDesign.writeScalarLhs2, hws, hw'], h1, h2⟩
  all_goals
    simp only [CoreMemDesign.writeLhsV, Res.bind_eq_ok] at h
    obtain ⟨⟨name, window⟩, hr, hw⟩ := h
    dsimp only at hw
    cases window with
    | none =>
        simp only [Res.ok.injEq] at hw
        subst hw
        exact ⟨st, by simp [CoreMemDesign.writeScalarLhs2, hr], rfl, hc⟩
    | some lw =>
        obtain ⟨lo, width⟩ := lw
        cases hx : E.scalar.resolve name with
        | none => simp [hx] at hw
        | some xid =>
            simp only [hx, Res.ok.injEq] at hw
            subst hw
            have hl : SvState.lookup (E.scalar.view st.scalar) name = some (st.scalar xid).bits := by
              rw [Elab.lookup_view, hx]; rfl
            obtain ⟨h1, h2⟩ := CoreMemDesign.setV_spec hc hx ((st.scalar xid).bits.insertAt lo (x.resizeU width))
            exact ⟨_, by simp [CoreMemDesign.writeScalarLhs2, hr, hx], by rw [h1, hl]; rfl, h2⟩

/-- The route's pattern-list evaluator is `evalListV` on the view (no memories, function-free patterns). -/
theorem CoreMemDesign.evalMemExprList_eq {E : CoreMemDesign} (hm : E.memories.toList = []) (st : CoreMemState) :
    ∀ (ps : List PExpr), LeanModels.Sv.PExpr.hasFunctionCallList ps = false →
      evalMemExprList E E.env E.elems st ps = E.evalListV E.env E.elems (E.scalar.view st.scalar) ps
  | [], _ => by simp [evalMemExprList, CoreMemDesign.evalListV]
  | p :: ps, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCallList, Bool.or_eq_false_iff] at h
      simp only [evalMemExprList, CoreMemDesign.evalListV, CoreMemDesign.evalExpr_eq hm st none p h.1,
        CoreMemDesign.evalMemExprList_eq hm st ps h.2]

/-- The route's qualified-case hit count is `caseHitsV` on the view. -/
theorem CoreMemDesign.caseHits_eq {E : CoreMemDesign} (hm : E.memories.toList = []) (st : CoreMemState)
    (sv : LVec) (mode : CaseMode) :
    ∀ (items : List (List PExpr × PStmt)), PStmt.itemsEdgeOkB items = true →
      coreMemCaseHits E E.env E.elems st sv mode items = E.caseHitsV (E.scalar.view st.scalar) sv mode items
  | [], _ => by simp [coreMemCaseHits, CoreMemDesign.caseHitsV]
  | (ps, b) :: rest, h => by
      simp only [PStmt.itemsEdgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
      simp only [coreMemCaseHits, CoreMemDesign.caseHitsV, CoreMemDesign.evalMemExprList_eq hm st ps h.1.1,
        CoreMemDesign.caseHits_eq hm st sv mode rest h.2]

mutual

/-- **THE EDGE-BODY REFINEMENT**: for a design without memories, from a coherent state, when the view-level executor
gives `(v', q)` the route's edge-body executor (at every fuel from the body's need on) leaves a coherent state whose
view is `v'` and issues exactly `q` (no memory updates). -/
theorem CoreMemDesign.execStmtFuel_V {E : CoreMemDesign} (hm : E.memories.toList = [])
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar) :
    ∀ (b : PStmt) (fuel : Nat) (st : CoreMemState) (v' : SvState) (q : NbaQueue2), E.Coherent st →
      b.edgeOkB = true → b.need ≤ fuel → E.execV (E.scalar.view st.scalar) b = .ok (v', q) →
      ∃ st', E.execStmtFuel E.env E.elems st fuel b = .ok ⟨st', q, []⟩ ∧ E.scalar.view st'.scalar = v' ∧
        E.Coherent st'
  | .nbaAssign t e, fuel, st, v', q, hc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.not_eq_true'] at hb
      simp only [CoreMemDesign.execV] at hv
      cases hw : E.scalarTarget t with
      | none => simp [hw] at hv
      | some w =>
          simp only [hw, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨x, hx, rfl, rfl⟩ := hv
          refine ⟨st, ?_, rfl, hc⟩
          simp [CoreMemDesign.execStmtFuel, hw, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx,
            CoreMemDesign.issueTarget, CoreMemExec.fromQueue]
  | .nbaAssignL lhs e, fuel, st, v', q, hc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.not_eq_true'] at hb
      cases lhs with
      | ident t =>
          simp only [CoreMemDesign.execV] at hv
          cases hw : E.scalarTarget t with
          | none => simp [hw] at hv
          | some w =>
              simp only [hw, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
              obtain ⟨x, hx, rfl, rfl⟩ := hv
              refine ⟨st, ?_, rfl, hc⟩
              simp [CoreMemDesign.execStmtFuel, hw, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx,
                CoreMemDesign.issueTarget, CoreMemExec.fromQueue]
      | arrayElem name indices =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl⟩ := hv
          dsimp only at hx hws
          refine ⟨st, ?_, rfl, hc⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemDesign.memDecl?_none hm, hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx,
            CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
      | bitSel name idx =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl⟩ := hv
          dsimp only at hx hws
          refine ⟨st, ?_, rfl, hc⟩
          simp [CoreMemDesign.execStmtFuel, hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx,
            CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
      | partSel name a b =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl⟩ := hv
          dsimp only at hx hws
          refine ⟨st, ?_, rfl, hc⟩
          simp [CoreMemDesign.execStmtFuel, hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx,
            CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
      | concat parts =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl⟩ := hv
          dsimp only at hx hws
          refine ⟨st, ?_, rfl, hc⟩
          simp [CoreMemDesign.execStmtFuel, hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx,
            CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
      | arrayPart name indices mode a b =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl⟩ := hv
          dsimp only at hx hws
          refine ⟨st, ?_, rfl, hc⟩
          simp [CoreMemDesign.execStmtFuel, hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx,
            CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
  | .blockingAssign n e, fuel, st, v', q, hc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.not_eq_true'] at hb
      simp only [CoreMemDesign.execV] at hv
      cases hw : E.scalarTarget n with
      | none => simp [hw] at hv
      | some w =>
          simp only [hw, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨x, hx, rfl, rfl⟩ := hv
          obtain ⟨xid, hxid⟩ := CoreMemDesign.scalarWidth?_some (E := E) (n := n) (by
            have hw' : E.scalarWidth? n = some w := hw
            simp [hw'])
          obtain ⟨h1, h2⟩ := CoreMemDesign.setV_spec hc hxid x
          refine ⟨_, ?_, h1, h2⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemDesign.execBlockingTarget, hw,
            CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx]
  | .blockingAssignL lhs e, fuel, st, v', q, hc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.not_eq_true'] at hb
      cases lhs with
      | ident n =>
          simp only [CoreMemDesign.execV] at hv
          cases hw : E.scalarTarget n with
          | none => simp [hw] at hv
          | some w =>
              simp only [hw, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
              obtain ⟨x, hx, rfl, rfl⟩ := hv
              obtain ⟨xid, hxid⟩ := CoreMemDesign.scalarWidth?_some (E := E) (n := n) (by
                have hw' : E.scalarWidth? n = some w := hw
                simp [hw'])
              obtain ⟨h1, h2⟩ := CoreMemDesign.setV_spec hc hxid x
              refine ⟨_, ?_, h1, h2⟩
              simp [CoreMemDesign.execStmtFuel, CoreMemDesign.execBlockingTarget, hw,
                CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx]
      | arrayElem name indices =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl⟩ := hv
          dsimp only at hx hw'
          obtain ⟨st', hs', hv'', hc'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
          refine ⟨st', ?_, hv'', hc'⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemDesign.execBlockingTarget, CoreMemDesign.memDecl?_none hm, CoreMemDesign.execScalarTarget,
            hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx, hs']
      | bitSel name idx =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl⟩ := hv
          dsimp only at hx hw'
          obtain ⟨st', hs', hv'', hc'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
          refine ⟨st', ?_, hv'', hc'⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemDesign.execBlockingTarget, CoreMemDesign.execScalarTarget,
            hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx, hs']
      | partSel name a b =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl⟩ := hv
          dsimp only at hx hw'
          obtain ⟨st', hs', hv'', hc'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
          refine ⟨st', ?_, hv'', hc'⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemDesign.execBlockingTarget, CoreMemDesign.execScalarTarget,
            hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx, hs']
      | concat parts =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl⟩ := hv
          dsimp only at hx hw'
          obtain ⟨st', hs', hv'', hc'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
          refine ⟨st', ?_, hv'', hc'⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemDesign.execBlockingTarget, CoreMemDesign.execScalarTarget,
            hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx, hs']
      | arrayPart name indices mode a b =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl⟩ := hv
          dsimp only at hx hw'
          obtain ⟨st', hs', hv'', hc'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
          refine ⟨st', ?_, hv'', hc'⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemDesign.execBlockingTarget, CoreMemDesign.execScalarTarget,
            hl, CoreMemDesign.evalExpr_eq hm st (some w) e hb, hx, hs']
  | .ifStmt c y n, fuel, st, v', q, hc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at hb
      obtain ⟨⟨hcf, hy⟩, hn⟩ := hb
      simp only [PStmt.need] at hf
      have hfy : y.need ≤ f := by omega
      have hfn : PStmt.optNeed n ≤ f := by omega
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at hv
      obtain ⟨cv, hcv, hv⟩ := hv
      have hcv' : E.evalExpr E.env E.elems st (some 1) c = .ok cv := by
        rw [CoreMemDesign.evalExpr_eq hm st (some 1) c hcf]; exact hcv
      by_cases hct : cv.condTrue = true
      · simp only [hct, ↓reduceIte] at hv
        obtain ⟨st', hs, hv', hc'⟩ := CoreMemDesign.execStmtFuel_V hm hnd h4 y f st v' q hc hy hfy hv
        exact ⟨st', by simp [CoreMemDesign.execStmtFuel, hcv', hct, hs], hv', hc'⟩
      · simp only [hct, Bool.false_eq_true, ↓reduceIte] at hv
        cases n with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq, Prod.mk.injEq] at hv
            obtain ⟨rfl, rfl⟩ := hv
            exact ⟨st, by simp [CoreMemDesign.execStmtFuel, hcv', hct], rfl, hc⟩
        | some s =>
            simp only [PStmt.optEdgeOkB] at hn
            simp only [PStmt.optNeed] at hfn
            simp only [CoreMemDesign.execOptV] at hv
            obtain ⟨st', hs, hv', hc'⟩ := CoreMemDesign.execStmtFuel_V hm hnd h4 s f st v' q hc hn hfn hv
            exact ⟨st', by simp [CoreMemDesign.execStmtFuel, hcv', hct, hs], hv', hc'⟩
  | .block body, fuel, st, v', q, hc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB] at hb
      simp only [PStmt.need] at hf
      simp only [CoreMemDesign.execV] at hv
      obtain ⟨st', hs, hv', hc'⟩ := CoreMemDesign.execStmtsFuel_V hm hnd h4 body f st v' q hc hb (by omega) hv
      exact ⟨st', by simp only [CoreMemDesign.execStmtFuel]; exact hs, hv', hc'⟩
  | .caseStmt subject items d mode check, fuel, st, v', q, hc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at hb
      obtain ⟨⟨hs, hi⟩, hd⟩ := hb
      simp only [PStmt.need] at hf
      have hfi : PStmt.itemsNeed items ≤ f := by omega
      have hfd : PStmt.optNeed d ≤ f := by omega
      have hdef : ∀ s, d = some s → E.execV (E.scalar.view st.scalar) s = .ok (v', q) →
          ∃ st', E.execStmtFuel E.env E.elems st f s = .ok ⟨st', q, []⟩ ∧ E.scalar.view st'.scalar = v' ∧
            E.Coherent st' := by
        intro s hds hx
        subst hds
        simp only [PStmt.optEdgeOkB] at hd
        simp only [PStmt.optNeed] at hfd
        exact CoreMemDesign.execStmtFuel_V hm hnd h4 s f st v' q hc hd hfd hx
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at hv
      obtain ⟨sv, hsv, hv⟩ := hv
      have hsv' : E.evalExpr E.env E.elems st none subject = .ok sv := by
        rw [CoreMemDesign.evalExpr_eq hm st none subject hs]; exact hsv
      have hrun : E.execItemsV (E.scalar.view st.scalar) sv mode items
          (E.execOptV (E.scalar.view st.scalar) d) = .ok (v', q) →
          ∃ sel st', coreMemSelectCase E E.env E.elems st sv mode items d = .ok sel ∧
            ((sel = none ∧ st' = st ∧ q = []) ∨
              ∃ body, sel = some body ∧ E.execStmtFuel E.env E.elems st f body = .ok ⟨st', q, []⟩) ∧
            E.scalar.view st'.scalar = v' ∧ E.Coherent st' := by
        intro hr
        rcases CoreMemDesign.execItems_V hm hnd h4 sv mode items f st _ _ hc hi hfi hr with
          ⟨body, st', hsel, hs, hv1, hc1⟩ | ⟨hsel, hdf⟩
        · exact ⟨some body, st', hsel d, Or.inr ⟨body, rfl, hs⟩, hv1, hc1⟩
        · cases d with
          | none =>
              simp only [CoreMemDesign.execOptV, Res.ok.injEq, Prod.mk.injEq] at hdf
              obtain ⟨rfl, rfl⟩ := hdf
              exact ⟨none, st, hsel none, Or.inl ⟨rfl, rfl, rfl⟩, rfl, hc⟩
          | some s =>
              simp only [CoreMemDesign.execOptV] at hdf
              obtain ⟨st', hs, hv1, hc1⟩ := hdef s rfl hdf
              exact ⟨some s, st', hsel (some s), Or.inr ⟨s, rfl, hs⟩, hv1, hc1⟩
      cases check
      case none =>
          obtain ⟨sel, st', hsel, hcase, h2, h3⟩ := hrun hv
          refine ⟨st', ?_, h2, h3⟩
          rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨body, rfl, hs⟩
          · simp [CoreMemDesign.execStmtFuel, hsv', hsel]
          · simp [CoreMemDesign.execStmtFuel, hsv', hsel, hs]
      all_goals
          simp only [Res.bind_eq_ok] at hv
          obtain ⟨n, hn, hv⟩ := hv
          have hn' : coreMemCaseHits E E.env E.elems st sv mode items = .ok n := by
            rw [CoreMemDesign.caseHits_eq hm st sv mode items hi]; exact hn
          split at hv
          · rename_i hok
            obtain ⟨sel, st', hsel, hcase, h2, h3⟩ := hrun hv
            refine ⟨st', ?_, h2, h3⟩
            rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨body, rfl, hs⟩
            · simp [CoreMemDesign.execStmtFuel, hsv', hn', hok, hsel]
            · simp [CoreMemDesign.execStmtFuel, hsv', hn', hok, hsel, hs]
          · simp at hv
  | .forLoop .., _, _, _, _, _, hb, _, _ => by simp [PStmt.edgeOkB] at hb
  | .unsupported .., _, _, _, _, _, hb, _, _ => by simp [PStmt.edgeOkB] at hb

/-- The list form of `execStmtFuel_V`: the route's `execStmtsFuel` threads the state as `execListV` threads the view. -/
theorem CoreMemDesign.execStmtsFuel_V {E : CoreMemDesign} (hm : E.memories.toList = [])
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar) :
    ∀ (bs : List PStmt) (fuel : Nat) (st : CoreMemState) (v' : SvState) (q : NbaQueue2), E.Coherent st →
      PStmt.listEdgeOkB bs = true → PStmt.listNeed bs ≤ fuel →
      E.execListV (E.scalar.view st.scalar) bs = .ok (v', q) →
      ∃ st', E.execStmtsFuel E.env E.elems st fuel bs = .ok ⟨st', q, []⟩ ∧ E.scalar.view st'.scalar = v' ∧
        E.Coherent st'
  | [], fuel, st, v', q, hc, _, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.listNeed] at hf; omega⟩
      simp only [CoreMemDesign.execListV, Res.ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact ⟨st, rfl, rfl, hc⟩
  | s :: ss, fuel, st, v', q, hc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.listNeed] at hf; omega⟩
      simp only [PStmt.listEdgeOkB, Bool.and_eq_true] at hb
      simp only [PStmt.listNeed] at hf
      simp only [CoreMemDesign.execListV, Res.bind_eq_ok, Res.ok.injEq] at hv
      obtain ⟨⟨v1, a⟩, h1, ⟨v2, b⟩, h2, hq⟩ := hv
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      obtain ⟨st1, hs1, hv1, hc1⟩ := CoreMemDesign.execStmtFuel_V hm hnd h4 s f st v1 a hc hb.1 (by omega) h1
      obtain ⟨st2, hs2, hv2, hc2⟩ :=
        CoreMemDesign.execStmtsFuel_V hm hnd h4 ss f st1 v2 b hc1 hb.2 (by omega) (by rw [hv1]; exact h2)
      exact ⟨st2, by simp [CoreMemDesign.execStmtsFuel, hs1, hs2, CoreMemExec.append], hv2, hc2⟩

/-- The arms of a `case`: when the view-level search finds an arm, the route's selection finds the same arm and its
run lands on the same view and queue; when it finds none, the route's selection falls to the default and the result is
the default's. -/
theorem CoreMemDesign.execItems_V {E : CoreMemDesign} (hm : E.memories.toList = [])
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar) (sv : LVec) (mode : CaseMode) :
    ∀ (items : List (List PExpr × PStmt)) (fuel : Nat) (st : CoreMemState) (dflt : Res (SvState × NbaQueue2))
      (res : SvState × NbaQueue2),
      E.Coherent st → PStmt.itemsEdgeOkB items = true → PStmt.itemsNeed items ≤ fuel →
      E.execItemsV (E.scalar.view st.scalar) sv mode items dflt = .ok res →
      (∃ body st', (∀ d, coreMemSelectCase E E.env E.elems st sv mode items d = .ok (some body)) ∧
          E.execStmtFuel E.env E.elems st fuel body = .ok ⟨st', res.2, []⟩ ∧ E.scalar.view st'.scalar = res.1 ∧
            E.Coherent st') ∨
        ((∀ d, coreMemSelectCase E E.env E.elems st sv mode items d = .ok d) ∧ dflt = .ok res)
  | [], fuel, st, dflt, res, hc, _, _, hv => by
      simp only [CoreMemDesign.execItemsV] at hv
      exact Or.inr ⟨fun d => rfl, hv⟩
  | (ps, b) :: rest, fuel, st, dflt, res, hc, hb, hf, hv => by
      simp only [PStmt.itemsEdgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at hb
      simp only [PStmt.itemsNeed] at hf
      simp only [CoreMemDesign.execItemsV, Res.bind_eq_ok] at hv
      obtain ⟨vals, hvals, hv⟩ := hv
      have hpe : evalMemExprList E E.env E.elems st ps = .ok vals := by
        rw [CoreMemDesign.evalMemExprList_eq hm st ps hb.1.1]; exact hvals
      by_cases hhit : vals.any (fun value => caseHit mode sv value) = true
      · simp only [hhit, ↓reduceIte] at hv
        obtain ⟨v', q⟩ := res
        obtain ⟨st', hs, hv', hc'⟩ := CoreMemDesign.execStmtFuel_V hm hnd h4 b fuel st v' q hc hb.1.2 (by omega) hv
        exact Or.inl ⟨b, st', fun d => by simp only [coreMemSelectCase, hpe, Res.ok_bind, hhit, ↓reduceIte], hs,
          hv', hc'⟩
      · rw [Bool.not_eq_true] at hhit
        simp only [hhit, Bool.false_eq_true, ↓reduceIte] at hv
        rcases CoreMemDesign.execItems_V hm hnd h4 sv mode rest fuel st dflt res hc hb.2 (by omega) hv with
          ⟨body, st', hsel, hs, hv', hc'⟩ | ⟨hsel, hdf⟩
        · exact Or.inl ⟨body, st', fun d => by
            simp only [coreMemSelectCase, hpe, Res.ok_bind, hhit, Bool.false_eq_true, ↓reduceIte, hsel d],
            hs, hv', hc'⟩
        · exact Or.inr ⟨fun d => by
            simp only [coreMemSelectCase, hpe, Res.ok_bind, hhit, Bool.false_eq_true, ↓reduceIte, hsel d], hdf⟩

end

#print axioms CoreMemDesign.execStmtFuel_V

/-! ## The edge pass and the slot -/

/-- **The edge pass on views** (`runEdges`): every edge process whose clock rose or whose asynchronous reset fell from
the slot's start view `before` to the pre-edge view `after` (`CoreMemEdge.fires`: §9.4.2's edge table, x/z rows
included) runs its body on the threaded view; the updates are concatenated in process order. -/
def CoreMemDesign.edgesV (E : CoreMemDesign) (before after : SvState) (v : SvState) :
    List CoreMemProc → Res (SvState × NbaQueue2)
  | [] => .ok (v, [])
  | .edge p :: rest =>
      if p.fires before after then do
        let a ← E.execV v p.body
        let b ← E.edgesV before after a.1 rest
        .ok (b.1, a.2 ++ b.2)
      else E.edgesV before after v rest
  | _ :: rest => E.edgesV before after v rest

/-- The shape of a process of the clocked profile, without its index. -/
def CoreMemDesign.ProcShape (clk : String) : CoreMemProc → Prop
  | .assign _ _ => True
  | .edge f => f.clock = clk ∧ f.body.edgeOkB = true ∧ f.body.need ≤ 4096
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

/-- **The edge pass refinement**: from a coherent state, when the view-level edge pass gives `(v', q)` the route's
`runEdges` leaves a coherent state whose view is `v'` and issues exactly `q`. -/
theorem CoreMemDesign.runEdges_V {E : CoreMemDesign} (hm : E.memories.toList = [])
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar) (clk : String)
    (before after : SvState) :
    ∀ (procs : List CoreMemProc), (∀ p ∈ procs, CoreMemDesign.ProcShape clk p) →
    ∀ (st : CoreMemState) (v' : SvState) (q : NbaQueue2), E.Coherent st →
      E.edgesV before after (E.scalar.view st.scalar) procs = .ok (v', q) →
      ∃ st', E.runEdges E.env E.elems st before after procs = .ok ⟨st', q, []⟩ ∧
        E.scalar.view st'.scalar = v' ∧ E.Coherent st'
  | [], _, st, v', q, hc, hv => by
      simp only [CoreMemDesign.edgesV, Res.ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact ⟨st, rfl, rfl, hc⟩
  | p :: rest, h, st, v', q, hc, hv => by
      have hrest : ∀ q ∈ rest, CoreMemDesign.ProcShape clk q := fun q hq => h q (by simp [hq])
      have hp := h p (by simp)
      cases p with
      | edge f =>
          obtain ⟨-, hb, hn⟩ := hp
          simp only [CoreMemDesign.edgesV] at hv
          by_cases hf : f.fires before after = true
          · simp only [hf, ↓reduceIte, Res.bind_eq_ok, Res.ok.injEq] at hv
            obtain ⟨⟨v1, a⟩, h1, ⟨v2, b⟩, h2, hq⟩ := hv
            simp only [Prod.mk.injEq] at hq
            obtain ⟨rfl, rfl⟩ := hq
            obtain ⟨st1, hs1, hv1, hc1⟩ := CoreMemDesign.execStmtFuel_V hm hnd h4 f.body 4096 st v1 a hc hb hn h1
            obtain ⟨st2, hs2, hv2, hc2⟩ := CoreMemDesign.runEdges_V hm hnd h4 clk before after rest hrest st1 v2 b
              hc1 (by rw [hv1]; exact h2)
            exact ⟨st2, by simp [CoreMemDesign.runEdges, hf, CoreMemDesign.execStmt, hs1, hs2, CoreMemExec.append],
              hv2, hc2⟩
          · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hv
            obtain ⟨st2, hs2, hv2, hc2⟩ := CoreMemDesign.runEdges_V hm hnd h4 clk before after rest hrest st v' q hc hv
            exact ⟨st2, by simp [CoreMemDesign.runEdges, hf, hs2], hv2, hc2⟩
      | assign t v =>
          simp only [CoreMemDesign.edgesV] at hv
          obtain ⟨st2, hs2, hv2, hc2⟩ := CoreMemDesign.runEdges_V hm hnd h4 clk before after rest hrest st v' q hc hv
          exact ⟨st2, by simp [CoreMemDesign.runEdges, hs2], hv2, hc2⟩
      | initial _ => exact absurd hp (by simp [CoreMemDesign.ProcShape])
      | comb _ => exact absurd hp (by simp [CoreMemDesign.ProcShape])
      | implicit _ => exact absurd hp (by simp [CoreMemDesign.ProcShape])
      | unsupported _ _ => exact absurd hp (by simp [CoreMemDesign.ProcShape])

/-- **One slot of the route, on views**: the inputs applied, two settle passes (the pre-edge view), the edge pass from
the slot's start view to the pre-edge view, the commit of its updates on the view it leaves, two settle passes. -/
def CoreMemDesign.slotV (E : CoreMemDesign) (v entry : SvState) : Res SvState := do
  let p0 ← E.settleV (applyInputs2 E.scalar.toDesign2 entry v)
  let p ← E.settleV p0
  let r ← E.edgesV v p p E.processes.toList
  let s1 ← E.settleV (commitNba2 r.1 r.2)
  E.settleV s1

/-- **THE SLOT REFINEMENT**: for a design of the clocked profile, from every coherent state and every typed stimulus
entry, when the view-level slot succeeds the route's `step` succeeds, lands on exactly that view, and stays coherent. -/
theorem CoreMemDesign.step_seq {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) {st : CoreMemState}
    (hc : E.Coherent st) {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry) {v' : SvState}
    (hv : E.slotV (E.scalar.view st.scalar) entry = .ok v') :
    ∃ st', E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧ E.Coherent st' := by
  simp only [CoreMemDesign.slotV, Res.bind_eq_ok] at hv
  obtain ⟨p0, h0, p, h1, ⟨pe, q⟩, hq, s1, h2, h3⟩ := hv
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
  obtain ⟨st2, hedge, hv2, hc2⟩ := CoreMemDesign.runEdges_V hP.noMem hP.names hP.four clk
    (E.scalar.view st.scalar) (E.scalar.view st1.scalar) E.processes.toList hP.shapes st1 pe q hc1
    (by rw [hv1]; exact hq)
  -- the commit
  have hT2 : E.scalarEdge.base.Typed st2.scalar := by rw [hP.base]; exact hc2.typed
  have hTc : E.scalar.Typed (E.scalarEdge.commit st2.scalar q) := by
    have := Elab1.typed_commit (E := E.scalarEdge) q hT2
    rwa [hP.base] at this
  have hvc : E.scalar.view (E.scalarEdge.commit st2.scalar q) = commitNba2 pe q := by
    have := Elab1.view_commit (E := E.scalarEdge) (by rw [hP.base]; exact hP.four) q hT2
    rw [hP.base] at this
    rw [this, hv2]
  have hcc := E.normalizeScalar_coherent st2 hTc
  have hvcc : E.scalar.view (E.normalizeScalar st2 (E.scalarEdge.commit st2.scalar q)).scalar = commitNba2 pe q := by
    rw [E.normalizeScalar_view, hvc]
  -- the two post-edge settle passes
  obtain ⟨st3, hs3, hv3, hc3⟩ := CoreMemDesign.settleAssign_seq hP
    (st := { E.normalizeScalar st2 (E.scalarEdge.commit st2.scalar q) with memory := st2.memory })
    hcc (by rw [show E.scalar.view ({ E.normalizeScalar st2 (E.scalarEdge.commit st2.scalar q) with
      memory := st2.memory } : CoreMemState).scalar = commitNba2 pe q from hvcc]; exact h2)
  obtain ⟨st4, hs4, hv4, hc4⟩ := CoreMemDesign.settleAssign_seq hP hc3 (by rw [hv3]; exact h3)
  refine ⟨st4, ?_, hv4, hc4⟩
  simp only [CoreMemDesign.step, hs0, Res.ok_bind, hP.hasComb, Bool.false_eq_true, ↓reduceIte, hs1, hedge,
    MemState.commitNba_nil, hs3, hP.hasImplicit, hs4]

#print axioms CoreMemDesign.step_seq

/-! ## The cycle -/

/-- **One clock cycle on views**: the low slot (`clk` = 0 and the data), then the high slot (`clk` raised); the pre
sample and the post sample. -/
def CoreMemDesign.cycleV (E : CoreMemDesign) (clk : String) (v data : SvState) : Res (SvState × SvState) := do
  let pre ← E.slotV v (lowEntry clk data)
  let post ← E.slotV pre (highEntry clk)
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

/-- Each continuous assign, from index `idx` on, reads (in the expression the route evaluates, its compiled form) no
target of itself or of a LATER assign: topological source order. -/
def CoreMemDesign.topoFrom (E : CoreMemDesign) (idx : Nat) : List CoreMemProc → Bool
  | [] => true
  | p :: rest =>
      (match p with
        | .assign (.ident _) _ =>
            match E.compiledAssigns[idx]? with
            | some (some c) => c.idents.all fun x => !(assignTargets (p :: rest)).contains x
            | _ => true
        | _ => true) && E.topoFrom (idx + 1) rest

/-- The continuous assigns are in topological source order (on their compiled expressions). -/
def CoreMemDesign.topoC (E : CoreMemDesign) : Bool := E.topoFrom 0 E.processes.toList

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

/-- The edge order is irrelevant: at most one edge process, or no edge body with a blocking write. -/
def CoreMemDesign.oblEdgeOrder (E : CoreMemDesign) : Bool :=
  let edges := E.processes.toList.filter CoreMemProc.isEdge
  decide (edges.length ≤ 1) || edges.all fun p => !p.blocking

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
  edge detection only in a later slot: finding F7, a U-item);
* the edge order is irrelevant: either no edge body has a blocking write (then each body reads the pre-edge view and
  the queues commit to disjoint signals: `edgesV_perm`) or there is at most one edge process (no order to choose);
* no expression of a process holds a node ingestion kept unconverted (the route refuses it when evaluated).
Under them the route's answer is the LRM's and independent of the order the route picks (rule 4's cheap sufficient
conditions, proved below). -/
def CoreMemDesign.seqOblB (E : CoreMemDesign) (clk : String) : Bool :=
  E.oblDrivers && E.topoC && E.oblNoInputWrite clk && E.oblNoClockRead clk && E.oblReset clk && E.oblEdgeOrder &&
    E.oblConverted

/-- **The structure of a clocked family member**: it instantiates, in the clocked profile, with its obligations. -/
def SeqDesign (r : Res CoreMemDesign) (clk : String) : Prop :=
  ∃ E, r = .ok E ∧ E.SeqProfile clk ∧ E.seqOblB clk = true

/-! ## What the obligations buy: the settle is a fixpoint (§4.5, §10.3; U1 excluded)

The route closes a slot after a fixed number of source-order passes over the continuous assigns. Under the topological
obligation (`topoC`: each assign's compiled expression reads no target of itself or of a later assign) one pass already
reaches the fixpoint: a further pass changes nothing (`settleV_idem`), so no continuous assignment is out of date when
the slot closes, and the route's settled value is the LRM's. -/

/-- One settle pass changes only the targets of the assigns it runs. -/
theorem CoreMemDesign.settleRaw_frame {E : CoreMemDesign} :
    ∀ (procs : List CoreMemProc) (idx : Nat) (r r' : SvState), E.settleRaw r idx procs = .ok r' →
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

/-- **Two passes from views that agree off the remaining targets agree everywhere at the end**, when the assigns are
in topological order: each assign reads only names that are not remaining targets. -/
theorem CoreMemDesign.settleRaw_agree {E : CoreMemDesign} :
    ∀ (procs : List CoreMemProc) (idx : Nat) (r1 r2 r1' : SvState), E.topoFrom idx procs = true →
      (∀ x, x ∉ assignTargets procs → SvState.lookup r1 x = SvState.lookup r2 x) →
      E.settleRaw r1 idx procs = .ok r1' →
      ∃ r2', E.settleRaw r2 idx procs = .ok r2' ∧ ∀ x, SvState.lookup r1' x = SvState.lookup r2' x
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
              simp only [CoreMemDesign.settleRaw] at h
              cases hc : E.compiledAssigns[idx]? with
              | none => simp [hc] at h
              | some oc =>
                  cases oc with
                  | none => simp [hc] at h
                  | some c =>
                      simp only [hc, Res.bind_eq_ok] at h
                      obtain ⟨y, hy, h⟩ := h
                      simp only [hc, List.all_eq_true, Bool.not_eq_true', List.contains_eq_any_beq,
                        List.any_eq_false, beq_iff_eq] at ht
                      have hreads : ∀ x ∈ c.idents, SvState.lookup r1 x = SvState.lookup r2 x := by
                        intro x hx
                        refine hag x fun hxt => ?_
                        exact ht.1 x hx x hxt rfl
                      have hy2 : evalPure2 r2 c = .ok y := by rw [← evalPure2_congr hreads]; exact hy
                      have hag' : ∀ x, x ∉ assignTargets rest →
                          SvState.lookup (SvState.set r1 n y) x = SvState.lookup (SvState.set r2 n y) x := by
                        intro x hx
                        rw [lookup_set', lookup_set']
                        by_cases hnx : n = x
                        · simp [hnx]
                        · simp only [hnx, ↓reduceIte]
                          exact hag x (by simp [assignTargets] at hx ⊢; exact ⟨fun h' => hnx h'.symm, hx⟩)
                      obtain ⟨r2', h2, hfin⟩ := CoreMemDesign.settleRaw_agree rest (idx + 1) _ _ r1' ht.2 hag' h
                      exact ⟨r2', by simp [CoreMemDesign.settleRaw, hc, hy2, h2], hfin⟩
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

/-- **THE SETTLE IS A FIXPOINT**: under the topological obligation, from a materialized view (every view of a coherent
state is one, `matV_view`), one more settle pass after a settle pass changes nothing. So the route's slot never closes
with a continuous assignment out of date (§4.5, §10.3: the condition U1 violates), and its extra passes are idle. -/
theorem CoreMemDesign.settleV_idem {E : CoreMemDesign} (ht : E.topoC = true) {v v' : SvState} (hv : E.matV v = v)
    (h : E.settleV v = .ok v') : E.settleV v' = .ok v' := by
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
def CoreMemDesign.slot1V (E : CoreMemDesign) (v entry : SvState) : Res SvState := do
  let p ← E.settleV (applyInputs2 E.scalar.toDesign2 entry v)
  let r ← E.edgesV v p p E.processes.toList
  E.settleV (commitNba2 r.1 r.2)

/-- **The cycle under the obligations**, two `slot1V`s. -/
def CoreMemDesign.cycle1V (E : CoreMemDesign) (clk : String) (v data : SvState) : Res (SvState × SvState) := do
  let pre ← E.slot1V v (lowEntry clk data)
  let post ← E.slot1V pre (highEntry clk)
  .ok (pre, post)

/-- A settle pass's result is materialized (on distinct 4-state declarations). -/
theorem CoreMemDesign.matV_settleV {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {v v' : SvState} (h : E.settleV v = .ok v') : E.matV v' = v' := by
  simp only [CoreMemDesign.settleV, Res.bind_eq_ok, Res.ok.injEq] at h
  obtain ⟨r, -, rfl⟩ := h
  rw [← E.view_storeFromView r]
  exact CoreMemDesign.matV_view hnd h4 (E.typed_storeFromView r)

/-- The view a slot commits its edge updates on is materialized (it is the view of a typed store). -/
theorem CoreMemDesign.matV_commit_of_slot {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    {st : CoreMemState} (hc : E.Coherent st) {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry)
    {p : SvState} (hp : E.settleV (applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar)) = .ok p)
    {r : SvState × NbaQueue2} (hr : E.edgesV (E.scalar.view st.scalar) p p E.processes.toList = .ok r) :
    E.matV (commitNba2 r.1 r.2) = commitNba2 r.1 r.2 := by
  have hTin : E.scalar.Typed (E.scalar.applyInputs st.scalar entry) := hc.typed.applyInputs entry
  have hci := E.normalizeScalar_coherent { st with memory := E.applyMemoryInputs entry st.memory } hTin
  have hvi : E.scalar.view (E.normalizeScalar { st with memory := E.applyMemoryInputs entry st.memory }
      (E.scalar.applyInputs st.scalar entry)).scalar =
        applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar) := by
    rw [E.normalizeScalar_view, Elab.view_applyInputs hP.names hP.four hc.typed hty]
  obtain ⟨st0, -, hv0, hc0⟩ := CoreMemDesign.settleAssign_seq hP hci (by rw [hvi]; exact hp)
  obtain ⟨st2, -, hv2, hc2⟩ := CoreMemDesign.runEdges_V hP.noMem hP.names hP.four clk
    (E.scalar.view st.scalar) p E.processes.toList hP.shapes st0 r.1 r.2 hc0 (by rw [hv0]; exact hr)
  have hT2 : E.scalarEdge.base.Typed st2.scalar := by rw [hP.base]; exact hc2.typed
  have hTc : E.scalar.Typed (E.scalarEdge.commit st2.scalar r.2) := by
    have := Elab1.typed_commit (E := E.scalarEdge) r.2 hT2
    rwa [hP.base] at this
  have hvc : E.scalar.view (E.scalarEdge.commit st2.scalar r.2) = commitNba2 r.1 r.2 := by
    have := Elab1.view_commit (E := E.scalarEdge) (by rw [hP.base]; exact hP.four) r.2 hT2
    rw [hP.base] at this
    rw [this, hv2]
  rw [← hvc]
  exact CoreMemDesign.matV_view hP.names hP.four hTc

/-- **THE SLOT UNDER THE OBLIGATIONS**: from a coherent state's view and a typed entry, the route's slot (four settle
passes) and the one-pass slot agree. -/
theorem CoreMemDesign.slotV_eq_slot1V {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk)
    (ht : E.topoC = true) {st : CoreMemState} (hc : E.Coherent st) {entry : SvState}
    (hty : EntryTyped E.scalar.toDesign2 entry) :
    E.slotV (E.scalar.view st.scalar) entry = E.slot1V (E.scalar.view st.scalar) entry := by
  have hin : E.matV (applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar)) =
      applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar) := by
    rw [← Elab.view_applyInputs hP.names hP.four hc.typed hty]
    exact CoreMemDesign.matV_view hP.names hP.four (hc.typed.applyInputs entry)
  simp only [CoreMemDesign.slotV, CoreMemDesign.slot1V]
  cases hp : E.settleV (applyInputs2 E.scalar.toDesign2 entry (E.scalar.view st.scalar)) with
  | ok p =>
      simp only [Res.ok_bind, CoreMemDesign.settleV_idem ht hin hp]
      cases hr : E.edgesV (E.scalar.view st.scalar) p p E.processes.toList with
      | ok r =>
          simp only [Res.ok_bind]
          cases hs : E.settleV (commitNba2 r.1 r.2) with
          | ok s1 =>
              simp only [Res.ok_bind]
              exact CoreMemDesign.settleV_idem ht (CoreMemDesign.matV_commit_of_slot hP hc hty hp hr) hs
          | timeout => rfl
          | unsupported m => rfl
      | timeout => rfl
      | unsupported m => rfl
  | timeout => rfl
  | unsupported m => rfl

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

/-! ## Runs of a cycle function: the plumbing every claim needs, once

A prover states the design's cycle as a function `F v d = (pre, post)` of the current view and the cycle's data (the
cycle equations, `sv_equations`), and its claim about the samples `runF F v ins`. `SeqRuns.of_cycleFn` closes the run
judgment from the two; `runF_getElem?` and `stF_succ` index a run (cycle `c` is `F` applied to the view before it). -/

/-- The samples of the run of a cycle function `F` from the view `v` on the data list (one (pre, post) per cycle). -/
def runF (F : SvState → SvState → SvState × SvState) : SvState → List SvState → List (SvState × SvState)
  | _, [] => []
  | v, d :: ds => F v d :: runF F (F v d).2 ds

/-- The view before cycle `c` of such a run. -/
def stF (F : SvState → SvState → SvState × SvState) : SvState → List SvState → Nat → SvState
  | v, _, 0 => v
  | v, [], _ + 1 => v
  | v, d :: ds, c + 1 => stF F (F v d).2 ds c

/-- Cycle `c` of a run is `F` applied to the view before it and the cycle's data. -/
theorem runF_getElem? (F : SvState → SvState → SvState × SvState) :
    ∀ (v : SvState) (ins : List SvState) (c : Nat),
      (runF F v ins)[c]? = (ins[c]?).map fun d => F (stF F v ins c) d
  | v, [], c => by simp [runF]
  | v, d :: ds, 0 => by simp [runF, stF]
  | v, d :: ds, c + 1 => by simp [runF, stF, runF_getElem? F (F v d).2 ds c]

/-- The view before cycle `c + 1` is the post sample of cycle `c`. -/
theorem stF_succ (F : SvState → SvState → SvState × SvState) :
    ∀ (v : SvState) (ins : List SvState) (c : Nat) (d : SvState), ins[c]? = some d →
      stF F v ins (c + 1) = (F (stF F v ins c) d).2
  | v, [], c, d, h => by simp at h
  | v, d' :: ds, 0, d, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [stF]
  | v, d' :: ds, c + 1, d, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [stF]
      exact stF_succ F (F v d').2 ds c d h

/-- An invariant the cycle function keeps holds before every cycle of a run. -/
theorem stF_inv (F : SvState → SvState → SvState × SvState) (Inv : SvState → Prop) (D : SvState → Prop)
    (hstep : ∀ v d, Inv v → D d → Inv (F v d).2) :
    ∀ (v : SvState) (ins : List SvState) (c : Nat), Inv v → (∀ d ∈ ins, D d) → Inv (stF F v ins c)
  | v, [], c, hv, _ => by cases c <;> simpa [stF] using hv
  | v, d :: ds, 0, hv, _ => by simpa [stF] using hv
  | v, d :: ds, c + 1, hv, hd => by
      simp only [stF]
      exact stF_inv F Inv D hstep (F v d).2 ds c (hstep v d hv (hd d (by simp)))
        (fun d' h' => hd d' (by simp [h']))

/-- **How a `SeqRuns` claim is proved from the cycle function**: the profile, an invariant every shaped view has, the
cycle equations (`cycleV` computes `F` and `F` keeps the invariant), and the claim about the samples of `F`'s runs. -/
theorem SeqRuns.of_cycleFn {r : Res CoreMemDesign} {E : CoreMemDesign} {clk : String}
    {P : List (SvState × SvState) → Prop} (hr : r = .ok E) (hP : E.SeqProfile clk)
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) (Inv : SvState → Prop) (hinv : ∀ v, E.ShapeV v → Inv v)
    (F : SvState → SvState → SvState × SvState)
    (hstep : ∀ v d, Inv v → E.DataTyped clk d → E.cycleV clk v d = .ok (F v d) ∧ Inv (F v d).2)
    (hrun : ∀ v ins, Inv v → (∀ d ∈ ins, E.DataTyped clk d) → P (runF F v ins)) :
    SeqRuns r clk P := by
  refine SeqRuns.intro hr hP hclk Inv hinv
    (fun v d hv hd => ⟨(F v d).1, (F v d).2, (hstep v d hv hd).1, (hstep v d hv hd).2⟩) ?_
  intro v ins tr hv hd htr
  have hall : ∀ (ins : List SvState) (v : SvState), Inv v → (∀ d ∈ ins, E.DataTyped clk d) →
      E.runV clk v ins = .ok (runF F v ins) := by
    intro ins
    induction ins with
    | nil => intro v _ _; rfl
    | cons d ds ih =>
        intro v hv hd
        have h1 := hstep v d hv (hd d (by simp))
        simp [CoreMemDesign.runV, runF, h1.1, ih _ h1.2 (fun d' h' => hd d' (by simp [h']))]
  rw [hall ins v hv hd, Res.ok.injEq] at htr
  subst htr
  exact hrun v ins hv hd

#print axioms SeqRuns.of_cycleFn

/-- A typed data entry binds an input at its declared width. -/
theorem CoreMemDesign.DataTyped.width {E : CoreMemDesign} {clk : String} {d : SvState} (hd : E.DataTyped clk d)
    {n : String} (hn : n ≠ clk) (hin : n ∈ E.scalar.toDesign2.inputNames.toList) {x : LVec}
    (hx : SvState.lookup d n = some x) : E.scalar.toDesign2.declWidth n = some x.width := by
  apply hd n x hin
  have hne : (clk == n) = false := by simpa using fun h => hn h.symm
  simp [lowEntry, SvState.lookup, hne, hx]

/-! ## A cycle reads its data entry only through the values it applies -/

/-- The value a cycle's data entry `d` applies to input `n` of the view `v`: the entry's own value, else the held
one. -/
def appliedIn (d v : SvState) (n : String) : LVec :=
  (SvState.lookup d n).getD ((SvState.lookup v n).getD ⟨#[]⟩)

/-- The data inputs of a design: its input ports other than the clock. -/
def CoreMemDesign.dataInputs (E : CoreMemDesign) (clk : String) : List String :=
  E.scalar.toDesign2.inputNames.toList.filter (· != clk)

/-- The entry binding every data input to the value `d` applies to `v`. -/
def CoreMemDesign.appliedEntry (E : CoreMemDesign) (clk : String) (d v : SvState) : SvState :=
  (E.dataInputs clk).map fun n => (n, appliedIn d v n)

private theorem lookup_map_pair (f : String → LVec) : ∀ (ns : List String) (n : String), n ∈ ns →
    SvState.lookup (ns.map fun m => (m, f m)) n = some (f n)
  | [], _, h => by simp at h
  | m :: ms, n, h => by
      by_cases hmn : m = n
      · subst hmn; simp [SvState.lookup]
      · have hmn' : (m == n) = false := by simpa using hmn
        simp only [List.map_cons, SvState.lookup, hmn', Bool.false_eq_true, ↓reduceIte]
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hmn
        · exact lookup_map_pair f ms n h

private theorem lookup_some_of_key : ∀ (v : SvState) (n : String), n ∈ v.map Prod.fst →
    ∃ y, SvState.lookup v n = some y
  | [], _, h => by simp at h
  | (k, w) :: rest, n, h => by
      by_cases hk : k = n
      · exact ⟨w, by simp [SvState.lookup, hk]⟩
      · have hk' : (k == n) = false := by simpa using hk
        simp only [SvState.lookup, hk', Bool.false_eq_true, ↓reduceIte]
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hk
        · exact lookup_some_of_key rest n h

/-- **A cycle reads its data entry only through the values it applies**: from a view with every declaration
(`ShapeV`), a cycle on `d` is the cycle on the entry binding every data input to its applied value (so the cycle
equations are computed once, for an entry that binds every data input). -/
theorem CoreMemDesign.cycleV_applied {E : CoreMemDesign} {clk : String} (hP : E.SeqProfile clk) {v : SvState}
    (hv : E.ShapeV v) (d : SvState) : E.cycleV clk v d = E.cycleV clk v (E.appliedEntry clk d v) := by
  apply CoreMemDesign.cycleV_congr_data
  have h4' : ∀ dc ∈ E.scalar.toDesign2.decls.toList, dc.isInput = true → dc.twoState = false :=
    fun dc hdc _ => hP.four dc (by simpa [Elab.toDesign2] using hdc)
  have hkeys : ∀ n ∈ E.scalar.toDesign2.inputNames.toList, n ∈ v.map Prod.fst := by
    intro n hn
    rw [hv.1]
    obtain ⟨dc, hdc, -, rfl⟩ : ∃ dc ∈ E.scalar.decls.toList, dc.isInput = true ∧ dc.name = n := by
      simpa [Design2.inputNames, Elab.toDesign2] using hn
    exact List.mem_map_of_mem (f := Decl.name) hdc
  apply SvState.ext
  · rw [keys_applyInputs2 _ _ h4' hkeys, keys_applyInputs2 _ _ h4' hkeys]
  · rw [keys_applyInputs2 _ _ h4' hkeys, hv.1]; exact hP.names
  · intro n
    rw [lookup_applyInputs2 _ _ _ n h4', lookup_applyInputs2 _ _ _ n h4']
    split
    · rename_i hn
      obtain ⟨y, hy⟩ := lookup_some_of_key v n (hkeys n hn)
      by_cases hc : clk = n
      · subst hc; simp [lowEntry, SvState.lookup]
      · have hc' : (clk == n) = false := by simpa using hc
        have hmem : n ∈ E.dataInputs clk := by
          simp only [CoreMemDesign.dataInputs, List.mem_filter, bne_iff_ne, ne_eq]
          exact ⟨hn, fun h => hc h.symm⟩
        simp only [lowEntry, SvState.lookup, hc', Bool.false_eq_true, ↓reduceIte, CoreMemDesign.appliedEntry]
        rw [lookup_map_pair _ _ n hmem]
        cases hdn : SvState.lookup d n <;> simp [appliedIn, hdn, hy]
    · rfl

/-- An applied input has its declared width (the entry is typed, the held value has the width). -/
theorem CoreMemDesign.appliedIn_width {E : CoreMemDesign} {clk : String} {d : SvState} (hd : E.DataTyped clk d)
    {n : String} (hn : n ∈ E.dataInputs clk) {w : Nat} (hw : E.scalar.toDesign2.declWidth n = some w)
    {v : SvState} {x : LVec} (hx : SvState.lookup v n = some x) (hxw : x.width = w) :
    (appliedIn d v n).width = w := by
  unfold appliedIn
  cases hdn : SvState.lookup d n with
  | none => simp [hx, hxw]
  | some y =>
      simp only [CoreMemDesign.dataInputs, List.mem_filter, bne_iff_ne, ne_eq] at hn
      have := CoreMemDesign.DataTyped.width hd hn.2 hn.1 hdn
      rw [hw] at this
      simp only [Option.getD_some]
      exact (Option.some.inj this).symm










end LeanModels.Sv.Kernel
