import LeanModels.Sv.Kernel.CoreMemExec

/-! # Resuming a retained blocking process

A scheduler can interrupt a procedural block between statements (IEEE
1800-2023 §4.7). The work stack retains the selected branch and loop iterator.
Each step takes the current shared store and scalar view. Only the pending
work and automatic locals belong to the suspended process. This interface
executes an already active body. Event registration, choice of ready process
and NBA delivery belong to the caller.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-- Evaluating a block prefix and then its suffix preserves the result of the
original activation, including timeout and refusal. The suffix receives the
scalar view and automatic locals at the split, as well as the remaining fuel. -/
theorem CoreMemDesign.execCombStmtsFuel_append (e : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view locals : SvState)
    (fuel : Nat) (front rest : List PStmt) :
    e.execCombStmtsFuel env elems st view locals fuel (front ++ rest) =
      (do
        let (st', view', locals') ← e.execCombStmtsFuel env elems st view locals fuel front
        e.execCombStmtsFuel env elems st' view' locals' (fuel - front.length) rest) := by
  induction front generalizing st view locals fuel with
  | nil => cases fuel <;> simp [CoreMemDesign.execCombStmtsFuel] <;> rfl
  | cons stmt tail ih =>
    cases fuel with
    | zero => simp [CoreMemDesign.execCombStmtsFuel] <;> rfl
    | succ fuel =>
      cases h : e.execCombStmtFuel env elems st view locals fuel stmt with
      | timeout => simp [CoreMemDesign.execCombStmtsFuel, h] <;> rfl
      | unsupported why => simp [CoreMemDesign.execCombStmtsFuel, h] <;> rfl
      | ok result =>
        obtain ⟨next, v, l⟩ := result
        simpa [CoreMemDesign.execCombStmtsFuel, h, Nat.succ_sub_succ_eq_sub] using ih next v l fuel

/-- The pending source node and its elaboration environment. Loop iterations
share the body and bind the iterator only when that iteration starts. -/
inductive CombWork where
  | stmt (env : IEnv) (body : PStmt)
  | block (env : IEnv) (stmts : List PStmt)
  | loop (env : IEnv) (iterator : String) (body : PStmt) (values : List Int)

structure CombCursor where
  work : List CombWork
  locals : SvState := []

def CombCursor.start (env : IEnv) (body : PStmt) : CombCursor :=
  { work := [.stmt env body] }

abbrev CombResult := CoreMemState × SvState × SvState

/-- Inspect one source node, changing the store only at a leaf statement.
A branch records its selected arm before another process may run. -/
def CombWork.openNode (E : CoreMemDesign) (st : CoreMemState)
    (view locals : SvState) : CombWork → Res (CombResult × List CombWork)
  | .block _ [] | .loop _ _ _ [] => .ok ((st, view, locals), [])
  | .block env (s :: ss) => .ok ((st, view, locals), [.stmt env s, .block env ss])
  | .loop env name body (i :: rest) =>
      .ok ((st, view, locals), [.stmt (env.bindVal name i) body, .loop env name body rest])
  | .stmt env s => do
      match s with
      | .block body => return ((st, view, locals), [.block env body])
      | .ifStmt cond yes no =>
          let branch ← E.combIfBranch env E.elems st locals cond yes no
          return ((st, view, locals), branch.toList.map (.stmt env))
      | .caseStmt subj items dflt mode check =>
          let branch ← E.combCaseBranch env E.elems st locals subj items dflt mode check
          return ((st, view, locals), branch.toList.map (.stmt env))
      | .forLoop name init cond step body =>
          match forValues2 env name init cond step with
          | .ok vs => return ((st, view, locals), [.loop env name body vs])
          | .unsupported msg => .unsupported s!"ForLoopStatement: {msg}"
          | .timeout => .timeout
      | .blockingAssignL (.ident n) v =>
          return ((st, view, locals), [.stmt env (.blockingAssign n v)])
      | .blockingAssign .. | .blockingAssignL .. | .automaticDecl ..
      | .localDecl .. | .nbaAssign .. | .nbaAssignL .. | .unsupported .. =>
          let result ← E.execCombStmtFuel env E.elems st view locals 1 s
          return (result, [])

/-- Take the next step of this activation. The empty cursor has returned to
its event control. A scheduler supplies the shared state at resumption. -/
def CombCursor.resume (E : CoreMemDesign) (st : CoreMemState) (view : SvState)
    (cursor : CombCursor) : Res (CoreMemState × SvState × CombCursor) := do
  match cursor.work with
  | [] => .unsupported "9.4.2: cannot resume a waiting process"
  | head :: tail =>
      let ((next, nextView, locals), work) ← head.openNode E st view cursor.locals
      return (next, nextView, ⟨work ++ tail, locals⟩)

/-- Interpret pending work uninterrupted using the existing block executor. -/
def CombWork.run (E : CoreMemDesign) (st : CoreMemState) (view locals : SvState)
    (fuel : Nat) : CombWork → Res (CoreMemState × SvState × SvState)
  | .stmt env s => E.execCombStmtFuel env E.elems st view locals fuel s
  | .block env ss => E.execCombStmtsFuel env E.elems st view locals fuel ss
  | .loop env name body values =>
      E.execCombLoopValuesFuel env E.elems st view locals fuel values body name

/-- Finish a list of suspended tasks without interleaving. Each task receives its own depth bound. -/
def CombWork.runList (E : CoreMemDesign) (fuel : Nat) (r : CombResult) :
    List CombWork → Res CombResult
  | [] => .ok r
  | child :: children => do
      let r' ← child.run E r.1 r.2.1 r.2.2 fuel
      CombWork.runList E fuel r' children

private theorem ok_bind {α β : Type} (a : α) (f : α → Res β) :
    (Res.ok a >>= f) = f a := rfl

private theorem pure_ok {α : Type} (a : α) : (pure a : Res α) = .ok a := rfl

private theorem bind_right {α : Type} (r : Res α) : (r >>= Res.ok) = r := by
  cases r <;> rfl

private theorem run_one (E : CoreMemDesign) (fuel : Nat) (r : CombResult) (w : CombWork) :
    CombWork.runList E fuel r [w] = w.run E r.1 r.2.1 r.2.2 fuel := by
  simp only [CombWork.runList]
  cases w.run E r.1 r.2.1 r.2.2 fuel <;> rfl

private theorem finish_leaf (E : CoreMemDesign) (fuel : Nat) (r : Res CombResult) :
    r = (do
      let (next, work) ← (do let result ← r; pure (result, []))
      CombWork.runList E fuel next work) := by cases r <;> rfl

/-- Each cursor transition, followed immediately by its newly exposed work,
is exactly one unfolding of the original activation. This covers failure as
well as success at every depth and for every incoming store and local frame. -/
theorem CombWork.openNode_correct (E : CoreMemDesign) (st : CoreMemState)
    (view locals : SvState) (fuel : Nat) (w : CombWork) :
    w.run E st view locals (fuel + 1) =
      (do
        let (r, children) ← w.openNode E st view locals
        CombWork.runList E fuel r children) := by
  cases w with
  | block env ss =>
    cases ss <;> simp only [CombWork.run, CoreMemDesign.execCombStmtsFuel, openNode,
      ok_bind, CombWork.runList, bind_right]
  | loop env name body vs =>
    cases vs <;> simp only [CombWork.run, CoreMemDesign.execCombLoopValuesFuel, openNode,
      ok_bind, CombWork.runList, bind_right]
  | stmt env s =>
    cases s with
    | ifStmt cond yes no =>
      simp only [CombWork.run, CoreMemDesign.execCombStmtFuel, openNode]
      cases E.combIfBranch env E.elems st locals cond yes no with
      | timeout | unsupported => rfl
      | ok opt => cases opt <;> simp only [ok_bind, pure_ok, Option.toList, List.map,
          CombWork.runList, CombWork.run, bind_right]
    | caseStmt subj items dflt mode check =>
      simp only [CombWork.run, CoreMemDesign.execCombStmtFuel, openNode]
      cases E.combCaseBranch env E.elems st locals subj items dflt mode check with
      | timeout | unsupported => rfl
      | ok opt => cases opt <;> simp only [ok_bind, pure_ok, Option.toList, List.map,
          CombWork.runList, CombWork.run, bind_right]
    | forLoop name init cond step body =>
      simp only [CombWork.run, CoreMemDesign.execCombStmtFuel, openNode]
      cases forValues2 env name init cond step <;>
        first | rfl | simp only [ok_bind, pure_ok, run_one, CombWork.run]
    | block ss => exact (run_one E fuel (st, view, locals) (.block env ss)).symm
    | blockingAssignL target value =>
      cases target with
      | ident n => exact (run_one E fuel (st, view, locals) (.stmt env (.blockingAssign n value))).symm
      | arrayElem name indices =>
        cases indices with
        | nil => apply finish_leaf
        | cons i rest => cases rest <;> apply finish_leaf
      | _ => apply finish_leaf
    | _ => apply finish_leaf

private theorem bind_assoc_res {α β γ : Type} (r : Res α) (f : α → Res β) (g : β → Res γ) :
    ((r >>= f) >>= g) = (r >>= fun a => f a >>= g) := by cases r <;> rfl

private theorem runList_append (E : CoreMemDesign) (fuel : Nat) (r : CombResult)
    (front tail : List CombWork) :
    CombWork.runList E fuel r (front ++ tail) =
      (CombWork.runList E fuel r front >>= fun r' => CombWork.runList E fuel r' tail) := by
  induction front generalizing r with
  | nil => rfl
  | cons w ws ih => simp only [List.cons_append, CombWork.runList, bind_assoc_res, ← ih]

/-- Resuming on the same shared state and finishing immediately is equivalent
to uninterrupted execution of the pending node followed by its original tail.
In particular, the saved cursor carries every automatic local across the cut. -/
theorem CombCursor.resume_correct (E : CoreMemDesign) (st : CoreMemState)
    (view locals : SvState) (w : CombWork) (tail : List CombWork) (fuel : Nat) :
    (do
      let r ← w.run E st view locals (fuel + 1)
      CombWork.runList E fuel r tail) =
    (do
      let (next, v, cursor) ← (CombCursor.mk (w :: tail) locals).resume E st view
      CombWork.runList E fuel (next, v, cursor.locals) cursor.work) := by
  rw [CombWork.openNode_correct]
  simp only [CombCursor.resume]
  cases w.openNode E st view locals with
  | timeout | unsupported => rfl
  | ok result =>
    obtain ⟨⟨next, v, l⟩, children⟩ := result
    exact (runList_append E fuel (next, v, l) children tail).symm

#print axioms CombCursor.resume_correct

end LeanModels.Sv.Kernel

/-! ## Clocked source-shaped activations

An edge process may be selected between any two blocking statements (§4.7).
The cursor keeps the parser-native `PStmt`, its bound environment, automatic
locals, and issue-time NBA/memory queues together. The caller commits those
queues after the Active region is drained (§10.4.2).
-/

namespace LeanModels.Sv.Kernel

inductive EdgeWork where
  | edgeStmt (env : IEnv) (body : PStmt)
  | edgeBlock (env : IEnv) (stmts : List PStmt)

structure EdgeCursor where
  work : List EdgeWork
  locals : SvState := []

def EdgeCursor.start (env : IEnv) (body : PStmt) : EdgeCursor :=
  { work := [.edgeStmt env body] }

def EdgeWork.openNode (E : CoreMemDesign) (st : CoreMemState)
    (locals : SvState) : EdgeWork → Res (CoreMemExecResult × List EdgeWork)
  | EdgeWork.edgeBlock _ [] => .ok ({ state := st, scalarQ := [], memoryQ := [], locals }, [])
  | EdgeWork.edgeBlock env (stmt :: rest) =>
      .ok ({ state := st, scalarQ := [], memoryQ := [], locals },
        [EdgeWork.edgeStmt env stmt, EdgeWork.edgeBlock env rest])
  | EdgeWork.edgeStmt env (.block body) =>
      .ok ({ state := st, scalarQ := [], memoryQ := [], locals }, [EdgeWork.edgeBlock env body])
  | EdgeWork.edgeStmt env (.ifStmt cond yes no) => do
      let cv ← E.evalExprLocals env E.elems st none locals cond
      let branch := if cv.condTrue then some yes else no
      .ok ({ state := st, scalarQ := [], memoryQ := [], locals }, branch.toList.map (EdgeWork.edgeStmt env))
  | EdgeWork.edgeStmt env stmt =>
      do
        let result ← E.execStmtFuel env E.elems st locals 1 stmt
        .ok (result, [])

def EdgeCursor.resume (E : CoreMemDesign) (cursor : EdgeCursor)
    (st : CoreMemState) : Res (CoreMemExecResult × EdgeCursor) := do
  match cursor.work with
  | [] => .unsupported "10.4.2: edge process has no pending source statement"
  | head :: tail =>
      let (result, exposed) ← head.openNode E st cursor.locals
      .ok (result, { work := exposed ++ tail, locals := result.locals })

end LeanModels.Sv.Kernel
