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
          match forValues2Int32 env name init cond step with
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

/-! The retained cursor exposes the same executor result, with its waiting
tail preserved.  This is the one-leaf bridge used when a scheduler cuts a
blocking process at the statement boundary. -/
theorem CombCursor.resume_blocking_scalar_of_exec
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n : String} {value : PExpr} {width : Nat} {v : LVec}
    {tail : List CombWork}
    (hlocal : SvState.lookup locals n = none)
    (hlocals : locals = [])
    (htarget : E.scalarTarget n = some width)
    (htest : PExpr.hasTestPlusargs value = false)
    (hvalue : E.evalExprLocals env E.elems st (some width) locals value = .ok v) :
    E.execCombStmtAtView env E.elems st view (.blockingAssign n value) =
        .ok (E.setScalarState st n v, SvState.set view n v) ∧
      CombCursor.resume E st view
          { work := .stmt env (.blockingAssign n value) :: tail, locals := locals } =
        .ok (E.setScalarState st n v, SvState.set view n v,
          { work := tail, locals := locals }) := by
  constructor
  · subst locals
    simp [CoreMemDesign.execCombStmtAtView, CoreMemDesign.execCombStmtFuel,
      htarget, htest, hvalue]
  · simp [CombCursor.resume, CombWork.openNode, CoreMemDesign.execCombStmtFuel,
      hlocal, htarget, htest, hvalue]

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
      cases forValues2Int32 env name init cond step <;>
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

/-! A comb activation has the same source-shaped scheduling boundary as an
edge activation, without an NBA queue. The shared view is carried in the
state so a later cursor observes an earlier blocking write. -/

structure CombPhaseState where
  state : CoreMemState
  view : SvState
  active : List CombCursor := []

def CombPhaseState.start (state : CoreMemState) (view : SvState)
    (cursors : List CombCursor) : CombPhaseState :=
  { state, view, active := cursors }

def CombPhaseState.after (s : CombPhaseState) (next : CoreMemState)
    (nextView : SvState) (cursor : CombCursor)
    (before after : List CombCursor) : CombPhaseState :=
  { state := next
    view := nextView
    active := before ++ (if cursor.work.isEmpty then [] else [cursor]) ++ after }

inductive CombPhaseStep (E : CoreMemDesign) : CombPhaseState → CombPhaseState → Prop where
  | select {s : CombPhaseState} {before after : List CombCursor}
      {cursor next : CombCursor} {state : CoreMemState} {view : SvState}
      (hactive : s.active = before ++ cursor :: after)
      (hresume : cursor.resume E s.state s.view = .ok (state, view, next)) :
      CombPhaseStep E s (s.after state view next before after)

def CombPhaseQuiescent (s : CombPhaseState) : Prop := s.active = []

private theorem comb_exists_split_mem {α : Type} (x : α) : ∀ {xs : List α},
    x ∈ xs → ∃ before after, xs = before ++ x :: after
  | [], h => by simp at h
  | y :: ys, h => by
      by_cases hxy : x = y
      · subst y
        exact ⟨[], ys, rfl⟩
      · have htail : x ∈ ys := by simpa [hxy] using h
        obtain ⟨before, after, hsplit⟩ := comb_exists_split_mem x htail
        exact ⟨y :: before, after, by simp [hsplit]⟩

/-- Every active combinational cursor is an admissible §4.7 choice when its
    source-shaped resume succeeds.  No process order is imposed by the
    relation. -/
theorem CombPhaseStep.exists_of_mem
    {E : CoreMemDesign} {s : CombPhaseState} {cursor : CombCursor}
    (hmem : cursor ∈ s.active) {state : CoreMemState} {view : SvState}
    {next : CombCursor}
    (hresume : cursor.resume E s.state s.view = .ok (state, view, next)) :
    ∃ before after, s.active = before ++ cursor :: after ∧
      CombPhaseStep E s (s.after state view next before after) := by
  obtain ⟨before, after, hactive⟩ := comb_exists_split_mem cursor hmem
  exact ⟨before, after, hactive, .select hactive hresume⟩

theorem CombPhaseStep.active_source_order
    {E : CoreMemDesign} {s t : CombPhaseState}
    (h : CombPhaseStep E s t) :
    t.active.length ≤ s.active.length := by
  cases h with
  | select hactive hresume =>
      rw [hactive]
      simp [CombPhaseState.after]
      split <;> simp_all <;> omega

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
  /-- A parser-native procedural loop retains its iterator values so each
      iteration can be selected independently in the active region. -/
  | edgeLoop (env : IEnv) (iterator : String) (body : PStmt) (values : List Int)

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
      let cv ← E.evalExprLocals env E.elems st (some 1) locals cond
      let branch := if cv.condTrue then some yes else no
      .ok ({ state := st, scalarQ := [], memoryQ := [], locals }, branch.toList.map (EdgeWork.edgeStmt env))
  | EdgeWork.edgeStmt env (.forLoop name init cond step body) =>
      match forValues2Int32 env name init cond step with
      | .ok values =>
          .ok ({ state := st, scalarQ := [], memoryQ := [], locals },
            [.edgeLoop env name body values])
      | .unsupported msg => .unsupported s!"ForLoopStatement: {msg}"
      | .timeout => .timeout
  | EdgeWork.edgeLoop _ _ _ [] =>
      .ok ({ state := st, scalarQ := [], memoryQ := [], locals }, [])
  | EdgeWork.edgeLoop env name body (value :: rest) =>
      .ok ({ state := st, scalarQ := [], memoryQ := [], locals },
        [.edgeStmt (env.bindVal name value) body, .edgeLoop env name body rest])
  | EdgeWork.edgeStmt env stmt =>
      do
        let result ← E.execStmtFuel env E.elems st locals 4096 stmt
        .ok (result, [])

def EdgeCursor.resume (E : CoreMemDesign) (cursor : EdgeCursor)
    (st : CoreMemState) : Res (CoreMemExecResult × EdgeCursor) := do
  match cursor.work with
  | [] => .unsupported "10.4.2: edge process has no pending source statement"
  | head :: tail =>
      let (result, exposed) ← head.openNode E st cursor.locals
      .ok (result, { work := exposed ++ tail, locals := result.locals })

/-- A counted procedural-loop activation exposes one iteration and retains the
    remaining iterator values.  This source-shaped equation is the scheduler
    boundary that permits a §4.7 choice between loop iterations. -/
theorem EdgeWork.openNode_loop_cons (E : CoreMemDesign) (st : CoreMemState)
    (locals : SvState) (env : IEnv) (name : String) (body : PStmt)
    (value : Int) (rest : List Int) :
    EdgeWork.openNode E st locals (.edgeLoop env name body (value :: rest)) =
      .ok ({ state := st, scalarQ := [], memoryQ := [], locals },
        [.edgeStmt (env.bindVal name value) body,
          .edgeLoop env name body rest]) := by
  rfl

/-! ## Source-shaped active-region interleavings

The retained edge cursor is also the unit used by the event scheduler.  A
step chooses one cursor, executes exactly one parser node, and puts the
exposed continuation back into the active set.  Blocking writes are already
in `CoreMemExecResult.state`; scalar and memory NBAs are appended in issue
order and are committed only after the active set is drained.  This relation
therefore keeps the §4.7 choice explicit without selecting a source order or
lowering a `PStmt` into another AST.
-/

structure EdgePhaseState where
  state : CoreMemState
  active : List EdgeCursor := []
  scalarQ : NbaQueue2 := []
  memoryQ : MemNbaQueue := []

def EdgePhaseState.start (state : CoreMemState) (cursors : List EdgeCursor) : EdgePhaseState :=
  { state, active := cursors }

def EdgePhaseState.after (s : EdgePhaseState) (result : CoreMemExecResult)
    (cursor : EdgeCursor) (before : List EdgeCursor) (after : List EdgeCursor) : EdgePhaseState :=
  { state := result.state
    active := before ++ (if cursor.work.isEmpty then [] else [cursor]) ++ after
    scalarQ := s.scalarQ ++ result.scalarQ
    memoryQ := s.memoryQ ++ result.memoryQ }

inductive EdgePhaseStep (E : CoreMemDesign) : EdgePhaseState → EdgePhaseState → Prop where
  | select {s : EdgePhaseState} {before after : List EdgeCursor}
      {cursor next : EdgeCursor} {result : CoreMemExecResult}
      (hactive : s.active = before ++ cursor :: after)
      (hresume : cursor.resume E s.state = .ok (result, next)) :
      EdgePhaseStep E s (s.after result next before after)

def EdgePhaseQuiescent (s : EdgePhaseState) : Prop := s.active = []

private theorem exists_split_mem {α : Type} (x : α) : ∀ {xs : List α},
    x ∈ xs → ∃ before after, xs = before ++ x :: after
  | [], h => by simp at h
  | y :: ys, h => by
      by_cases hxy : x = y
      · subst y
        exact ⟨[], ys, rfl⟩
      · have htail : x ∈ ys := by simpa [hxy] using h
        obtain ⟨before, after, hsplit⟩ := exists_split_mem x htail
        exact ⟨y :: before, after, by simp [hsplit]⟩

/-- Every active cursor is an admissible §4.7 choice when its source-shaped
    resume succeeds.  The relation therefore does not silently impose a
    source order between distinct active processes. -/
theorem EdgePhaseStep.exists_of_mem
    {E : CoreMemDesign} {s : EdgePhaseState} {cursor : EdgeCursor}
    (hmem : cursor ∈ s.active) {result : CoreMemExecResult} {next : EdgeCursor}
    (hresume : cursor.resume E s.state = .ok (result, next)) :
    ∃ before after, s.active = before ++ cursor :: after ∧
      EdgePhaseStep E s (s.after result next before after) := by
  obtain ⟨before, after, hactive⟩ := exists_split_mem cursor hmem
  exact ⟨before, after, hactive, .select hactive hresume⟩

/-- A phase step appends issue-time NBA records to the existing queues.  This
    prefix equation is the order-preservation fact used when a later proof
    commits the queues after the active region is drained. -/
theorem EdgePhaseStep.queue_prefix
    {E : CoreMemDesign} {s t : EdgePhaseState}
    (h : EdgePhaseStep E s t) :
    ∃ result : CoreMemExecResult, t.scalarQ = s.scalarQ ++ result.scalarQ ∧
      t.memoryQ = s.memoryQ ++ result.memoryQ := by
  cases h with
  | select hactive hresume =>
      exact ⟨_, rfl, rfl⟩

def EdgePhaseState.commit (E : CoreMemDesign) (s : EdgePhaseState) : Res CoreMemState := do
  let scalar := E.scalarEdge.commit s.state.scalar s.scalarQ
  let memory ← match s.state.memory.commitNba s.memoryQ with
    | some memory => .ok memory
    | none => .unsupported "10.4.2: memory NBA commit lost its declaration identity"
  .ok (E.normalizeScalar { s.state with scalar, memory } scalar)

theorem EdgePhaseStep.active_source_order
    {E : CoreMemDesign} {s t : EdgePhaseState}
    (h : EdgePhaseStep E s t) :
    t.active.length ≤ s.active.length := by
  cases h with
  | select hactive hresume =>
      rw [hactive]
      simp [EdgePhaseState.after]
      split <;> simp_all <;> omega

/-! The active-region relation has an explicit progress premise.  Once every
active cursor can resume, any nonempty active list admits a legal next step.
The selected cursor is obtained by the relation's source-shaped list split, so
this theorem does not impose source order. -/
theorem EdgePhaseStep.progress
    {E : CoreMemDesign} {s : EdgePhaseState} (hn : s.active ≠ [])
    (hresume : ∀ cursor, cursor ∈ s.active →
      ∃ result next, cursor.resume E s.state = .ok (result, next)) :
    ∃ t, EdgePhaseStep E s t := by
  cases hs : s.active with
  | nil => exact False.elim (hn hs)
  | cons cursor rest =>
      obtain ⟨result, next, hnext⟩ := hresume cursor (by simp [hs])
      exact ⟨s.after result next [] rest, .select (by simp [hs]) hnext⟩

end LeanModels.Sv.Kernel
