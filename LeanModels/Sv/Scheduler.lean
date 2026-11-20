import LeanModels.Sv.Semantics

/-!
# S1: a choice-bearing event scheduler

This file is intentionally additive.  It does not redefine or call the
existing cycle `step`: the scheduler is a relation for one time slot, with a
small executable enumerator beside it.  A scheduler evaluation is one
source-shaped action at a time, so blocking writes are visible to the next
action and a wake resumes at the recorded point.  The only nondeterminism is
the choice of an active update or evaluation event.

## Clause boundary and stated narrowing

The scheduler follows IEEE 1800-2023 §4.6's determinism rule that the
simulator may choose the order of active events, while preserving the
source-order rules inside one process.  The relevant clause text is quoted
here for auditability.  §4.6 says, “The order of execution of events in the
same region is nondeterministic.”  §4.9.4 says, “The order of execution of
events in the active region is nondeterministic.”  §10.4.2 says, “The RHS of a
nonblocking assignment shall be evaluated when the nonblocking assignment is
executed.  The update of the LHS shall be performed as an update event in the
NBA region.”  Section §4.9.4 places NBA updates after the active and inactive
work.  Accordingly, every NBA scheduled by one process
receives a monotonically increasing per-process sequence number.  The
sequence relation is intentionally a superset of the standard's concrete
queue order, so theorems quantify over all admissible readings without
claiming a particular implementation order.

The scheduler follows the full §4.7 interleaving boundary.  A ready process
may be interrupted between any two source-shaped statements, so each ordinary
action leaves its continuation as a selectable Active event.  The choice of
ready active event and every such mid-process interleaving remain explicit in
`oneStep`; `allSlots` and `BoundedSteps` enumerate them under their stated
fuel bound.  Race-free designs require a separate confluence theorem before
these interleavings can be erased.
-/

namespace LeanModels.Sv.Scheduler

open LeanModels.Sv

set_option autoImplicit false

inductive EdgeWait where
  | posedge
  | negedge
  | level
  | anyChange
deriving Repr, DecidableEq, Inhabited

structure Sensitivity where
  process : Nat
  target : String
  wait : EdgeWait
  resume : Nat := 0
deriving Repr, DecidableEq, Inhabited

structure Update where
  /-- `none` is an unordered environment update; `some p` is process p. -/
  owner : Option Nat
  /-- Only nonblocking updates have a per-process sequence number. -/
  seq : Option Nat
  target : String
  value : LVec
deriving Repr, DecidableEq, Inhabited

inductive Active where
  | eval (process : Nat) (resume : Nat)
  /-- A statement selected from a branch block, with its source-order tail. -/
  | evalStmt (process : Nat) (stmt : Stmt) (tail : List Stmt) (next : Nat)
  | update (u : Update)
deriving Repr, BEq, Inhabited

structure SlotState where
  store : SvState := []
  active : List Active := []
  /-- NBA events are held in scheduling order until Active is empty. -/
  nba : List Update := []
  /-- Next per-process NBA sequence number for the current time slot. -/
  nbaNext : List (Nat × Nat) := []
  sens : List Sensitivity := []
  /-- A refusal is a terminal loud outcome, never a fabricated value. -/
  refusal : Option String := none
deriving Repr, Inhabited

inductive EvalAction where
  | blocking (target : String) (value : LVec) (next : Nat)
  | nonblocking (seq : Nat) (target : String) (value : LVec) (next : Nat)
  | blockingTail (target : String) (value : LVec) (tail : List Stmt) (next : Nat)
  | nonblockingTail (seq : Nat) (target : String) (value : LVec)
      (tail : List Stmt) (next : Nat)
  | enter (stmts : List Stmt) (tail : List Stmt) (next : Nat)
  /-- A continuous assignment emits its own Active update event and then
      re-arms its source sensitivity. -/
  | continuous (target : String) (value : LVec)
  /-- Continue at the following statement without performing a write. -/
  | continue (next : Nat)
  | continueTail (stmt : Stmt) (tail : List Stmt) (next : Nat)
  | wait (s : List Sensitivity)
  | done
  | refuse (message : String)
deriving Repr, BEq, Inhabited

structure SchedulerDesign where
  /-- One source-shaped action from a process's resume point. -/
  eval : Nat → Nat → SlotState → EvalAction
  /-- Time-zero state: declaration initializers plus all initially active processes. -/
  initial : SlotState := {}
  /-- Edge processes must install their event controls before the implicit
      time-zero activation of always_comb (§9.2.2.2). -/
  startupEdges : List Nat := []
  /-- Declared input ports and their two-state conversion bit. -/
  inputInfo : List (String × Bool) := []
  /-- Admission is explicit so refused designs cannot satisfy a property
      vacuously through an empty run relation. -/
  admitted : Bool := true
deriving Inhabited

def lookupBit (st : SvState) (name : String) : Logic := st.bit0 name

def lookupValue (st : SvState) (name : String) : LVec :=
  (SvState.lookup st name).getD (.lit "x")

def waitMet (w : EdgeWait) (old new : LVec) : Bool :=
  match w with
  | .posedge => isPosedge (old.bits[0]?.getD .lx) (new.bits[0]?.getD .lx)
  | .negedge => isNegedge (old.bits[0]?.getD .lx) (new.bits[0]?.getD .lx)
  | .level | .anyChange => old != new

def sensitivityMet (s : Sensitivity) (old new : SvState) : Bool :=
  waitMet s.wait (lookupValue old s.target) (lookupValue new s.target)

/-- Partition sleepers and wake events; a woken sensitivity is consumed. -/
def wakeSens (old new : SvState) : List Sensitivity → List Sensitivity × List Active
  | [] => ([], [])
  | s :: rest =>
      let (kept, wakes) := wakeSens old new rest
      if sensitivityMet s old new then (kept, .eval s.process s.resume :: wakes)
      else (s :: kept, wakes)

def appendWake (old new : SvState) (sens : List Sensitivity) : List Active :=
  (wakeSens old new sens).2

def removeActive : Active → List Active → List Active
  | _, [] => []
  | x, y :: ys => if x == y then ys else y :: removeActive x ys

def updateOwnerBlocked (u : Update) : List Active → Bool
  | [] => false
  | .update v :: rest =>
      (match u.owner, v.owner, u.seq, v.seq with
       | some ou, some ov, some us, some vs => ov == ou && vs < us
       | _, _, _, _ => false) || updateOwnerBlocked u rest
  | .eval _ _ :: rest => updateOwnerBlocked u rest
  | .evalStmt _ _ _ _ :: rest => updateOwnerBlocked u rest

def canConsume (u : Update) (active : List Active) : Bool :=
  !updateOwnerBlocked u active

def nbaSeq (s : SlotState) (p : Nat) : Nat :=
  (s.nbaNext.find? (fun x => x.1 == p)).map (·.2) |>.getD 0

def bumpNbaSeq (s : SlotState) (p : Nat) : SlotState :=
  let next := nbaSeq s p + 1
  let rest := s.nbaNext.filter (fun x => x.1 != p)
  { s with nbaNext := rest ++ [(p, next)] }

def activeProcesses : List Active → List Nat
  | [] => []
  | Active.eval p _ :: rest => p :: activeProcesses rest
  | Active.evalStmt p _ _ _ :: rest => p :: activeProcesses rest
  | Active.update _ :: rest => activeProcesses rest

def dropProcesses (ps : List Nat) : List Sensitivity → List Sensitivity
  | [] => []
  | x :: rest =>
      if ps.contains x.process then dropProcesses ps rest
      else x :: dropProcesses ps rest

def applyUpdate (s : SlotState) (u : Update) : SlotState :=
  let old := s.store
  let now := SvState.set old u.target u.value
  let (kept, wakes) := wakeSens old now s.sens
  let woken := wakes.foldl (fun acc a => if acc.contains a then acc else a :: acc) []
  let remaining := dropProcesses (activeProcesses woken) kept
  { s with store := now, sens := remaining, active := s.active ++ woken }

def evalAllowed (d : SchedulerDesign) (s : SlotState) (p : Nat) : Bool :=
  p ∈ d.startupEdges ||
    !(d.startupEdges.any (fun q => s.active.any (fun a => a == Active.eval q 0)))

def continuationActive (p : Nat) (tail : List Stmt) (next : Nat) : List Active :=
  match tail with
  | [] => [.eval p next]
  | stmt :: rest => [.evalStmt p stmt rest next]

def actionStep (s : SlotState) (p : Nat) : EvalAction → SlotState
  | .blocking target value next =>
      let u : Update := { owner := some p, seq := none, target, value }
      let s' := applyUpdate s u
      if s'.refusal.isSome then s' else { s' with active := s'.active ++ [.eval p next] }
  | .nonblocking _ target value next =>
      let seq := nbaSeq s p
      let u : Update := { owner := some p, seq := some seq, target, value }
      let s' := bumpNbaSeq s p
      { s' with nba := s'.nba ++ [u], active := s'.active ++ [.eval p next] }
  | .blockingTail target value tail next =>
      let u : Update := { owner := some p, seq := none, target, value }
      let s' := applyUpdate s u
      if s'.refusal.isSome then s' else
        { s' with active := s'.active ++ continuationActive p tail next }
  | .nonblockingTail _ target value tail next =>
      let seq := nbaSeq s p
      let u : Update := { owner := some p, seq := some seq, target, value }
      let s' := bumpNbaSeq s p
      { s' with nba := s'.nba ++ [u], active := s'.active ++ continuationActive p tail next }
  | .enter stmts tail next =>
      { s with active := s.active ++ continuationActive p (stmts ++ tail) next }
  | .continuous target value =>
      let u : Update := { owner := none, seq := none, target, value }
      let s' := applyUpdate s u
      if s'.refusal.isSome then s' else { s' with active := s'.active ++ [.eval p 1] }
  | .continue next => { s with active := s.active ++ [.eval p next] }
  | .continueTail stmt tail next =>
      { s with active := s.active ++ continuationActive p (stmt :: tail) next }
  | .wait ws => { s with sens := (s.sens ++ ws).eraseDups }
  | .done => s
  | .refuse message => { s with refusal := some message }

def moveNba (s : SlotState) : SlotState :=
  { s with active := s.nba.map Active.update, nba := [] }

def quietB (s : SlotState) : Bool :=
  s.active.isEmpty && s.nba.isEmpty && s.refusal.isNone

def quiet (s : SlotState) : Prop := quietB s = true

inductive Steps (r : SlotState → SlotState → Prop) : SlotState → SlotState → Prop where
  | refl (s) : Steps r s s
  | tail {s t u} : Steps r s t → r t u → Steps r s u

theorem Steps.trans {r : SlotState → SlotState → Prop} {s t u : SlotState} :
    Steps r s t → Steps r t u → Steps r s u
  | h, .refl _ => h
  | h, .tail h' hu => Steps.tail (Steps.trans h h') hu

/-! ## A loaded M0 design view -/

/-! These walkers recurse over the parser-shaped AST itself.  The old
    depth-4096 workers silently turned a real deep expression or block into
    an empty dependency set or a truncated process body.  The scheduler's
    only bounded operation is `allSlots`, whose fuel bounds event exploration
    and therefore retains the stated narrowing that a process runs to its next
    wait. -/
mutual

def exprNames : Expr → List String
  | .lit _ | .unsupported _ _ => []
  | .ident name => [name]
  | .unary _ a | .reduce _ a | .resizeSigned _ a | .squash2 a => exprNames a
  | .binary _ a b => exprNames a ++ exprNames b
  | .ternary c a b => exprNames c ++ exprNames a ++ exprNames b
  | .concat es => exprNamesList es.toList
termination_by structural e => e

def exprNamesList : List Expr → List String
  | [] => []
  | e :: es => exprNames e ++ exprNamesList es
termination_by structural es => es

def stmtNames : Stmt → List String
  | .blockingAssign _ e | .nbaAssign _ e => exprNames e
  | .ifStmt c t e => exprNames c ++ stmtNames t ++ stmtNamesOpt e
  | .block ss => stmtNamesList ss.toList
  | .unsupported _ _ => []
termination_by structural s => s

def stmtNamesOpt : Option Stmt → List String
  | none => []
  | some s => stmtNames s
termination_by structural o => o

def stmtNamesList : List Stmt → List String
  | [] => []
  | s :: ss => stmtNames s ++ stmtNamesList ss
termination_by structural ss => ss

def flattenStmt : Stmt → List Stmt
  | .block ss => flattenStmtList ss.toList
  | s => [s]
termination_by structural s => s

def flattenStmtList : List Stmt → List Stmt
  | [] => []
  | s :: ss => flattenStmt s ++ flattenStmtList ss
termination_by structural ss => ss

end

mutual

def stmtWrites : Stmt → List String
  | .blockingAssign target _ | .nbaAssign target _ => [target]
  | .ifStmt _ t e => stmtWrites t ++ stmtWritesOpt e
  | .block ss => stmtWritesList ss.toList
  | .unsupported _ _ => []
termination_by structural s => s

def stmtWritesOpt : Option Stmt → List String
  | none => []
  | some s => stmtWrites s
termination_by structural o => o

def stmtWritesList : List Stmt → List String
  | [] => []
  | s :: ss => stmtWrites s ++ stmtWritesList ss
termination_by structural ss => ss

end

def waitForProcess (p : Process) : List Sensitivity :=
  match p with
  | .alwaysFF clock _ | .alwaysPlain clock _ =>
      -- `0` is reserved for the initial registration action below; a wake
      -- resumes at program counter one, i.e. the first flattened statement.
      [{ process := 0, target := clock, wait := .posedge, resume := 1 }]
  | .alwaysComb body =>
      let writes := stmtWrites body
      ((stmtNames body).eraseDups.filter fun n => !writes.contains n).map fun n =>
        { process := 0, target := n, wait := .anyChange, resume := 0 }
  | .assign _ value => (exprNames value).eraseDups.map fun n =>
      { process := 0, target := n, wait := .anyChange, resume := 0 }
  | .unsupported _ _ => []

mutual

def evalExprStructural : Expr → SvState → Except String LVec
  | .lit v, _ => .ok v
  | .ident name, st =>
      match readSignal st name with
      | .ok v => .ok v
      | .timeout => .error "scheduler: expression evaluation timed out"
      | .unsupported msg => .error msg
  | .unary op a, st => do
      return evalUnaryOp op (← evalExprStructural a st)
  | .reduce op a, st => do
      return .ofLogic (evalRedOp op (← evalExprStructural a st))
  | .resizeSigned width operand, st => do
      return (← evalExprStructural operand st).resizeSigned width
  | .squash2 operand, st => do
      return (← evalExprStructural operand st).toTwoState
  | .binary op l r, st => do
      let a ← evalExprStructural l st
      let b ← evalExprStructural r st
      return evalBinOp op a b
  | .ternary c t f, st => do
      let cv ← evalExprStructural c st
      let tv ← evalExprStructural t st
      let fv ← evalExprStructural f st
      return LVec.ternary cv tv fv
  | .concat parts, st => do
      let vs ← evalExprStructuralList parts.toList st
      return LVec.concatMany vs.toArray
  | .unsupported svKind _, _ => .error s!"unsupported expression '{svKind}'"
termination_by structural e => e

def evalExprStructuralList : List Expr → SvState → Except String (List LVec)
  | [], _ => .ok []
  | e :: rest, st => do
      let v ← evalExprStructural e st
      let vs ← evalExprStructuralList rest st
      return v :: vs
termination_by structural es => es

end

def evalValue (s : SlotState) (e : Expr) : Except String LVec :=
  evalExprStructural e s.store

def stmtAction (s : SlotState) (p : Nat) (stmt : Stmt) (next : Nat) : EvalAction :=
  match stmt with
  | .blockingAssign target e =>
      match evalValue s e with
      | .ok v => .blocking target v next
      | .error msg => .refuse msg
  | .nbaAssign target e =>
      match evalValue s e with
      | .ok v => .nonblocking next target v next
      | .error msg => .refuse msg
  | .ifStmt cond t e =>
      match evalValue s cond with
      | .error msg => .refuse msg
      | .ok v => if v.condTrue then stmtAction s p t next else
          match e with
          | some alt => stmtAction s p alt next
          | none => .continue next
  | .block body =>
      match body.toList with
      | [] => .continue next
      | [.blockingAssign target e] =>
          match evalValue s e with
          | .ok v => .blocking target v next
          | .error msg => .refuse msg
      | [.nbaAssign target e] =>
          match evalValue s e with
          | .ok v => .nonblocking next target v next
          | .error msg => .refuse msg
      | _ => .refuse "scheduler: nested block with multiple statements"
  | .unsupported kind _ => .refuse s!"scheduler: unsupported statement '{kind}'"

/- A branch block is entered without collapsing its statements into one
   atomic action.  The tail is carried by `Active.evalStmt`, so every
   statement remains an independently selectable active event (§4.7). -/
def stmtActionTail (s : SlotState) (p : Nat) (stmt : Stmt)
    (tail : List Stmt) (next : Nat) : EvalAction :=
  match stmt with
  | .blockingAssign target e =>
      match evalValue s e with
      | .ok v => .blockingTail target v tail next
      | .error msg => .refuse msg
  | .nbaAssign target e =>
      match evalValue s e with
      | .ok v => .nonblockingTail 0 target v tail next
      | .error msg => .refuse msg
  | .ifStmt cond t e =>
      match evalValue s cond with
      | .error msg => .refuse msg
      | .ok v => if v.condTrue then .enter [t] tail next else
          match e with
          | some alt => .enter [alt] tail next
          | none => .enter [] tail next
  | .block body => .enter body.toList tail next
  | .unsupported kind _ => .refuse s!"scheduler: unsupported statement '{kind}'"
def processEval (d : Design) (p : Nat) (resume : Nat) (s : SlotState) : EvalAction :=
  match d.processes[p]? with
  | none => .done
  | some proc =>
      let edge := match proc with
        | .alwaysFF _ _ | .alwaysPlain _ _ => true
        | _ => false
      if edge && resume == 0 then
        -- Starting an edge process only installs its event control.  Its body
        -- is entered by the first matching update, never at time zero.
        .wait ((waitForProcess proc).map fun x => { x with process := p })
      else
        match proc with
        | .assign target e =>
            if resume == 0 then
              match evalValue s e with
              | .ok v => .continuous target v
              | .error msg => .refuse msg
            else
              .wait ((waitForProcess proc).map fun x => { x with process := p })
        | _ =>
            let pc := if edge then resume - 1 else resume
            let body := match proc with
              | .alwaysFF _ b | .alwaysPlain _ b | .alwaysComb b => flattenStmt b
              | .assign _ _ => []
              | .unsupported kind _ => [.unsupported kind ""]
            match body[pc]? with
            | some stmt => stmtActionTail s p stmt [] (pc + 1 + if edge then 1 else 0)
            | none => .wait ((waitForProcess proc).map fun x => { x with process := p })

def oneStep (d : SchedulerDesign) (s t : SlotState) : Prop :=
  (∃ u, Active.update u ∈ s.active ∧ canConsume u s.active ∧
    t = applyUpdate { s with active := removeActive (.update u) s.active } u) ∨
  (∃ p resume, Active.eval p resume ∈ s.active ∧
    evalAllowed d s p ∧
    t = actionStep { s with active := removeActive (.eval p resume) s.active }
      p (d.eval p resume s)) ∨
  (∃ p stmt tail next, Active.evalStmt p stmt tail next ∈ s.active ∧
    evalAllowed d s p ∧
    t = actionStep { s with active := removeActive (.evalStmt p stmt tail next) s.active }
      p (stmtActionTail s p stmt tail next)) ∨
  (s.active = [] ∧ s.nba ≠ [] ∧ t = moveNba s)

def Slot (d : SchedulerDesign) (s t : SlotState) : Prop :=
  Steps (oneStep d) s t ∧ quiet t

def inputUpdatesFrom (info : List (String × Bool)) : SvState → List Update
  | [] => []
  | (name, value) :: rest =>
      match info with
      | [] =>
          { owner := none, seq := none, target := name, value } ::
            inputUpdatesFrom [] rest
      | _ => match info.find? (fun x => x.1 == name) with
        | some (_, twoState) =>
          { owner := none, seq := none, target := name,
            value := if twoState then value.toTwoState else value } ::
            inputUpdatesFrom info rest
        | none => inputUpdatesFrom info rest

def inputUpdates (row : SvState) : List Update := inputUpdatesFrom [] row

def inputUpdatesFor (info : List (String × Bool)) (row : SvState) : List Update :=
  inputUpdatesFrom info row

def startWithInputs (d : SchedulerDesign) (s : SlotState) (row : SvState) : SlotState :=
  { s with active := (inputUpdatesFor (SchedulerDesign.inputInfo d) row).map Active.update ++ s.active, nbaNext := [] }

def Run (d : SchedulerDesign) : List SvState → SlotState → List SvState → Prop
  | [], s, [] => quiet s
  | row :: rows, s, out :: outs =>
      ∃ t, Slot d (startWithInputs d s row) t ∧ out = t.store ∧ Run d rows t outs
  | _, _, _ => False

/- A design starts with its time-zero processes active.  Settle that initial
   slot before consuming external rows, so an empty stimulus still denotes a
   completed time-zero run. -/
def RunDesign (d : SchedulerDesign) (rows : List SvState) (outs : List SvState) : Prop :=
  d.admitted = true ∧ ∃ s, Slot d d.initial s ∧ Run d rows s outs

def nextUpdates (d : SchedulerDesign) (s : SlotState) : List SlotState :=
  s.active.filterMap fun a =>
    match a with
    | .update u => if canConsume u s.active then
        some (applyUpdate { s with active := removeActive a s.active } u) else none
    | _ => none

def nextEvals (d : SchedulerDesign) (s : SlotState) : List SlotState :=
  s.active.filterMap fun a =>
    match a with
    | .eval p resume =>
        if evalAllowed d s p then
          some (actionStep { s with active := removeActive a s.active }
            p (d.eval p resume s))
        else none
    | .evalStmt p stmt tail next =>
        if evalAllowed d s p then
          some (actionStep { s with active := removeActive a s.active }
            p (stmtActionTail s p stmt tail next))
        else none
    | .update _ => none

def nextNba (s : SlotState) : List SlotState :=
  if s.active.isEmpty && !s.nba.isEmpty then [moveNba s] else []

def nextStates (d : SchedulerDesign) (s : SlotState) : List SlotState :=
  nextUpdates d s ++ nextEvals d s ++ nextNba s

def allSlots : Nat → SchedulerDesign → SlotState → List SvState
  | 0, _, s => if quietB s then [s.store] else []
  | fuel + 1, d, s =>
      if quietB s then [s.store] else (nextStates d s).flatMap (allSlots fuel d)

def allSlotStates : Nat → SchedulerDesign → SlotState → List SlotState
  | 0, _, s => if quietB s then [s] else []
  | fuel + 1, d, s =>
      if quietB s then [s] else (nextStates d s).flatMap (allSlotStates fuel d)

def SchedulerDesign.ofDesign (d : Design) : SchedulerDesign :=
  { eval := processEval d
    startupEdges := d.edgeIndices
    inputInfo := d.decls.toList.filterMap fun dc =>
      if dc.isInput then some (dc.name, dc.twoState) else none
    admitted := !d.hasUnsupported && !hasMultipleAssignDrivers d
    initial :=
      { store := initState d
        active := (List.range d.processes.size).map fun p => .eval p 0
        refusal := if hasMultipleAssignDrivers d then
          some "scheduler: multiple continuous drivers are unsupported"
        else none } }

/-! ## Enumerator soundness -/

theorem mem_nextStates_iff (d : SchedulerDesign) (s t : SlotState) :
    t ∈ nextStates d s ↔ oneStep d s t := by
  have hu : t ∈ nextUpdates d s ↔ ∃ u, Active.update u ∈ s.active ∧
      canConsume u s.active ∧ t = applyUpdate { s with active := removeActive (.update u) s.active } u := by
    unfold nextUpdates
    constructor
    · intro h
      rw [List.mem_filterMap] at h
      obtain ⟨a, ha, hm⟩ := h
      cases a with
      | update u =>
          by_cases hc : canConsume u s.active
          · simp [hc] at hm
            exact ⟨u, ha, hc, hm.symm⟩
          · simp [hc] at hm
      | eval p r => simp at hm
      | evalStmt p stmt tail next => simp at hm
    · rintro ⟨u, hu, hc, rfl⟩
      rw [List.mem_filterMap]
      exact ⟨.update u, hu, by simp [hc]⟩
  have he : t ∈ nextEvals d s ↔
      (∃ p resume, Active.eval p resume ∈ s.active ∧
        evalAllowed d s p ∧
        t = actionStep { s with active := removeActive (.eval p resume) s.active }
          p (d.eval p resume s)) ∨
      (∃ p stmt tail next, Active.evalStmt p stmt tail next ∈ s.active ∧
        evalAllowed d s p ∧
        t = actionStep { s with active := removeActive (.evalStmt p stmt tail next) s.active }
          p (stmtActionTail s p stmt tail next)) := by
    unfold nextEvals
    constructor
    · intro h
      rw [List.mem_filterMap] at h
      obtain ⟨a, ha, hm⟩ := h
      cases a with
      | update u => simp at hm
      | eval p r =>
          simp at hm
          exact Or.inl ⟨p, r, ha, by simpa using hm.1, hm.2.symm⟩
      | evalStmt p stmt tail next =>
          simp at hm
          exact Or.inr ⟨p, stmt, tail, next, ha, by simpa using hm.1, hm.2.symm⟩
    · rintro (⟨p, r, hp, ha, rfl⟩ | ⟨p, stmt, tail, next, hp, ha, rfl⟩)
      · rw [List.mem_filterMap]
        exact ⟨.eval p r, hp, by simp [ha]⟩
      · rw [List.mem_filterMap]
        exact ⟨.evalStmt p stmt tail next, hp, by simp [ha]⟩
  by_cases hn : s.active.isEmpty && !s.nba.isEmpty
  · simp only [nextStates, List.mem_append, hu, he, nextNba, hn, List.mem_cons,
      List.not_mem_nil, or_false]
    have hrel : s.active = [] ∧ s.nba ≠ [] := by simpa using hn
    simp [oneStep, hrel]
  · simp only [nextStates, List.mem_append, hu, he, nextNba, hn, List.not_mem_nil,
      false_or]
    have hrel : ¬(s.active = [] ∧ s.nba ≠ []) := by
      intro h
      apply hn
      simp [h.1, h.2]
    have hrel' : ¬(s.active = [] ∧ ¬s.nba = []) := by simpa using hrel
    have hfalse : ¬(s.active = [] ∧ ¬s.nba = [] ∧ t = moveNba s) := by
      intro h
      exact hrel' ⟨h.1, h.2.1⟩
    unfold oneStep
    simp [hfalse]

theorem allSlots_sound : ∀ (n : Nat) (d : SchedulerDesign) (s : SlotState) (v : SvState),
    v ∈ allSlots n d s → ∃ t, Slot d s t ∧ t.store = v
  | 0, d, s, v, hv => by
      by_cases hq : quietB s
      · have hv' : v = s.store := by simpa [allSlots, hq] using hv
        exact ⟨s, ⟨Steps.refl s, by simpa [quiet, hq]⟩, hv'.symm⟩
      · simp [allSlots, hq] at hv
  | n + 1, d, s, v, hv => by
      by_cases hq : quietB s
      · have hv' : v = s.store := by simpa [allSlots, hq] using hv
        exact ⟨s, ⟨Steps.refl s, by simpa [quiet, hq]⟩, hv'.symm⟩
      · rw [allSlots] at hv
        simp only [hq, ↓reduceIte] at hv
        obtain ⟨u, hu, hv⟩ := List.mem_flatMap.mp hv
        have hu' : oneStep d s u := (mem_nextStates_iff d s u).mp hu
        obtain ⟨t, ht, htv⟩ := allSlots_sound n d u v hv
        refine ⟨t, ?_, htv⟩
        exact ⟨Steps.trans (Steps.tail (Steps.refl s) hu') ht.1, ht.2⟩

/- A bounded path records the scheduler choices explicitly.  Its head
   constructor mirrors `allSlots`'s one-step expansion, while the reflexive
   constructor permits a quiet state to be observed at any remaining fuel. -/
inductive BoundedSteps (r : SlotState → SlotState → Prop) :
    Nat → SlotState → SlotState → Prop where
  | refl {n : Nat} (s : SlotState) : BoundedSteps r n s s
  | head {n : Nat} {s t u : SlotState} :
      r s t → BoundedSteps r n t u → BoundedSteps r (n + 1) s u

theorem allSlots_complete : ∀ (n : Nat) (d : SchedulerDesign) (s t : SlotState),
    BoundedSteps (oneStep d) n s t → quiet t → t.store ∈ allSlots n d s
  | 0, d, s, t, hpath, hquiet => by
      cases hpath with
      | refl =>
          have hq : quietB s = true := by simpa [quiet] using hquiet
          simp [allSlots, hq]
  | n + 1, d, s, t, hpath, hquiet => by
      cases hpath with
      | refl =>
          have hq : quietB s = true := by simpa [quiet] using hquiet
          simp [allSlots, hq]
      | @head n s u t hstep hrest =>
          by_cases hs : quietB s
          · have hs' : (s.active = [] ∧ s.nba = []) ∧ s.refusal = none := by
              simpa [quietB] using hs
            simp [oneStep, hs'.1.1, hs'.1.2] at hstep
          · have hnext : u ∈ nextStates d s :=
              (mem_nextStates_iff d s u).mpr hstep
            have htail : t.store ∈ allSlots n d u :=
              allSlots_complete n d u t hrest hquiet
            rw [allSlots]
            simp only [hs, ↓reduceIte]
            exact List.mem_flatMap.mpr ⟨u, hnext, htail⟩

/-! ## Executable audit rows -/

/- A real source-shaped race receipt.  The two processes are the ordinary
   `always @(posedge clk)` form, and the NBA values come from their AST
   statements rather than from a hand-built update list.  Icarus Verilog
   13.0 and Xcelium 24.03-s004 both admit this bench and report q=0 or q=1,
   depending on the permitted active-event order (IEEE 1800-2023 §§4.6,
   10.4.2). -/
private def raceDesign : Design :=
  { name := "scheduler_race"
    decls := #[{ name := "clk", width := 1, isInput := true },
      { name := "q", width := 8 }]
    processes := #[
      .alwaysPlain "clk" (.nbaAssign "q" (.lit (LVec.ofNat 8 0))),
      .alwaysPlain "clk" (.nbaAssign "q" (.lit (LVec.ofNat 8 1)))] }

private def raceScheduler : SchedulerDesign := SchedulerDesign.ofDesign raceDesign

private def raceSettled : List SlotState :=
  allSlotStates 8 raceScheduler raceScheduler.initial

private def raceAfterClock (s : SlotState) : List SlotState :=
  allSlotStates 8 raceScheduler
    (startWithInputs raceScheduler s [("clk", LVec.ofNat 1 1)])

private def raceStores : List SvState :=
  (raceSettled.flatMap raceAfterClock).map SlotState.store

#guard (raceStores.any (fun s => s.lookup "q" == some (LVec.ofNat 8 0)))
#guard (raceStores.any (fun s => s.lookup "q" == some (LVec.ofNat 8 1)))

private def orderedDesign : Design :=
  { name := "scheduler_ordered_nba"
    decls := #[{ name := "clk", width := 1, isInput := true },
      { name := "q", width := 1 }]
    processes := #[.alwaysPlain "clk" (.block #[
      .nbaAssign "q" (.lit (LVec.ofNat 1 0)),
      .nbaAssign "q" (.lit (LVec.ofNat 1 1))])] }

private def orderedScheduler : SchedulerDesign := SchedulerDesign.ofDesign orderedDesign

private def orderedStart : SlotState := orderedScheduler.initial

private def orderedStores : List SvState :=
  (allSlotStates 8 orderedScheduler orderedStart).flatMap fun s =>
    allSlotStates 8 orderedScheduler
      (startWithInputs orderedScheduler s [("clk", LVec.ofNat 1 1)])
      |>.map SlotState.store

#guard orderedStores.any (fun s => s.lookup "q" == some (LVec.ofNat 1 1))
#guard !orderedStores.any (fun s => s.lookup "q" == some (LVec.ofNat 1 0))

private def raceDesigns : List SchedulerDesign :=
  [raceScheduler, orderedScheduler]

#guard raceDesigns.all (fun d => d.admitted)

/-! ## A1-A5 regression guards -/

private def wakeStart : SlotState :=
  { store := [("v", LVec.ofNat 2 0)]
    sens := [{ process := 4, target := "v", wait := .level, resume := 9 }] }

private def wakeTwoStart : SlotState :=
  { store := [("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)]
    sens := [{ process := 4, target := "a", wait := .level, resume := 0 },
      { process := 4, target := "b", wait := .level, resume := 0 }] }

private def selfReadComb : Process :=
  .alwaysComb (.block #[
    .blockingAssign "a" (.ident "a"),
    .blockingAssign "y" (.ident "a")])

/- IEEE 1800-2023 §9.2.2.2.1 excludes every variable written by an
   `always_comb` procedure from its implicit sensitivity list, even when the
   variable also occurs on a right-hand side. -/
#guard waitForProcess selfReadComb == []

private def wakeOnce : SlotState :=
  applyUpdate wakeStart { owner := none, seq := none, target := "v", value := LVec.ofNat 2 1 }

#guard wakeOnce.sens == []
#guard wakeOnce.active == [.eval 4 9]
#guard (applyUpdate wakeOnce { owner := none, seq := none, target := "v", value := LVec.ofNat 2 0 }).active == [.eval 4 9]
#guard sensitivityMet { process := 0, target := "v", wait := .level } [("v", LVec.ofNat 2 0)] [("v", LVec.ofNat 2 2)]
#guard (applyUpdate wakeTwoStart
  { owner := none, seq := none, target := "a", value := LVec.ofNat 1 1 }).sens == []
#guard (applyUpdate wakeTwoStart
  { owner := none, seq := none, target := "a", value := LVec.ofNat 1 1 }).active == [.eval 4 0]

private def readAfterWrite : SchedulerDesign :=
  { eval := fun _ resume s =>
      if resume == 0 then .blocking "a" (LVec.ofNat 1 1) 1
      else if resume == 1 then .blocking "b" (lookupValue s.store "a") 2
      else .done }

private def readAfterWriteResult : List SvState :=
  allSlots 8 readAfterWrite { store := [("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)], active := [.eval 0 0] }

#guard readAfterWriteResult.any (fun s => s.lookup "b" == some (LVec.ofNat 1 1))

#guard updateOwnerBlocked
  { owner := some 0, seq := some 1, target := "q", value := LVec.ofNat 1 1 }
  [.update { owner := some 0, seq := some 0, target := "q", value := LVec.ofNat 1 0 }]
#guard !updateOwnerBlocked
  { owner := some 0, seq := some 0, target := "q", value := LVec.ofNat 1 0 }
  [.update { owner := some 0, seq := some 1, target := "q", value := LVec.ofNat 1 1 }]

private def timeZeroEdgeDesign : Design :=
  { name := "time_zero_edge"
    decls := #[
      { name := "k", width := 1, init := some (LVec.ofNat 1 0) },
      { name := "g", width := 1 },
      { name := "seen", width := 1 }]
    processes := #[
      .alwaysComb (.blockingAssign "g" (.unary .bnot (.ident "k"))),
      .alwaysPlain "g" (.nbaAssign "seen" (.lit (LVec.ofNat 1 1)))] }

#guard (allSlots 16 (SchedulerDesign.ofDesign timeZeroEdgeDesign)
  (SchedulerDesign.ofDesign timeZeroEdgeDesign).initial).all
  (fun st => st.lookup "seen" == some (LVec.ofNat 1 1))

private def ifWithoutElseContinues : SchedulerDesign :=
  { eval := fun _ resume s =>
      if resume == 0 then
        stmtAction s 0
          (.ifStmt (.lit (LVec.ofNat 1 0))
            (.blockingAssign "q" (.lit (LVec.ofNat 1 1))) none) 1
      else if resume == 1 then
        .blocking "q" (LVec.ofNat 1 0) 2
      else .done
    initial := { store := [("q", LVec.lit "x")], active := [.eval 0 0] } }

#guard (allSlots 8 ifWithoutElseContinues ifWithoutElseContinues.initial).any
  (fun st => st.lookup "q" == some (LVec.ofNat 1 0))

private def nestedIfBlock : SchedulerDesign :=
  { eval := fun _ resume s =>
      if resume == 0 then
        stmtAction s 0
          (.ifStmt (.lit (LVec.ofNat 1 1))
            (.block #[.blockingAssign "q" (.lit (LVec.ofNat 1 1))]) none) 1
      else .done
    initial := { store := [("q", LVec.ofNat 1 0)], active := [.eval 0 0] } }

#guard (allSlots 8 nestedIfBlock nestedIfBlock.initial).any
  (fun st => st.lookup "q" == some (LVec.ofNat 1 1))

/- A source-shaped begin/end in an if keeps both statements as separate
   active events.  The second write is therefore still schedulable against
   another process between the two statements. -/
private def nestedIfMultiDesign : Design :=
  { name := "nested_if_multi"
    decls := #[{ name := "q", width := 1 }, { name := "r", width := 1 }]
    processes := #[.alwaysComb
      (.ifStmt (.lit (LVec.ofNat 1 1))
        (.block #[
          .blockingAssign "q" (.lit (LVec.ofNat 1 1)),
          .blockingAssign "r" (.lit (LVec.ofNat 1 1))]) none)] }

#guard (allSlots 16 (SchedulerDesign.ofDesign nestedIfMultiDesign)
    (SchedulerDesign.ofDesign nestedIfMultiDesign).initial).any
  (fun st => st.lookup "q" == some (LVec.ofNat 1 1) &&
    st.lookup "r" == some (LVec.ofNat 1 1))

private def midBodyWait : SchedulerDesign :=
  { eval := fun _ resume s =>
      if resume == 0 then .blocking "x" (LVec.ofNat 1 1) 1
      else if resume == 1 then
        .wait [{ process := 0, target := "y", wait := .level, resume := 2 }]
      else if resume == 2 then .blocking "z" (LVec.ofNat 1 1) 3
      else .done }

private def midBodyWaitStart : SlotState :=
  { store := [("x", LVec.ofNat 1 0), ("y", LVec.ofNat 1 0), ("z", LVec.ofNat 1 0)]
    active := [.eval 0 0,
      .update { owner := none, seq := none, target := "y", value := LVec.ofNat 1 1 }]
    sens := [] }

private def midBodyWaitResult : List SvState :=
  allSlots 12 midBodyWait midBodyWaitStart

#guard midBodyWaitResult.any (fun s =>
  s.lookup "x" == some (LVec.ofNat 1 1) &&
  s.lookup "z" == some (LVec.ofNat 1 1))

/- A mid-process race: process 0 writes `x` and then reads it into `q`, while
   process 1 may write `x` between those two statements.  The two final q
   values are the legal members of the corresponding blocking race.  This
   guard specifically checks that the scheduler does not erase
   the §4.7 interruption between ordinary statements. -/
private def midProcessRace : SchedulerDesign :=
  { eval := fun p resume s =>
      if p == 0 then
        if resume == 0 then .blocking "x" (LVec.ofNat 8 1) 1
        else if resume == 1 then .blocking "q" (lookupValue s.store "x") 2
        else .done
      else if resume == 0 then .blocking "x" (LVec.ofNat 8 2) 1
      else .done
    initial :=
      { store := [("x", LVec.ofNat 8 0), ("q", LVec.ofNat 8 0)]
        active := [.eval 0 0, .eval 1 0] } }

private def midProcessRaceStores : List SvState :=
  allSlots 8 midProcessRace midProcessRace.initial

#guard midProcessRaceStores.any (fun s =>
  s.lookup "q" == some (LVec.ofNat 8 1))
#guard midProcessRaceStores.any (fun s =>
  s.lookup "q" == some (LVec.ofNat 8 2))

private def unorderedInputs : SlotState :=
  { store := [("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)]
    active := (inputUpdates [("a", LVec.ofNat 1 1), ("b", LVec.ofNat 1 1)]).map Active.update }

private def inputFirstStates : List SlotState := nextStates raceScheduler unorderedInputs

#guard inputFirstStates.any (fun s => s.store.lookup "a" == some (LVec.ofNat 1 1))
#guard inputFirstStates.any (fun s => s.store.lookup "b" == some (LVec.ofNat 1 1))

private def timeZeroDesign : Design :=
  { name := "time_zero"
    decls := #[{ name := "q", width := 1, init := some (LVec.ofNat 1 1) }]
    processes := #[.alwaysPlain "clk" (.blockingAssign "q" (.lit (LVec.ofNat 1 0)))] }

#guard (SchedulerDesign.ofDesign timeZeroDesign).initial.store == [("q", LVec.ofNat 1 1)]
#guard (SchedulerDesign.ofDesign timeZeroDesign).initial.active == [.eval 0 0]
#guard (allSlots 8 (SchedulerDesign.ofDesign timeZeroDesign)
  (SchedulerDesign.ofDesign timeZeroDesign).initial).all
  (fun st => st.lookup "q" == some (LVec.ofNat 1 1))

example : RunDesign (SchedulerDesign.ofDesign timeZeroDesign) [] [] := by
  refine ⟨by simp [SchedulerDesign.ofDesign, timeZeroDesign, Design.hasUnsupported,
    Stmt.hasUnsupported, Expr.hasUnsupported]
    <;> decide, ?_⟩
  let d := SchedulerDesign.ofDesign timeZeroDesign
  let s : SlotState :=
    { store := d.initial.store
      sens := [{ process := 0, target := "clk", wait := .posedge, resume := 1 }] }
  refine ⟨s, ?_, ?_⟩
  · constructor
    · exact Steps.tail (Steps.refl d.initial) (by
        apply Or.inr
        left
        refine ⟨0, 0, ?_, ?_, ?_⟩
        · simp [d, SchedulerDesign.ofDesign, timeZeroDesign]
        · simp [d, SchedulerDesign.ofDesign, timeZeroDesign, evalAllowed,
            Design.edgeIndices, Process.isEdgePhase]
        · simp [s, d, SchedulerDesign.ofDesign, timeZeroDesign, actionStep,
            processEval, waitForProcess, quietB, quiet, hasMultipleAssignDrivers,
            removeActive]
          refine ⟨?_, ?_, ?_⟩
          · rfl
          · rfl
          · rfl
          )
    · simp [s, quietB, quiet]
  · simp [Run, s, quietB, quiet]

private def timeZeroRun : List SvState :=
  let d := SchedulerDesign.ofDesign timeZeroDesign
  let afterLow : SlotState :=
    { store := [("q", LVec.ofNat 1 1), ("clk", LVec.lit "0")]
      sens := [{ process := 0, target := "clk", wait := .posedge, resume := 1 }] }
  allSlots 8 d (startWithInputs d afterLow [("clk", LVec.lit "1")])

#guard timeZeroRun == [[("q", LVec.ofNat 1 0), ("clk", LVec.lit "1")]]

private def inputBoundaryDesign : Design :=
  { name := "input_boundary"
    decls := #[
      { name := "in2", width := 2, isInput := true, twoState := true },
      { name := "out", width := 2, isOutput := true }]
    processes := #[] }

private def inputBoundaryScheduler := SchedulerDesign.ofDesign inputBoundaryDesign
#guard (inputBoundaryScheduler.inputInfo == [("in2", true)])
#guard (startWithInputs inputBoundaryScheduler inputBoundaryScheduler.initial
    [("in2", LVec.lit "xz"), ("out", LVec.lit "11")]).active ==
  [.update { owner := none, seq := none, target := "in2", value := LVec.lit "00" }]

private def multiAssignDesign : Design :=
  { name := "multi_assign"
    decls := #[{ name := "a", width := 1 }, { name := "y", width := 1 }]
    processes := #[
      .assign "y" (.ident "a"),
      .assign "y" (.unary .bnot (.ident "a"))] }

#guard hasMultipleAssignDrivers multiAssignDesign
#guard !(SchedulerDesign.ofDesign multiAssignDesign).admitted
#guard (processEval
  { name := "one_assign"
    decls := #[{ name := "a", width := 1 }, { name := "y", width := 1 }]
    processes := #[.assign "y" (.ident "a")] }
  0 0 { store := [("a", LVec.ofNat 1 1)] }) ==
  .continuous "y" (LVec.ofNat 1 1)

private def refusedDesign : SchedulerDesign :=
  SchedulerDesign.ofDesign
    { name := "refused"
      decls := #[]
      processes := #[.unsupported "Initial" "initial process"] }

#guard !refusedDesign.admitted
example : ¬ RunDesign refusedDesign [] [] := by
  intro h
  unfold RunDesign refusedDesign at h
  dsimp [SchedulerDesign.ofDesign] at h
  simp [Design.hasUnsupported, hasMultipleAssignDrivers] at h

/- READY FOR AUDIT S1b: A1-A7, B1-B2, and C1-C3 are implemented in this
   additive scheduler file; S2 remains outside this change. -/

end LeanModels.Sv.Scheduler
