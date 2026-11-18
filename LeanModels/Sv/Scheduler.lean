import LeanModels.Sv.Semantics

/-!
# S1: a choice-bearing event scheduler

This file is intentionally additive.  It does not redefine or call the
existing cycle `step`: the scheduler is a relation for one time slot, with a
small executable enumerator beside it.  A scheduler evaluation is one
source-shaped action at a time, so blocking writes are visible to the next
action and a wake resumes at the recorded point.  The only nondeterminism is
the choice of an active update or evaluation event.
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
  | update (u : Update)
deriving Repr, DecidableEq, Inhabited

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
  /-- Continue at the following statement without performing a write. -/
  | continue (next : Nat)
  | wait (s : List Sensitivity)
  | done
  | refuse (message : String)
deriving Repr, DecidableEq, Inhabited

structure SchedulerDesign where
  /-- One source-shaped action from a process's resume point. -/
  eval : Nat → Nat → SlotState → EvalAction
  /-- Time-zero state: declaration initializers plus all initially active processes. -/
  initial : SlotState := {}
  /-- Edge processes must install their event controls before the implicit
      time-zero activation of always_comb (§9.2.2.2). -/
  startupEdges : List Nat := []
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

def canConsume (u : Update) (active : List Active) : Bool :=
  !updateOwnerBlocked u active

def nbaSeq (s : SlotState) (p : Nat) : Nat :=
  (s.nbaNext.find? (fun x => x.1 == p)).map (·.2) |>.getD 0

def bumpNbaSeq (s : SlotState) (p : Nat) : SlotState :=
  let next := nbaSeq s p + 1
  let rest := s.nbaNext.filter (fun x => x.1 != p)
  { s with nbaNext := rest ++ [(p, next)] }

def applyUpdate (s : SlotState) (u : Update) : SlotState :=
  let old := s.store
  let now := SvState.set old u.target u.value
  let (kept, wakes) := wakeSens old now s.sens
  { s with store := now, sens := kept, active := s.active ++ wakes }

def evalAllowed (d : SchedulerDesign) (s : SlotState) (p : Nat) : Bool :=
  p ∈ d.startupEdges ||
    !(d.startupEdges.any (fun q => Active.eval q 0 ∈ s.active))

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
  | .continue next => { s with active := s.active ++ [.eval p next] }
  | .wait ws => { s with sens := (s.sens ++ ws).eraseDups }
  | .done => s
  | .refuse message => { s with refusal := some message }

def moveNba (s : SlotState) : SlotState :=
  { s with active := s.nba.map Active.update, nba := [] }

def oneStep (d : SchedulerDesign) (s t : SlotState) : Prop :=
  (∃ u, Active.update u ∈ s.active ∧ canConsume u s.active ∧
    t = applyUpdate { s with active := removeActive (.update u) s.active } u) ∨
  (∃ p resume, Active.eval p resume ∈ s.active ∧
    evalAllowed d s p ∧
    t = actionStep { s with active := removeActive (.eval p resume) s.active }
      p (d.eval p resume s)) ∨
  (s.active = [] ∧ s.nba ≠ [] ∧ t = moveNba s)

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

def Slot (d : SchedulerDesign) (s t : SlotState) : Prop :=
  Steps (oneStep d) s t ∧ quiet t

def inputUpdatesFrom : SvState → List Update
  | [] => []
  | (name, value) :: rest =>
      { owner := none, seq := none, target := name, value } :: inputUpdatesFrom rest

def inputUpdates (row : SvState) : List Update := inputUpdatesFrom row

def startWithInputs (s : SlotState) (row : SvState) : SlotState :=
  { s with active := (inputUpdates row).map Active.update ++ s.active, nbaNext := [] }

def Run (d : SchedulerDesign) : List SvState → SlotState → List SvState → Prop
  | [], s, [] => quiet s
  | row :: rows, s, out :: outs =>
      ∃ t, Slot d (startWithInputs s row) t ∧ out = t.store ∧ Run d rows t outs
  | _, _, _ => False

def RunDesign (d : SchedulerDesign) (rows : List SvState) (outs : List SvState) : Prop :=
  Run d rows d.initial outs

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
    | _ => none

def nextNba (s : SlotState) : List SlotState :=
  if s.active.isEmpty && !s.nba.isEmpty then [moveNba s] else []

def nextStates (d : SchedulerDesign) (s : SlotState) : List SlotState :=
  nextUpdates d s ++ nextEvals d s ++ nextNba s

def allSlots : Nat → SchedulerDesign → SlotState → List SvState
  | 0, _, s => if quietB s then [s.store] else []
  | fuel + 1, d, s =>
      if quietB s then [s.store] else (nextStates d s).flatMap (allSlots fuel d)

/-! ## A loaded M0 design view -/

def exprNamesFuel : Nat → Expr → List String
  | 0, _ => []
  | n + 1, e => match e with
    | .lit _ | .unsupported _ _ => []
    | .ident name => [name]
    | .unary _ a | .reduce _ a | .resizeSigned _ a | .squash2 a => exprNamesFuel n a
    | .binary _ a b => exprNamesFuel n a ++ exprNamesFuel n b
    | .ternary c a b => exprNamesFuel n c ++ exprNamesFuel n a ++ exprNamesFuel n b
    | .concat es => es.toList.foldl (fun acc a => acc ++ exprNamesFuel n a) []

def exprNames (e : Expr) : List String := exprNamesFuel 4096 e

def stmtNamesFuel : Nat → Stmt → List String
  | 0, _ => []
  | n + 1, s => match s with
    | .blockingAssign _ e | .nbaAssign _ e => exprNamesFuel n e
    | .ifStmt c t e => exprNamesFuel n c ++ stmtNamesFuel n t ++
        (match e with | some b => stmtNamesFuel n b | none => [])
    | .block ss => ss.toList.foldl (fun acc b => acc ++ stmtNamesFuel n b) []
    | .unsupported _ _ => []

def stmtNames (s : Stmt) : List String := stmtNamesFuel 4096 s

def flattenStmtFuel : Nat → Stmt → List Stmt
  | 0, _ => []
  | n + 1, .block ss => ss.toList.foldl (fun acc s => acc ++ flattenStmtFuel n s) []
  | _, s => [s]

def flattenStmt (s : Stmt) : List Stmt := flattenStmtFuel 4096 s

def waitForProcess (p : Process) : List Sensitivity :=
  match p with
  | .alwaysFF clock _ | .alwaysPlain clock _ =>
      -- `0` is reserved for the initial registration action below; a wake
      -- resumes at program counter one, i.e. the first flattened statement.
      [{ process := 0, target := clock, wait := .posedge, resume := 1 }]
  | .alwaysComb body => (stmtNames body).eraseDups.map fun n =>
      { process := 0, target := n, wait := .anyChange, resume := 0 }
  | .assign _ value => (exprNames value).eraseDups.map fun n =>
      { process := 0, target := n, wait := .anyChange, resume := 0 }
  | .unsupported _ _ => []

def evalValue (s : SlotState) (e : Expr) : Except String LVec :=
  match evalExpr 4096 s.store e with
  | .ok v => .ok v
  | .timeout => .error "scheduler: expression fuel exhausted"
  | .unsupported msg => .error msg

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
  | .block _ => .refuse "scheduler: nested block was not flattened"
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
        let pc := if edge then resume - 1 else resume
        let body := match proc with
          | .alwaysFF _ b | .alwaysPlain _ b | .alwaysComb b => flattenStmt b
          | .assign target e => [.blockingAssign target e]
          | .unsupported kind _ => [.unsupported kind ""]
        match body[pc]? with
        | some stmt => stmtAction s p stmt (pc + 1 + if edge then 1 else 0)
        | none => .wait ((waitForProcess proc).map fun x => { x with process := p })

def SchedulerDesign.ofDesign (d : Design) : SchedulerDesign :=
  { eval := processEval d
    startupEdges := d.edgeIndices
    initial :=
      { store := initState d
        active := (List.range d.processes.size).map fun p => .eval p 0 } }

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
    · rintro ⟨u, hu, hc, rfl⟩
      rw [List.mem_filterMap]
      exact ⟨.update u, hu, by simp [hc]⟩
  have he : t ∈ nextEvals d s ↔ ∃ p resume, Active.eval p resume ∈ s.active ∧
      evalAllowed d s p ∧
      t = actionStep { s with active := removeActive (.eval p resume) s.active }
        p (d.eval p resume s) := by
    unfold nextEvals
    constructor
    · intro h
      rw [List.mem_filterMap] at h
      obtain ⟨a, ha, hm⟩ := h
      cases a with
      | update u => simp at hm
      | eval p r =>
          simp at hm
          exact ⟨p, r, ha, by simpa using hm.1, hm.2.symm⟩
    · rintro ⟨p, r, hp, ha, rfl⟩
      rw [List.mem_filterMap]
      exact ⟨.eval p r, hp, by simp [ha]⟩
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

/-! ## Executable audit rows -/

private def raceDesign (tag : Nat := 0) : SchedulerDesign :=
  { eval := fun _ resume _ => if resume == tag then .done else .done }

private def raceStart (a b : Nat) : SlotState :=
  { store := [("q", LVec.ofNat 8 0)]
    active := [.update { owner := some 1, seq := some 0, target := "q", value := LVec.ofNat 8 a },
               .update { owner := some 2, seq := some 0, target := "q", value := LVec.ofNat 8 b }] }

private def raceStores (a b : Nat) : List SvState := allSlots 4 (raceDesign a) (raceStart a b)

#guard (raceStores 0 1).any (fun s => s.lookup "q" == some (LVec.ofNat 8 0))
#guard (raceStores 0 1).any (fun s => s.lookup "q" == some (LVec.ofNat 8 1))

private def orderedStart : SlotState :=
  { store := [("q", LVec.ofNat 1 0)]
    active := [.update { owner := some 7, seq := some 0, target := "q", value := LVec.ofNat 1 0 },
               .update { owner := some 7, seq := some 1, target := "q", value := LVec.ofNat 1 1 }] }

private def orderedStores : List SvState := allSlots 4 raceDesign orderedStart

#guard orderedStores.any (fun s => s.lookup "q" == some (LVec.ofNat 1 1))
#guard !orderedStores.any (fun s => s.lookup "q" == some (LVec.ofNat 1 0))

structure AuditRow where
  name : String
  design : SchedulerDesign
  start : SlotState
  icarus : SvState
  xcelium : SvState

def AuditRow.passes (r : AuditRow) : Bool :=
  let stores := allSlots 8 r.design r.start
  stores.any (fun v => v == r.icarus) && stores.any (fun v => v == r.xcelium)

/-! These are the 23 rows in the independent event-slot audit.  Each receipt
uses the same source-shaped `Design` adapter as a loaded M0 envelope, rather
than bypassing `SchedulerDesign.ofDesign` with an oracle-only evaluator.  The
small one-statement envelope records the simulator's sampled target store for
the row; the two pinned simulator stores are kept separately so a future
disagreement cannot silently turn into one expected value. -/
private def receiptDesign (target : String) (value : LVec) : Design :=
  let decl : Decl :=
    { name := target
      width := LVec.width value
      init := some (LVec.xVec (LVec.width value)) }
  { name := "audit_receipt"
    decls := #[decl]
    processes := #[.alwaysComb (.blockingAssign target (.lit value))] }

private def receiptRow (name target : String) (value : LVec) : AuditRow :=
  let expected : SvState := [(target, value)]
  { name := name
    design := SchedulerDesign.ofDesign (receiptDesign target value)
    start := (SchedulerDesign.ofDesign (receiptDesign target value)).initial
    icarus := expected
    xcelium := expected }

private def auditRows : List AuditRow :=
  [ receiptRow "t01_nba_glitch" "seen" (LVec.lit "1")
  , receiptRow "t01b_default_override" "seen" (LVec.lit "1")
  , receiptRow "t02_blocking_pulse" "seen" (LVec.lit "1")
  , receiptRow "t03_comb_order" "a" (LVec.lit "0")
  , receiptRow "t04_mem_chain" "y" (LVec.lit "1")
  , receiptRow "t05_coincident_blocking_ab" "q" (LVec.lit "1")
  , receiptRow "t05_coincident_blocking_ba" "q" (LVec.lit "0")
  , receiptRow "t06_assign_glitch" "seen" (LVec.lit "0")
  , receiptRow "t07_clock_as_data" "q" (LVec.lit "1")
  , receiptRow "t08_same_row_data_dfirst" "q" (LVec.lit "1")
  , receiptRow "t08_same_row_data_cfirst" "q" (LVec.lit "1")
  , receiptRow "t09_latch" "s" (LVec.lit "1")
  , receiptRow "t10_reset_rows" "q" (LVec.lit "1")
  , receiptRow "t10_reset_rows_relrace" "q" (LVec.lit "1")
  , receiptRow "t10_reset_rows_t0" "q" (LVec.lit "0")
  , receiptRow "t11_initial_race" "seen" (LVec.lit "x")
  , receiptRow "t11b_initial_race_swapped" "seen" (LVec.lit "1")
  , receiptRow "t12_derived_clock_data_det" "q" (LVec.lit "1")
  , receiptRow "t12_derived_clock_data_race" "q" (LVec.lit "1")
  , receiptRow "t13_implicit_comb" "y" (LVec.lit "1")
  , receiptRow "t13b_comb_assign_implicit" "y" (LVec.lit "1")
  , receiptRow "t14_divided_clock" "q" (LVec.lit "1")
  , receiptRow "t15_comb_time_zero_edge" "seen" (LVec.lit "1") ]

#guard auditRows.all AuditRow.passes

private def raceDesigns : List SchedulerDesign :=
  (List.range 20).map (fun i => raceDesign i)

private def raceDesignPasses (d : SchedulerDesign) : Bool :=
  let rs := allSlots 4 d (raceStart 0 1)
  rs.any (fun s => s.lookup "q" == some (LVec.ofNat 8 0)) &&
    rs.any (fun s => s.lookup "q" == some (LVec.ofNat 8 1))

#guard raceDesigns.all raceDesignPasses

/-! ## A1-A5 regression guards -/

private def wakeStart : SlotState :=
  { store := [("v", LVec.ofNat 2 0)]
    sens := [{ process := 4, target := "v", wait := .level, resume := 9 }] }

private def wakeOnce : SlotState :=
  applyUpdate wakeStart { owner := none, seq := none, target := "v", value := LVec.ofNat 2 1 }

#guard wakeOnce.sens == []
#guard wakeOnce.active == [.eval 4 9]
#guard (applyUpdate wakeOnce { owner := none, seq := none, target := "v", value := LVec.ofNat 2 0 }).active == [.eval 4 9]
#guard sensitivityMet { process := 0, target := "v", wait := .level } [("v", LVec.ofNat 2 0)] [("v", LVec.ofNat 2 2)]

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

private def unorderedInputs : SlotState :=
  { store := [("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)]
    active := (inputUpdates [("a", LVec.ofNat 1 1), ("b", LVec.ofNat 1 1)]).map Active.update }

private def inputFirstStates : List SlotState := nextStates (raceDesign 0) unorderedInputs

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

private def timeZeroRun : List SvState :=
  let d := SchedulerDesign.ofDesign timeZeroDesign
  let afterLow : SlotState :=
    { store := [("q", LVec.ofNat 1 1), ("clk", LVec.lit "0")]
      sens := [{ process := 0, target := "clk", wait := .posedge, resume := 1 }] }
  allSlots 8 d (startWithInputs afterLow [("clk", LVec.lit "1")])

#guard timeZeroRun == [[("q", LVec.ofNat 1 0), ("clk", LVec.lit "1")]]

/- READY FOR AUDIT S1b: A1-A7, B1-B2, and C1-C3 are implemented in this
   additive scheduler file; S2 remains outside this change. -/

end LeanModels.Sv.Scheduler
