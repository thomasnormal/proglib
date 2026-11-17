import LeanModels.Sv.Semantics

/-!
# S1: a choice-bearing event scheduler

This file is intentionally additive.  It does not redefine or call the
existing cycle `step`: the scheduler is a relation for one time slot, with a
small executable enumerator beside it.  A `SchedulerDesign` supplies the
source-shaped evaluation result for each process; choosing an active item is
the explicit §4.7 choice.  NBA order is retained per process by `seq`.
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
deriving Repr, DecidableEq, Inhabited

structure Update where
  owner : Nat
  seq : Nat
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
  sens : List Sensitivity := []
deriving Repr, Inhabited

inductive EvalAction where
  | blocking (target : String) (value : LVec)
  | nonblocking (seq : Nat) (target : String) (value : LVec)
  | wait (s : List Sensitivity)
deriving Repr, DecidableEq, Inhabited

structure SchedulerDesign where
  /-- Source-shaped evaluation from a process's resume point. -/
  eval : Nat → Nat → SlotState → List EvalAction
deriving Inhabited

def lookupBit (st : SvState) (name : String) : Logic := st.bit0 name

def waitMet (w : EdgeWait) (old new : Logic) : Bool :=
  match w with
  | .posedge => isPosedge old new
  | .negedge => isNegedge old new
  | .level => old != new
  | .anyChange => old != new

def sensitivityMet (s : Sensitivity) (old new : SvState) : Bool :=
  waitMet s.wait (lookupBit old s.target) (lookupBit new s.target)

def appendWake (old new : SvState) (sens : List Sensitivity) : List Active :=
  sens.filterMap fun s =>
    if sensitivityMet s old new then some (.eval s.process 0) else none

def removeActive : Active → List Active → List Active
  | _, [] => []
  | x, y :: ys => if x == y then ys else y :: removeActive x ys

def updateOwnerBlocked (u : Update) : List Active → Bool
  | [] => false
  | .update v :: rest =>
      (v.owner == u.owner && v.seq < u.seq) || updateOwnerBlocked u rest
  | .eval _ _ :: rest => updateOwnerBlocked u rest

def canConsume (u : Update) (active : List Active) : Bool :=
  !updateOwnerBlocked u active

def applyUpdate (s : SlotState) (u : Update) : SlotState :=
  let old := s.store
  let now := SvState.set old u.target u.value
  { s with store := now, active := s.active ++ appendWake old now s.sens }

def actionStep (s : SlotState) (p : Nat) : List EvalAction → SlotState
  | [] => s
  | .blocking target value :: rest =>
      -- A blocking write is an A1 immediately, before the next statement.
      let u : Update := { owner := p, seq := 0, target, value }
      actionStep (applyUpdate s u) p rest
  | .nonblocking seq target value :: rest =>
      let u : Update := { owner := p, seq, target, value }
      actionStep { s with nba := s.nba ++ [u] } p rest
  | .wait ws :: rest =>
      actionStep { s with sens := s.sens ++ ws } p rest

def moveNba (s : SlotState) : SlotState :=
  { s with active := s.nba.map Active.update, nba := [] }

def oneStep (d : SchedulerDesign) (s t : SlotState) : Prop :=
  (∃ u, Active.update u ∈ s.active ∧ canConsume u s.active ∧
    t = applyUpdate { s with active := removeActive (.update u) s.active } u) ∨
  (∃ p resume, Active.eval p resume ∈ s.active ∧
    t = actionStep { s with active := removeActive (.eval p resume) s.active }
      p (d.eval p resume s)) ∨
  (s.active = [] ∧ s.nba ≠ [] ∧ t = moveNba s)

def quietB (s : SlotState) : Bool := s.active.isEmpty && s.nba.isEmpty

def quiet (s : SlotState) : Prop := quietB s = true

inductive Steps (r : SlotState → SlotState → Prop) : SlotState → SlotState → Prop where
  | refl (s) : Steps r s s
  | tail {s t u} : Steps r s t → r t u → Steps r s u

def Slot (d : SchedulerDesign) (s t : SlotState) : Prop :=
  Steps (oneStep d) s t ∧ quiet t

def inputUpdatesFrom : Nat → SvState → List Update
  | _, [] => []
  | i, (name, value) :: rest =>
      { owner := 0, seq := i, target := name, value } :: inputUpdatesFrom (i + 1) rest

def inputUpdates (row : SvState) : List Update := inputUpdatesFrom 0 row

def startWithInputs (s : SlotState) (row : SvState) : SlotState :=
  { s with active := (inputUpdates row).map Active.update ++ s.active }

def Run (d : SchedulerDesign) : List SvState → SlotState → List SvState → Prop
  | [], s, [] => quiet s
  | row :: rows, s, out :: outs =>
      ∃ t, Slot d (startWithInputs s row) t ∧ out = t.store ∧ Run d rows t outs
  | _, _, _ => False

def nextStates (d : SchedulerDesign) (s : SlotState) : List SlotState :=
  let updates := s.active.filterMap fun a =>
    match a with
    | .update u => if canConsume u s.active then
        some (applyUpdate { s with active := removeActive a s.active } u) else none
    | _ => none
  let evals := s.active.filterMap fun a =>
    match a with
    | .eval p resume =>
        some (actionStep { s with active := removeActive a s.active }
          p (d.eval p resume s))
    | _ => none
  let nba := if s.active.isEmpty && !s.nba.isEmpty then [moveNba s] else []
  updates ++ evals ++ nba

def allSlots : Nat → SchedulerDesign → SlotState → List SvState
  | 0, _, s => if quietB s then [s.store] else []
  | fuel + 1, d, s =>
      if quietB s then [s.store] else (nextStates d s).flatMap (allSlots fuel d)

/-! Membership rows: two update events from distinct processes are both
possible outcomes, while two updates from one process retain sequence order. -/

private def raceDesign : SchedulerDesign :=
  { eval := fun _ _ _ => [] }

private def raceStart : SlotState :=
  { store := [("q", LVec.ofNat 1 0)]
    active := [.update { owner := 1, seq := 0, target := "q", value := LVec.ofNat 1 0 },
               .update { owner := 2, seq := 0, target := "q", value := LVec.ofNat 1 1 }] }

private def raceStores : List SvState := allSlots 4 raceDesign raceStart

#guard raceStores.any (fun s => s.lookup "q" == some (LVec.ofNat 1 0))
#guard raceStores.any (fun s => s.lookup "q" == some (LVec.ofNat 1 1))

private def orderedStart : SlotState :=
  { store := [("q", LVec.ofNat 1 0)]
    active := [.update { owner := 7, seq := 0, target := "q", value := LVec.ofNat 1 0 },
               .update { owner := 7, seq := 1, target := "q", value := LVec.ofNat 1 1 }] }

private def orderedStores : List SvState := allSlots 4 raceDesign orderedStart

#guard orderedStores.any (fun s => s.lookup "q" == some (LVec.ofNat 1 1))
#guard !orderedStores.any (fun s => s.lookup "q" == some (LVec.ofNat 1 0))

/- The audit's named rows are recorded here as S1 membership labels.  Their
simulator traces are consumed by the canonical-E suite; the scheduler
enumerator's value-membership check is the next harness integration item. -/
private def auditRows : List String :=
  ["t01_nba_glitch", "t01b_default_override", "t02_blocking_pulse",
   "t03_comb_order", "t04_mem_chain", "t05_coincident_blocking",
   "t06_assign_glitch", "t07_clock_as_data", "t08_same_row_data_dfirst",
   "t08_same_row_data_cfirst", "t09_latch", "t10_reset_rows",
   "t10_reset_rows_relrace", "t10_reset_rows_t0", "t11_initial_race",
   "t11b_initial_race_swapped", "t12_derived_clock_data_det",
   "t12_derived_clock_data_race", "t13_implicit_comb",
   "t13b_comb_assign_implicit", "t14_divided_clock",
   "t15_comb_time_zero_edge", "t16_level_event_list"]

#guard auditRows.length == 23

end LeanModels.Sv.Scheduler
