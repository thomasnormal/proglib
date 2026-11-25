import LeanModels.Sv.Kernel.CoreMemResume
import LeanModels.Sv.Kernel.XResolve

/-!
# T1: the small fuel-free source-shaped relation

The retained cursor states are the semantic state at this seam.  A relation
step chooses one active cursor and supplies a fresh per-read oracle position.
The existing cursor resume functions are used only as the executor's one-node
implementation.  The closure below has no fuel or depth parameter.

This is deliberately a small seam.  The parser-native expression rules and
the elaboration judgment are separate migration items.  A timeout from the
current implementation is exposed as `stuck` so it cannot be mistaken for a
language refusal or a completed result.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

inductive RelPhaseState where
  | comb (state : CombPhaseState)
  | edge (state : EdgePhaseState)

structure RelState where
  phase : RelPhaseState
  /-- Number of read sites already consumed by this path. -/
  readIndex : Nat := 0
  /-- Concrete values chosen by the oracle at each consumed read site. -/
  readTrace : List LVec := []

structure RelXOracle where
  read : Nat → LVec → LVec
  resolves : ∀ (index : Nat) (source : LVec), XRead source (read index source)

structure RelChoice where
  /-- The active-cursor index selected in the current phase. -/
  cursor : Nat
  /-- Source values observed by this one-node executor step, in read order. -/
  reads : List LVec := []
deriving Inhabited

inductive RelStepResult where
  | next (state : RelState)
  | refused (message : String)
  | stuck

def splitAtChoice {α : Type} : Nat → List α → Option (List α × α × List α)
  | _, [] => none
  | 0, item :: rest => some ([], item, rest)
  | n + 1, item :: rest =>
      match splitAtChoice n rest with
      | none => none
      | some (before, selected, after) => some (item :: before, selected, after)

theorem splitAtChoice_zero {α : Type} (item : α) (rest : List α) :
    splitAtChoice 0 (item :: rest) = some ([], item, rest) := by
  rfl

theorem splitAtChoice_succ {α : Type} (n : Nat) (item : α) (rest : List α) :
    splitAtChoice (n + 1) (item :: rest) =
      (splitAtChoice n rest).map (fun result =>
        (item :: result.1, result.2.1, result.2.2)) := by
  cases h : splitAtChoice n rest with
  | none => simp [splitAtChoice, h]
  | some result =>
      obtain ⟨before, selected, after⟩ := result
      simp [splitAtChoice, h]

def oracleReads (oracle : RelXOracle) (start : Nat) : List LVec → List LVec
  | [] => []
  | source :: rest => oracle.read start source :: oracleReads oracle (start + 1) rest

theorem oracleReads_resolves (oracle : RelXOracle) (start : Nat) (sources : List LVec) :
    XReadRun sources (oracleReads oracle start sources) := by
  induction sources generalizing start with
  | nil => exact .nil
  | cons source rest ih =>
      exact .cons (oracle.resolves start source) (ih (start + 1))

def relCombStep (E : CoreMemDesign) (oracle : RelXOracle)
    (s : RelState) (choice : RelChoice) : RelStepResult :=
  match s.phase with
  | .comb phase =>
      match splitAtChoice choice.cursor phase.active with
      | none => .stuck
      | some (before, cursor, after) =>
          match cursor.resume E phase.state phase.view with
          | .timeout => .stuck
          | .unsupported message => .refused message
          | .ok (next, nextView, nextCursor) =>
              .next (RelState.mk (.comb (phase.after next nextView nextCursor before after))
                (s.readIndex + choice.reads.length)
                (s.readTrace ++ oracleReads oracle s.readIndex choice.reads))
  | .edge _ => .stuck

def relEdgeStep (E : CoreMemDesign) (oracle : RelXOracle)
    (s : RelState) (choice : RelChoice) : RelStepResult :=
  match s.phase with
  | .edge phase =>
      match splitAtChoice choice.cursor phase.active with
      | none => .stuck
      | some (before, cursor, after) =>
          match cursor.resume E phase.state with
          | .timeout => .stuck
          | .unsupported message => .refused message
          | .ok (result, nextCursor) =>
              .next (RelState.mk (.edge (phase.after result nextCursor before after))
                (s.readIndex + choice.reads.length)
                (s.readTrace ++ oracleReads oracle s.readIndex choice.reads))
  | .comb _ => .stuck

def relStepOne (E : CoreMemDesign) (oracle : RelXOracle)
    (s : RelState) (choice : RelChoice) : RelStepResult :=
  match s.phase with
  | .comb _ => relCombStep E oracle s choice
  | .edge _ => relEdgeStep E oracle s choice

inductive RelStep (E : CoreMemDesign) (oracle : RelXOracle) :
    RelState → RelState → Prop where
  | comb {phase : CombPhaseState} {index : Nat} {trace : List LVec}
      {t : RelState} {choice : RelChoice} :
      relStepOne E oracle (RelState.mk (.comb phase) index trace) choice = .next t →
      XReadRun choice.reads (oracleReads oracle index choice.reads) →
      RelStep E oracle (RelState.mk (.comb phase) index trace) t
  | edge {phase : EdgePhaseState} {index : Nat} {trace : List LVec}
      {t : RelState} {choice : RelChoice} :
      relStepOne E oracle (RelState.mk (.edge phase) index trace) choice = .next t →
      XReadRun choice.reads (oracleReads oracle index choice.reads) →
      RelStep E oracle (RelState.mk (.edge phase) index trace) t

inductive RelRun (E : CoreMemDesign) (oracle : RelXOracle) :
    RelState → RelState → Prop where
  | refl (state : RelState) : RelRun E oracle state state
  | tail {start middle finish : RelState} :
      RelRun E oracle start middle → RelStep E oracle middle finish →
      RelRun E oracle start finish

theorem RelRun.trans {E : CoreMemDesign} {oracle : RelXOracle}
    {s t u : RelState} :
    RelRun E oracle s t → RelRun E oracle t u → RelRun E oracle s u
  | h, .refl _ => h
  | h, .tail h' hu => RelRun.tail (RelRun.trans h h') hu

theorem relStep_comb_zero
    {E : CoreMemDesign} {oracle : RelXOracle}
    {phase : CombPhaseState} {cursor : CombCursor}
    {next : CoreMemState × SvState × CombCursor}
    (hactive : phase.active = [cursor])
    (hresume : cursor.resume E phase.state phase.view = .ok next) :
    relStepOne E oracle
        (RelState.mk (.comb phase) 0 [])
        { cursor := 0, reads := [] } =
      .next (RelState.mk (.comb (phase.after next.1 next.2.1 next.2.2 [] [])) 0 []) := by
  simp [relStepOne, relCombStep, hactive, splitAtChoice, hresume, oracleReads]

theorem relStep_edge_zero
    {E : CoreMemDesign} {oracle : RelXOracle}
    {phase : EdgePhaseState} {cursor : EdgeCursor}
    {result : CoreMemExecResult} {next : EdgeCursor}
    (hactive : phase.active = [cursor])
    (hresume : cursor.resume E phase.state = .ok (result, next)) :
    relStepOne E oracle
        (RelState.mk (.edge phase) 0 [])
        { cursor := 0, reads := [] } =
      .next (RelState.mk (.edge (phase.after result next [] [])) 0 []) := by
  simp [relStepOne, relEdgeStep, hactive, splitAtChoice, hresume, oracleReads]

theorem relStep_reads_are_independent
    (oracle : RelXOracle) (start : Nat) (source first second : LVec)
    (hfirst : XRead source first) (hsecond : XRead source second) :
    XReadRun [source, source] [first, second] := by
  exact xReadRun_same_source hfirst hsecond

theorem relStep_oracle_reads_two
    (oracle : RelXOracle) (start : Nat) (source : LVec) :
    XReadRun [source, source]
      (oracleReads oracle start [source, source]) := by
  exact oracleReads_resolves oracle start [source, source]

end LeanModels.Sv.Kernel
