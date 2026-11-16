import Examples.«system-verilog».mul_dadda.comb_proof
import Examples.«system-verilog».mul_dadda.arith
import LeanModels.Sv.CombTaskTactic

/-!
# The Dadda record's obligations (`Examples/system-verilog/mul_dadda`): the closer `dadda_obligation`

`sv_equations` on the record (`mul_dadda.sv`) states, besides the settled-state equations of its netlist, its
obligations: two in-range reads (`bitRead`), nine coverage goals (`cover`: every bit a read observes has a writer) and
the two input ports' knowledge (`inputsKnown`). `dadda_obligation` closes each of them (`mul_proof.lean` calls it on all
thirteen).

The coverage goals are `sv_cover`'s: the slot-window rule (`LeanModels/Sv/CombCoverUnit.lean`) solves every writer's
witnesses (the stage and column of the writer, and the one-iteration genvars of the schedule, `t`, `u`, `f`, `h`, `c`, at
their values), takes each if/else chain of writers as one case (the output column's carries, sums, kept bits and zeros
below the stage's target, with the zero slice above it; the adders' full, half and no adders, with the slice above
`u - t + 1`) and proves the writers' conditions. What the rule cannot know is the Dadda schedule's mathematics, the
player's facts (`sv_cover using dadda_cov`):

* the schedule's counts at the solved witnesses are non-negative (a writer's genvars are naturals), each proved apart by
  `sv_ite_omega` from the table's facts (`dadda_facts`);
* the bit a read names lies inside its column (`C < NP` for the read `rmN NP R C`, and every component `X < NP` of the
  writers' conditions): from the schedule's identities at the reader's stage and column (`sch_facts`: `3f + 2h ≤ N`,
  `h ≤ 1`, `c ≤ N`, `Hn - c + 2f + h ≤ N`, the height before the stage, by the identities of the column ledger,
  `arith.lean`, through the closed forms `fC_eq` … of the record's `?:` counts);
* the stage count's and `NP`'s bounds, and `2 ≤ dT X` at every table read;

and the localparams' definitions and the reader's own `?:` counts are cleared once those facts are stated: every
`omega` call of the rule reads the whole context.

Build: `lake build Examples.«system-verilog».mul_dadda.cover`.
-/

open Lean Elab Tactic Meta
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».mul_dadda.gen Examples.«system-verilog».mul_dadda.comb_proof
open Examples.«system-verilog».mul_dadda.arith

namespace Examples.«system-verilog».mul_dadda.cover

/-! ## The record's `?:` counts as the coverage goals print them, and their closed forms -/

/-- The target of stage `s`. -/
abbrev tC (S s : Int) : Int := dT (S + -1 + -s)
/-- The height bound before stage `s`. -/
abbrev uC (N : Nat) (s t : Int) : Int := if s = 0 then (N : Int) else t + t / 2
/-- `min(k, 2N - k)`. -/
abbrev mC (N : Nat) (k : Int) : Int := if k ≤ (N : Int) then k else 2 * (N : Int) + -k
/-- `min(k, 2N + 1 - k)`. -/
abbrev mC' (N : Nat) (k : Int) : Int := if k ≤ (N : Int) then k else 2 * (N : Int) + 1 + -k
/-- The full adders of column `k`. -/
abbrev fC (N : Nat) (s t u k : Int) : Int :=
  (if t < (if mC N k < u then mC N k else u) then (if mC N k < u then mC N k else u) + -t else 0) +
    -(if s = 0 then (if k = (N : Int) then 1 else 0) else 0)
/-- The half adders of column `k`. -/
abbrev hC (N : Nat) (s t u k : Int) : Int :=
  if t ≤ k then (if k < u then 1 else if s = 0 then (if k = (N : Int) then 1 else 0) else 0)
  else if s = 0 then (if k = (N : Int) then 1 else 0) else 0
/-- The carries into column `k`. -/
abbrev cC (N : Nat) (t u k : Int) : Int :=
  if t < (if mC' N k < u then mC' N k else u) then (if mC' N k < u then mC' N k else u) + -t else 0
/-- The height of column `k` after the stage. -/
abbrev HnC (N : Nat) (t k : Int) : Int :=
  if k ≤ 2 * (N : Int) + -t then (if k < t then k + 1 else t) else 2 * (N : Int) + -1 + -k

set_option hygiene false in
/-- A closed form, region by region: the stage's facts in context, the column index placed between the thresholds,
every `if` decided by `omega`, then the linear goal. -/
macro "csolve" : tactic => `(tactic| (
  have := hst.t2; have := hst.tu; have := hst.uN; have := hst.u3; have := hst.first
  rcases kregion N t u k with h | h | h | h | h | h | h <;>
    rcases Nat.eq_zero_or_pos s with h0 | h0 <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.min_eq_left, Nat.min_eq_right] <;> omega))

theorem fC_eq {N s t u k : Nat} (hst : Stg N s t u) (hk : k < 2 * N) :
    fC N s t u k = ((fF N s t u k : Nat) : Int) := by
  unfold fC mC fF mF ind; csolve

theorem hC_eq {N s t u k : Nat} (hst : Stg N s t u) (hk : k < 2 * N) :
    hC N s t u k = ((hF N s t u k : Nat) : Int) := by
  unfold hC hF ind; csolve

theorem cC_eq {N s t u k : Nat} (hst : Stg N s t u) (hk : k < 2 * N) :
    cC N t u k = ((cF N t u k : Nat) : Int) := by
  unfold cC mC' cF mF'; csolve

theorem HnC_eq {N s t u k : Nat} (hst : Stg N s t u) (hk : k < 2 * N) :
    HnC N t k = ((HnF N t k : Nat) : Int) := by
  unfold HnC HnF; csolve

/-- The height of column `k` before stage `s` is at most `N`, as an `Int`. -/
theorem HbF_le_int {N s t u : Nat} (hst : Stg N s t u) (k : Nat) : ((HbF N s u k : Nat) : Int) ≤ N := by
  have := id_Hb_le hst (k := k); omega

/-- **The schedule's facts at a reader's stage and column** (the coverage goals' form): the stage's numbers `t`, `u`
from the table and the stage count, then the column's counts `f`, `h`, `c` at their values; their signs, `3f + 2h ≤ N`
(the adders' inputs lie in the column; `h ≤ 1`), `c ≤ N` (the carries), `Hn - c + 2f + h ≤ N` (the kept bits: the
height before the stage), from the column ledger's identities through the closed forms. -/
theorem sch_facts (N : Nat) (S s t u k f h c : Int)
    (hdS : 0 ≤ S ∧ S ≤ 51 ∧ ((S = 0 ∧ (N : Int) ≤ 2) ∨
      (1 ≤ S ∧ dT (S - 1) < (N : Int) ∧ (N : Int) ≤ dT (S - 1) + dT (S - 1) / 2)))
    (ht1 : tC S s ≤ t) (ht2 : t < 1 + tC S s) (hu1 : uC N s t ≤ u) (hu2 : u < 1 + uC N s t)
    (hf1 : fC N s t u k ≤ f) (hf2 : f < 1 + fC N s t u k) (hh1 : hC N s t u k ≤ h) (hh2 : h < 1 + hC N s t u k)
    (hc1 : cC N t u k ≤ c) (hc2 : c < 1 + cC N t u k)
    (hs0 : 0 ≤ s) (hs : s < S) (hk0 : 0 ≤ k) (hk : k < 2 * (N : Int)) :
    0 ≤ f ∧ 0 ≤ h ∧ h ≤ 1 ∧ 0 ≤ c ∧ 3 * f + 2 * h ≤ (N : Int) ∧ c ≤ (N : Int) ∧
      HnC N t k - c + 2 * f + h ≤ (N : Int) ∧ 2 ≤ t ∧ t < u ∧ u ≤ (N : Int) := by
  obtain ⟨hS0, hS51, hSc⟩ := hdS
  have ht : t = dT (S + -1 + -s) := by unfold tC at ht1 ht2; omega
  have hu : u = uC N s t := by omega
  rcases hSc with ⟨hS, _⟩ | ⟨hS1, hlo, hhi⟩
  · omega
  -- the stage's numbers
  have hb := dT_bnd (S + -1 + -s) (by omega) (by omega)
  have hb1 := dT_bnd (S - 1) (by omega) (by omega)
  have hstI : 2 ≤ t ∧ t < u ∧ u ≤ (N : Int) ∧ 2 * u ≤ 3 * t ∧ (s = 0 → u = N) := by
    by_cases h0 : s = 0
    · subst h0
      have e : S + -1 + -0 = S - 1 := by omega
      rw [e] at ht
      have hu' : u = N := by rw [hu]; unfold uC; simp
      refine ⟨by omega, by omega, by omega, ?_, fun _ => hu'⟩
      rw [hu', ht]; omega
    · have hu' : u = t + t / 2 := by rw [hu]; unfold uC; simp [h0]
      have hr := dT_rec (S + -1 + -s) (by omega) (by omega)
      have hm := dT_mono (S + -1 + -s + 1) (S - 1) (by omega) (by omega) (by omega)
      refine ⟨by omega, by omega, ?_, by omega, fun h => absurd h h0⟩
      rw [hu', ht, hr]; omega
  obtain ⟨ht2', htu, huN, hu3, hfirst⟩ := hstI
  -- in `Nat`
  obtain ⟨s', rfl⟩ : ∃ s' : Nat, s = s' := ⟨s.toNat, by omega⟩
  obtain ⟨t', rfl⟩ : ∃ t' : Nat, t = t' := ⟨t.toNat, by omega⟩
  obtain ⟨u', rfl⟩ : ∃ u' : Nat, u = u' := ⟨u.toNat, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k' : Nat, k = k' := ⟨k.toNat, by omega⟩
  have hst : Stg N s' t' u' := ⟨by omega, by omega, by omega, by omega, fun h => by have := hfirst (by omega); omega⟩
  have hk' : k' < 2 * N := by omega
  rw [fC_eq hst hk'] at hf1 hf2
  rw [hC_eq hst hk'] at hh1 hh2
  rw [cC_eq hst hk'] at hc1 hc2
  rw [HnC_eq hst hk']
  have hr3 := id_reads hst hk'
  have hbl := HbF_le_int hst k'
  have hht := id_height hst hk'
  have hsl := id_slots hst hk'
  have hcm : cF N t' u' k' ≤ u' - t' := by unfold cF mF'; omega
  have hh1' := id_h_le (N := N) (s := s') (t := t') (u := u') (k := k')
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- The table is at least 2 at every index, its default arms included. -/
theorem dT_ge2 (j : Int) : 2 ≤ dT j := by
  unfold dT
  repeat' split
  all_goals omega

/-! ## The player's facts at the solved witnesses (`sv_cover using dadda_cov`) -/

/-- The conjuncts of a right-nested conjunction. -/
partial def conjs (e : Lean.Expr) : Array Lean.Expr :=
  if e.isAppOfArity ``And 2 then conjs e.appFn!.appArg! ++ conjs e.appArg! else #[e]

/-- `e` holds an `if-then-else`. -/
def hasIte (e : Lean.Expr) : Bool := (e.find? fun x => x.isAppOfArity ``ite 5).isSome

/-- `e` holds a read of the height table `dT`. -/
def hasDT (e : Lean.Expr) : Bool := (e.find? fun x => x.isAppOfArity ``dT 1).isSome

/-- Prove `ty` in the context of `g` without the rule's carriers `plans`, by `tac`, within `cap` thousand heartbeats:
the proof, or `none` (the state restored). -/
def proveApart (g : MVarId) (plans : Array FVarId) (ty : Lean.Expr) (cap : Nat) (tac : TSyntax `tactic) :
    TacticM (Option Lean.Expr) := do
  let mv ← g.withContext (mkFreshExprSyntheticOpaqueMVar ty)
  let g1 ← mv.mvarId!.tryClearMany plans
  setGoals [g1]
  let st ← saveState
  let now ← IO.getNumHeartbeats
  let ok ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := cap * 1000, initHeartbeats := now }) do
      evalTactic tac
      pure (← getGoals).isEmpty)
    (fun _ => pure false)
  if ok then return some (← instantiateMVars mv)
  st.restore
  return none

/-- The stage count's facts `hdS` (`dadda_S`) from its definition `hlp_S` (a type hint: the definition's decision
instances name the summary's `CE.eval`, which the elaborator does not unfold inside an instance argument; the kernel
checks the hint). -/
def stageFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let lctx ← getLCtx
  match lctx.findFromUserName? `hlp_S, lctx.findFromUserName? `S, lctx.findFromUserName? `N,
      lctx.findFromUserName? `h30 with
  | some hS, some S, some N, some h30 =>
    let want ← mkEq (mkApp (mkConst ``dSum) N.toExpr) S.toExpr
    let pf := mkAppN (mkConst ``dadda_S) #[N.toExpr, h30.toExpr, S.toExpr, ← mkExpectedTypeHint hS.toExpr want]
    pure (← (← g.assert `hdS (← inferType pf) pf).intro1P).2
  | _, _, _, _ => pure g

/-- `NP`'s two cases `hNPc` (`np_cases`) from its definition `hlp_NP` (a type hint, as `stageFacts`). -/
def npCases (g : MVarId) : MetaM MVarId := g.withContext do
  let lctx ← getLCtx
  match lctx.findFromUserName? `hlp_NP, lctx.findFromUserName? `NP, lctx.findFromUserName? `N with
  | some hNPd, some NPd, some Nd =>
    let f := mkAppN (mkConst ``np_cases) #[Nd.toExpr, NPd.toExpr]
    let fty ← whnf (← inferType f)
    let .forallE _ dom _ _ := fty | pure g
    let p := mkApp f (← mkExpectedTypeHint hNPd.toExpr dom)
    pure (← (← g.assert `hNPc (← inferType p) p).intro1P).2
  | _, _, _ => pure g

/-- `dadda_stage`: the stage count's facts `hdS` (`stageFacts`) and `NP`'s cases `hNPc` (`npCases`) in context. -/
elab "dadda_stage" : tactic => do replaceMainGoal [← npCases (← stageFacts (← getMainGoal))]

/-- A hypothesis of a comparison type that is `ty` up to reducible unfolding (the counts `tC` … are abbreviations), the
metavariables of `ty` assigned by it. Only comparisons are tried, unfolding abbreviations and instances only: a
hypothesis about the design (`CombEqs …`) must never be unfolded. -/
def findHyp (ty : Lean.Expr) : MetaM (Option Lean.Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 do continue
    let st ← saveState
    if ← withTransparency .instances (isDefEq t ty) then return some d.toExpr
    st.restore
  return none

/-- `sch_facts` at the reader's stage and column: its stage `s` and target `t` from `tC S s ≤ t`, then `u`, the
column `k` and the counts `f`, `h`, `c` from their bounds, each hypothesis found by `findHyp`; `none` where the reader
has no such stage (the final adder, the output). -/
def schFactsAt : MetaM (Option Lean.Expr) := do
  let lctx ← getLCtx
  let some N := lctx.findFromUserName? `N | return none
  let some S := lctx.findFromUserName? `S | return none
  let some hdS := lctx.findFromUserName? `hdS | return none
  let I := mkConst ``Int
  let (N, S, hdS) := (N.toExpr, S.toExpr, hdS.toExpr)
  let le (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``LE.le #[a, b]
  let lt (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``LT.lt #[a, b]
  let one := mkIntLit 1
  let zero := mkIntLit 0
  let s ← mkFreshExprMVar I
  let t ← mkFreshExprMVar I
  let tCe := mkApp2 (mkConst ``tC) S s
  let some ht1 ← findHyp (← le tCe t) | return none
  let s ← instantiateMVars s
  let t ← instantiateMVars t
  let u ← mkFreshExprMVar I
  let uCe := mkApp3 (mkConst ``uC) N s t
  let some hu1 ← findHyp (← le uCe u) | return none
  let u ← instantiateMVars u
  let k ← mkFreshExprMVar I
  let f ← mkFreshExprMVar I
  let some hf1 ← findHyp (← le (mkApp5 (mkConst ``fC) N s t u k) f) | return none
  let k ← instantiateMVars k
  let f ← instantiateMVars f
  let h ← mkFreshExprMVar I
  let hCe := mkApp5 (mkConst ``hC) N s t u k
  let some hh1 ← findHyp (← le hCe h) | return none
  let h ← instantiateMVars h
  let c ← mkFreshExprMVar I
  let cCe := mkApp4 (mkConst ``cC) N t u k
  let some hc1 ← findHyp (← le cCe c) | return none
  let c ← instantiateMVars c
  let fCe := mkApp5 (mkConst ``fC) N s t u k
  let some ht2 ← findHyp (← lt t (← mkAppM ``HAdd.hAdd #[one, tCe])) | return none
  let some hu2 ← findHyp (← lt u (← mkAppM ``HAdd.hAdd #[one, uCe])) | return none
  let some hf2 ← findHyp (← lt f (← mkAppM ``HAdd.hAdd #[one, fCe])) | return none
  let some hh2 ← findHyp (← lt h (← mkAppM ``HAdd.hAdd #[one, hCe])) | return none
  let some hc2 ← findHyp (← lt c (← mkAppM ``HAdd.hAdd #[one, cCe])) | return none
  let some hs0 ← findHyp (← le zero s) | return none
  let some hs ← findHyp (← lt s S) | return none
  let some hk0 ← findHyp (← le zero k) | return none
  let NI ← mkAppOptM ``Nat.cast #[I, none, N]
  let some hk ← findHyp (← lt k (← mkAppM ``HMul.hMul #[mkIntLit 2, NI])) | return none
  let pf := mkAppN (mkConst ``sch_facts) #[N, S, s, t, u, k, f, h, c, hdS, ht1, ht2, hu1, hu2, hf1, hf2, hh1,
    hh2, hc1, hc2, hs0, hs, hk0, hk]
  -- every argument has its parameter's type (the hypotheses were matched up to unfolding the abbreviations)
  try
    Meta.check pf
    return some pf
  catch _ => return none

/-- Add `ty` to `g` as `n` if `omega` proves it apart (within `cap0`), else the side tactic (within `cap1`). -/
def addApart (g : MVarId) (plans : Array FVarId) (n : Name) (ty : Lean.Expr) (cap0 cap1 : Nat)
    (side : TSyntax `tactic) : TacticM MVarId := do
  let pf? ← match ← proveApart g plans ty cap0 (← `(tactic| omega)) with
    | some p => pure (some p)
    | none => proveApart g plans ty cap1 side
  match pf? with
  | some pf => pure (← (← g.assert n ty pf).intro1P).2
  | none => pure g

/-- **The player's facts at the solved witnesses** (for `sv_cover using`; the rule's carriers `hplan` hold the writers'
conditions there):
* the stage count's facts (`dadda_S`, from its definition `hlp_S`), `NP`'s bounds `2 ≤ NP`, `N ≤ NP` (`np_cases`, without
  the disjunction), and `2 ≤ dT X` at every table read (`dT_ge2`: a stage index the solution names may lie outside the
  table at `S = 0`, where the writer is refuted, but the rule decides its components first);
* the schedule's facts at the reader's stage and column (`sch_facts`, where the reader has them: `3f + 2h ≤ N`, `c ≤ N`,
  `Hn - c + 2f + h ≤ N`, the counts' signs, `t < u ≤ N`);
* the writers' counts are non-negative (`0 ≤ E` for every lower bound `E ≤ ↑w` whose `E` holds an `if-then-else`; at
  the stage `S - 1` of the final adder's rows, which exists only where `1 ≤ S`, as `1 ≤ S → 0 ≤ E`);
* the bit the read names lies inside its column (`C < NP`, `0 ≤ C` for the read `rmN NP R C`), and so does every bit
  the writers' conditions name (`X < NP`), and every index is non-negative (`0 ≤ Y` for `↑(Y.toNat) = Y`);
each by `omega` (or, failing that, apart by `sv_ite_omega` from the table's facts, `dadda_facts`); then the localparams'
definitions `hlp_S`, `hlp_NP` and the reader's own `?:` counts (`E ≤ x`, `x < 1 + E`) are cleared: every `omega` call
of the rule reads the whole context (on cover_5, the rule's facts step 0.27M heartbeats with them, 36k without). -/
elab "dadda_cov" : tactic => do
  let g ← getMainGoal
  let side ← `(tactic| (dadda_facts; sv_ite_omega))
  let (starts, comps, plans) ← g.withContext do
    let lctx ← getLCtx
    let NP? := (lctx.findFromUserName? `NP).map (·.toExpr)
    let mut acc : Array Lean.Expr := #[]
    let mut cs : Array Lean.Expr := #[]
    let mut pls : Array FVarId := #[]
    -- the read's own bit inside its column
    let T ← instantiateMVars (← g.getType)
    if let some NP := NP? then
      if let some rd := (LeanModels.Sv.CombCoverUnit.orParts T).findSome? LeanModels.Sv.CombCoverUnit.readOf? then
        let C := rd.getArg! 2
        if (← inferType C) == mkConst ``Int then
          cs := cs.push (← mkAppM ``LE.le #[toExpr (0 : Int), C])
          cs := cs.push (← mkAppM ``LT.lt #[C, NP])
    for d in lctx do
      if d.isImplementationDetail || d.userName != `hplan then continue
      pls := pls.push d.fvarId
      let t ← instantiateMVars d.type
      let .forallE _ L _ _ := t | continue
      for c in conjs L do
        if c.hasLooseBVars then continue
        if c.isAppOfArity ``LE.le 4 then
          let E := c.getArg! 2
          if (← inferType E) == mkConst ``Int && hasIte E && !acc.contains E then acc := acc.push E
        if let some NP := NP? then
          if c.isAppOfArity ``LT.lt 4 && c.getArg! 3 == NP && !cs.contains c then cs := cs.push c
        if c.isAppOfArity ``Eq 3 && (c.getArg! 1).isAppOfArity ``Nat.cast 3 &&
            ((c.getArg! 1).getArg! 2).isAppOfArity ``Int.toNat 1 && ((c.getArg! 1).getArg! 2).appArg! == c.getArg! 2 &&
            !(c.getArg! 2).isFVar then
          let nn ← mkAppM ``LE.le #[toExpr (0 : Int), c.getArg! 2]
          unless cs.contains nn do cs := cs.push nn
    pure (acc, cs, pls)
  let mut gm := g
  -- the stage count's facts, `NP`'s bounds (from the localparams' definitions; type hints, as in `dadda_facts`)
  gm ← stageFacts gm
  gm ← gm.withContext do
    let lctx ← getLCtx
    match lctx.findFromUserName? `hlp_NP, lctx.findFromUserName? `NP, lctx.findFromUserName? `N with
    | some hNPd, some NPd, some Nd =>
      let f := mkAppN (mkConst ``np_cases) #[Nd.toExpr, NPd.toExpr]
      let fty ← whnf (← inferType f)
      if let .forallE _ dom _ _ := fty then
        let p := mkApp f (← mkExpectedTypeHint hNPd.toExpr dom)
        let NI ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, Nd.toExpr]
        let goalTy ← mkAppM ``And #[← mkAppM ``LE.le #[toExpr (2 : Int), NPd.toExpr], ← mkAppM ``LE.le #[NI, NPd.toExpr]]
        let mv ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (← inferType p) goalTy)
        let (_, g1) ← mv.mvarId!.intro1
        setGoals [g1]
        evalTactic (← `(tactic| omega))
        pure (← (← gm.assert `hNP goalTy (mkApp (← instantiateMVars mv) p)).intro1P).2
      else pure gm
    | _, _, _ => pure gm
  -- `2 ≤ dT X` at every table read of the context and the carriers
  gm ← gm.withContext do
    let mut xs : Array Lean.Expr := dtArgs (← instantiateMVars (← gm.getType)) #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do xs := dtArgs (← instantiateMVars d.type) xs
    let mut g' := gm
    for x in xs do
      let p ← mkAppM ``dT_ge2 #[x]
      g' := (← (← g'.assert `hdt (← inferType p) p).intro1P).2
    pure g'
  -- the schedule's facts at the reader's stage and column
  if let some pf ← gm.withContext schFactsAt then
    -- stated with the height `HnC` unfolded: the kept bits' arm reads the `?:` itself, and `omega` sees atoms only
    let ty ← gm.withContext do deltaExpand (← instantiateMVars (← inferType pf)) (· == ``HnC)
    gm := (← (← gm.assert `hsch ty pf).intro1P).2
  -- the stage count's bounds as plain facts (its definition's disjunction is cleared below)
  gm ← gm.withContext do
    let some hdS := (← getLCtx).findFromUserName? `hdS | pure gm
    let p0 ← mkAppM ``And.left #[hdS.toExpr]
    let p1 ← mkAppM ``And.left #[← mkAppM ``And.right #[hdS.toExpr]]
    let g1 := (← (← gm.assert `hS0 (← inferType p0) p0).intro1P).2
    g1.withContext do pure (← (← g1.assert `hS51 (← inferType p1) p1).intro1P).2
  for E in starts do
    let ty ← gm.withContext (mkAppM ``LE.le #[toExpr (0 : Int), E])
    let g1 ← addApart gm plans `hstart ty 20000 200000 side
    -- a count at the stage `S - 1` (the final adder's rows) is a count only where there is such a stage: `1 ≤ S → 0 ≤ E`
    if g1 == gm then
      let some S := (← gm.withContext getLCtx).findFromUserName? `S | continue
      let ty' ← gm.withContext do mkArrow (← mkAppM ``LE.le #[toExpr (1 : Int), S.toExpr]) ty
      gm ← addApart gm plans `hstart ty' 20000 200000 (← `(tactic| (intro; dadda_facts; sv_ite_omega)))
    else gm := g1
  for c in comps do
    gm ← addApart gm plans `hcol c 20000 400000 side
  -- the definitions and the reader's own `?:` counts, now that their facts are stated
  let ids ← gm.withContext do
    let mut acc : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || d.userName == `hplan then continue
      if d.userName == `hlp_S || d.userName == `hlp_NP || d.userName == `hdS then
        acc := acc.push d.fvarId
        continue
      let t ← instantiateMVars d.type
      if (t.isAppOfArity ``LE.le 4 && (t.getArg! 3).isFVar && hasIte (t.getArg! 2)) ||
         (t.isAppOfArity ``LT.lt 4 && (t.getArg! 2).isFVar && hasIte (t.getArg! 3)) then
        acc := acc.push d.fvarId
    pure acc
  gm ← gm.tryClearMany ids
  setGoals [gm]

/-- One obligation of `sv_equations` on the record, by its tag: a coverage goal by the slot-window rule with the
player's facts, in isolation (`sv_isolated`: memory stays flat over the nine); an input's knowledge by
`sv_known_inputs`; an in-range read by `omega`. (`omega` is never tried on a coverage goal: on its disjunction of up to
seven writers with nested existentials it ran the 8 GB scope out.) -/
elab "dadda_obligation" : tactic => do
  let tag := (← (← getMainGoal).getTag).eraseMacroScopes.toString
  if tag.startsWith "cover" then
    evalTactic (← `(tactic| quiet (sv_isolated (intros; dadda_abs; sv_cover using dadda_cov))))
  else if tag.startsWith "inputsKnown" then evalTactic (← `(tactic| sv_known_inputs))
  else evalTactic (← `(tactic| (intros; omega)))

end Examples.«system-verilog».mul_dadda.cover
