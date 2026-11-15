import Lean
import LeanModels.Sv.CombTask
import LeanModels.Sv.CombEqTactic

/-!
# The plumbing of a combinational task proof: lemmas and tactic steps (comb lane, tac6)

A task proof (`Examples/system-verilog/prefix_ks/add_proof.lean`) runs `sv_structure`, `sv_interface` and
`sv_equations`, then does mathematics; what it wrote by hand around them is here:

* the statement shape, `CombTask.of_comb` (CombTask.lean): the ports, the generic conjuncts and the stimulus form from
  `CombDesign`, `Acyclic` and the ports;
* `sv_inputs`: the stimulus-to-snapshot step. Each hypothesis `h : SvState.lookup inputs n = some v` of an input port
  becomes `h : SvState.lookup st n = some v` (through the transfer hypothesis `hin` of `CombTask.of_comb`), a one-bit
  port's `x : BitVec 1` becomes the `Bool` it holds (`x = BitVec.ofBool b`, `b` named `x`), and each port's bits are
  stated as the equations read them: `bit_<n> : ∀ i, i < w → st.boolAt n i = x.getLsbD i`, or `st.boolAt n 0 = b`;
* `sv_known_inputs`: closes an `inputsKnown` obligation of `sv_equations` from such a port hypothesis;
* `sv_eq_nat`: the equations and knownness facts of `sv_equations` (`eq_*`, `known_*`) in `Nat` index form. A 32-bit
  wrap `canonInt 32 true x` that `omega` places in range is `x` (`canonInt32_of_bounds`, with the facts of the `$clog2`,
  power and quotient atoms); a row-major offset `rmN W i j` is `i.toNat * W.toNat + j.toNat`; and an `Int` term built from
  casts of `Nat` terms and non-negative literals by `+`, `*`, `^`, `/`, `%` is the cast of the `Nat` term with the same
  structure (definitionally: core's `Int.natCast_add` … are `rfl`), so `Int.toNat` of it is that term, a comparison of
  two such terms is the `Nat` comparison, and `Int.toNat` of a sum with negative terms (`↑k + -1 * 2 ^ l`) is the
  truncated `Nat` difference (`k - 2 ^ l`, by `omega` and `Int.toNat_sub`). Every rewrite is an equation proved here or
  by `omega`; nothing is assumed;
* `SvState.port_ofBitVec`, `SvState.port_ofBool`: an output port all of whose bits are known holds the vector of its
  Boolean bits (from a `known_*` family), the last step of a task proof.
-/

open Lean Elab Tactic Meta

namespace LeanModels.Sv

/-! ## The ports from their bits -/

/-- **An output port from its known bits**: where every bit `k < N` of `n` is known and the signal has width `W = N`,
the port holds the `BitVec` of its Boolean bits (a `known_*` family of `sv_equations` is the hypothesis). -/
theorem SvState.port_ofBitVec {st : SvState} {n : String} {N W : Nat}
    (hk : ∀ k, k < N → (∃ v, SvState.lookup st n = some v ∧ v.width = W) ∧ KnownBit st n k) (hW : W = N)
    (hN : 0 < N) : SvState.lookup st n = some (LVec.ofBitVec (XF.bv N (SvState.boolAt st n))) := by
  obtain ⟨⟨v, hv, hvw⟩, -⟩ := hk 0 hN
  rw [hv, SvState.lookup_eq_ofBitVec_bv hv (hvw.trans hW) fun k hk' => (hk k hk').2]

/-- … and a one-bit port holds the `BitVec.ofBool` of its bit. -/
theorem SvState.port_ofBool {st : SvState} {n : String} {W : Nat}
    (hk : (∃ v, SvState.lookup st n = some v ∧ v.width = W) ∧ KnownBit st n 0) (hW : W = 1) :
    SvState.lookup st n = some (LVec.ofBitVec (BitVec.ofBool (SvState.boolAt st n 0))) := by
  rw [SvState.port_ofBitVec (N := 1) (fun k hk' => by obtain rfl : k = 0 := (by omega); exact hk) hW (by decide)]
  congr 2
  exact BitVec.eq_of_getLsbD_eq fun i hi => by
    obtain rfl : i = 0 := (by omega)
    rw [XF.getLsbD_bv hi]
    simp

/-- The bit of `BitVec.ofBool b`. -/
theorem CombTask.getLsbD_ofBool_zero (b : Bool) : (BitVec.ofBool b).getLsbD 0 = b := by simp

/-! ## The `Nat` index forms (`sv_eq_nat`) -/

namespace CombView

theorem toNat_eq_of_eq_natCast {x : Int} {p : Nat} (h : x = ↑p) : x.toNat = p := by subst h; rfl

theorem toNat_eq_of_eq_sub {x : Int} {p q : Nat} (h : x = ↑p - ↑q) : x.toNat = p - q := by
  subst h; exact Int.toNat_sub p q

theorem natAbs_eq_of_eq_natCast {x : Int} {p : Nat} (h : x = ↑p) : x.natAbs = p := by subst h; rfl

theorem lt_eq_of_natCast {a b : Int} {a' b' : Nat} (ha : a = ↑a') (hb : b = ↑b') : (a < b) = (a' < b') := by
  subst ha; subst hb; exact propext Int.ofNat_lt

theorem le_eq_of_natCast {a b : Int} {a' b' : Nat} (ha : a = ↑a') (hb : b = ↑b') : (a ≤ b) = (a' ≤ b') := by
  subst ha; subst hb; exact propext Int.ofNat_le

theorem eq_eq_of_natCast {a b : Int} {a' b' : Nat} (ha : a = ↑a') (hb : b = ↑b') : (a = b) = (a' = b') := by
  subst ha; subst hb; exact propext Int.ofNat_inj

end CombView

end LeanModels.Sv

namespace LeanModels.Sv.CombNat

open LeanModels.Sv.CombView

/-- `↑e` (`Nat` to `Int`). -/
def intCast (e : Lean.Expr) : Lean.Expr :=
  mkApp3 (mkConst ``Nat.cast [levelZero]) (mkConst ``Int) (mkConst ``instNatCastInt) e

/-- `e` is the application of the homogeneous `Int` operation `op` (`HAdd.hAdd Int Int Int _ a b`, …). -/
def isIntOp (e : Lean.Expr) (op : Name) : Bool :=
  e.isAppOfArity op 6 && e.getArg! 0 == mkConst ``Int && e.getArg! 1 == mkConst ``Int

/-- **The `Nat` term of an `Int` term**: for `e` built from casts of `Nat` terms and non-negative literals by `+`, `*`,
`^` (a `Nat` exponent), `/` and `%`, the `Nat` term `e'` of the same structure, so that `e = ↑e'` holds definitionally
(core's `Int.natCast_add`, `natCast_mul`, `natCast_pow`, `natCast_ediv`, `natCast_emod` are `rfl`; `castEq?` checks it). -/
partial def natOf? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if e.isAppOfArity ``Nat.cast 3 && e.getArg! 0 == mkConst ``Int then return some e.appArg!
  if e.isAppOfArity ``Int.ofNat 1 then return some e.appArg!
  if let some v ← getIntValue? e then
    return if 0 ≤ v then some (mkNatLit v.toNat) else none
  let bin (op : Name) (mk : Lean.Expr → Lean.Expr → MetaM Lean.Expr) : MetaM (Option Lean.Expr) := do
    let some a ← natOf? (e.getArg! 4) | return none
    let some b ← natOf? (e.getArg! 5) | return none
    return some (← mk a b)
  if isIntOp e ``HAdd.hAdd then return ← bin ``HAdd.hAdd fun a b => pure (mkNatAdd a b)
  if isIntOp e ``HMul.hMul then return ← bin ``HMul.hMul fun a b => pure (mkNatMul a b)
  if isIntOp e ``HDiv.hDiv then return ← bin ``HDiv.hDiv fun a b => mkAppM ``HDiv.hDiv #[a, b]
  if isIntOp e ``HMod.hMod then return ← bin ``HMod.hMod fun a b => mkAppM ``HMod.hMod #[a, b]
  if e.isAppOfArity ``HPow.hPow 6 && e.getArg! 0 == mkConst ``Int && e.getArg! 1 == mkConst ``Nat then
    let some a ← natOf? (e.getArg! 4) | return none
    -- a power of two literals is its value (`i / 2 ^ 1 * 2 ^ 1` is `i / 2 * 2`)
    if let some bv ← getNatValue? a then
      if let some ev ← getNatValue? (e.getArg! 5) then
        if ev ≤ 64 then return some (mkNatLit (bv ^ ev))
    return some (← mkAppM ``HPow.hPow #[a, e.getArg! 5])
  return none

/-- A proof of `e = ↑e'` where it holds definitionally. -/
def castEq? (e e' : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let c := intCast e'
  if ← withDefault (isDefEq e c) then
    return some (← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e c))
  return none

/-- The terms of an `Int` sum. -/
partial def intSumTerms (e : Lean.Expr) : Array Lean.Expr :=
  if isIntOp e ``HAdd.hAdd then intSumTerms (e.getArg! 4) ++ intSumTerms (e.getArg! 5) else #[e]

/-- A proof of `p` by `omega` from the facts `facts` (proofs) alone, in the current local context. -/
def omegaWith (p : Lean.Expr) (facts : List Lean.Expr) : MetaM (Option Lean.Expr) := do
  let m ← mkFreshExprSyntheticOpaqueMVar p
  try
    let some g ← m.mvarId!.falseOrByContra | return none
    g.withContext do
      let some neg := (← getLCtx).lastDecl | throwError "no negation"
      Lean.Elab.Tactic.Omega.omega (neg.toExpr :: facts) g
    return some (← instantiateMVars m)
  catch _ => return none

/-- **`Int.toNat x` in `Nat` form**: the `Nat` term of `x` (`natOf?`), else, for a sum whose terms are such terms,
negative literals and negative literal multiples of such terms, the truncated difference `P - Q` of its positive and
negative parts, `x = ↑P - ↑Q` by `omega` from the terms' own cast equations. -/
def toNatStep? (x : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if let some x' ← natOf? x then
    if let some h ← castEq? x x' then
      return some (x', ← mkAppM ``toNat_eq_of_eq_natCast #[h])
  let mut pos : Array Lean.Expr := #[]
  let mut neg : Array Lean.Expr := #[]
  let mut facts : List Lean.Expr := []
  for t in intSumTerms x do
    if (← getIntValue? t) == some 0 then continue
    if let some t' ← natOf? t then
      let some h ← castEq? t t' | return none
      pos := pos.push t'
      facts := h :: facts
      continue
    if let some v ← getIntValue? t then
      if v < 0 then
        neg := neg.push (mkNatLit (-v).toNat)
        continue
      return none
    if isIntOp t ``HMul.hMul then
      if let some c ← getIntValue? (t.getArg! 4) then
        if c < 0 then
          if let some u' ← natOf? (t.getArg! 5) then
            let some hu ← castEq? (t.getArg! 5) u' | return none
            neg := neg.push (if c == -1 then u' else mkNatMul (mkNatLit (-c).toNat) u')
            facts := hu :: facts
            continue
    return none
  if neg.isEmpty then return none
  let sumOf (xs : Array Lean.Expr) : Lean.Expr :=
    if h : 0 < xs.size then (xs.extract 1 xs.size).foldl mkNatAdd xs[0] else mkNatLit 0
  let p := sumOf pos
  let q := sumOf neg
  let goal ← mkEq x (← mkAppM ``HSub.hSub #[intCast p, intCast q])
  let some h ← omegaWith goal facts | return none
  return some (← mkAppM ``HSub.hSub #[p, q], ← mkAppM ``toNat_eq_of_eq_sub #[h])

/-- A proof that `x` (an `Int` term of the main goal's context) is in the signed 32-bit range, as the two hypotheses of
`canonInt32_of_bounds`, by the parameter stage's own route (`addClog2Facts`, `addPowFacts`, `int32Bound`, its fallback
`int32DecideAll`). -/
def rangeProofs? (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let pfFn := mkApp (mkConst ``LeanModels.Sv.CombView.canonInt32_of_bounds) x
  let (bs, _, _) ← forallMetaTelescopeReducing (← inferType pfFn)
  for b in bs do
    let ok ← try
        let gs ← Lean.Elab.Term.TermElabM.run' (Lean.Elab.Tactic.run b.mvarId! do
          addClog2Facts #[x]
          addPowFacts #[x]
          let g ← getMainGoal
          try int32Bound catch _ => (do setGoals [g]; int32DecideAll))
        pure gs.isEmpty
      catch _ => pure false
    unless ok do return none
  return some (← instantiateMVars (mkAppN pfFn bs))

/-- The rewriting step of `sv_eq_nat` at one subterm (a `Simp` post-procedure). `cache` holds the range proofs of the
wrapped values already tried. -/
def natPost (cache : IO.Ref (Array (Lean.Expr × Option Lean.Expr))) (e : Lean.Expr) : MetaM (Option Simp.Result) := do
  -- a 32-bit wrap whose value `omega` places in range
  if e.isAppOfArity ``LeanModels.Sv.canonInt 3 && !e.hasLooseBVars then
    let x := e.appArg!
    unless (← isDefEq e.appFn!.appFn!.appArg! (toExpr (32 : Nat))) && (← isDefEq e.appFn!.appArg! (toExpr true)) do
      return none
    let cached := (← cache.get).find? (·.1 == x)
    let pf? ← match cached with
      | some (_, p) => pure p
      | none => do
          let p ← rangeProofs? x
          cache.modify (·.push (x, p))
          pure p
    let some pf := pf? | return none
    return some { expr := x, proof? := some (← mkExpectedTypeHint pf (← mkEq e x)) }
  if e.isAppOfArity ``Int.toNat 1 then
    let some (e', pf) ← toNatStep? e.appArg! | return none
    return some { expr := e', proof? := some pf }
  if e.isAppOfArity ``Int.natAbs 1 then
    let some x' ← natOf? e.appArg! | return none
    let some h ← castEq? e.appArg! x' | return none
    return some { expr := x', proof? := some (← mkAppM ``natAbs_eq_of_eq_natCast #[h]) }
  -- a comparison of two `Int` terms that are casts of `Nat` terms
  let cmp (lem : Name) (a b : Lean.Expr) (mk : Lean.Expr → Lean.Expr → MetaM Lean.Expr) : MetaM (Option Simp.Result) := do
    let some a' ← natOf? a | return none
    let some b' ← natOf? b | return none
    let some ha ← castEq? a a' | return none
    let some hb ← castEq? b b' | return none
    return some { expr := ← mk a' b', proof? := some (← mkAppM lem #[ha, hb]) }
  if e.isAppOfArity ``LT.lt 4 && e.getArg! 0 == mkConst ``Int then
    return ← cmp ``lt_eq_of_natCast (e.getArg! 2) (e.getArg! 3) fun a b => mkAppM ``LT.lt #[a, b]
  if e.isAppOfArity ``LE.le 4 && e.getArg! 0 == mkConst ``Int then
    return ← cmp ``le_eq_of_natCast (e.getArg! 2) (e.getArg! 3) fun a b => mkAppM ``LE.le #[a, b]
  if e.isAppOfArity ``Eq 3 && e.getArg! 0 == mkConst ``Int then
    return ← cmp ``eq_eq_of_natCast (e.getArg! 1) (e.getArg! 2) mkEq
  return none

/-- `sv_eq_nat` on one hypothesis: its type rewritten by `natPost` (and `rmN` unfolded) under every binder. -/
def natHyp (cache : IO.Ref (Array (Lean.Expr × Option Lean.Expr))) (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← h.getType)
  let thms ← ({} : SimpTheorems).addDeclToUnfold ``LeanModels.Sv.CombView.rmN
  let ctx ← Simp.mkContext (config := { maxSteps := 400000 }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let post : Simp.Simproc := fun e => do
    match ← natPost cache e with
    | some r => return .done r
    | none => return .continue
  let (r, _) ← Simp.main ty ctx (methods := { post := post })
  if r.expr == ty then return g
  match ← applySimpResultToLocalDecl g h r false with
  | some (_, g') => return g'
  | none => return g

end LeanModels.Sv.CombNat

open LeanModels.Sv.CombNat in
/-- `sv_eq_nat`: the `eq_*` and `known_*` hypotheses of `sv_equations` in `Nat` index form (see the module docstring). -/
elab "sv_eq_nat" : tactic => do
  let g ← getMainGoal
  let hs ← g.withContext do
    let mut hs : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let n := d.userName.toString
      if n.startsWith "eq_" || n.startsWith "known_" then hs := hs.push d.fvarId
    return hs
  let cache ← IO.mkRef (#[] : Array (Lean.Expr × Option Lean.Expr))
  let mut g := g
  for h in hs do
    g ← natHyp cache g h
  replaceMainGoal [g]

/-- The input hypotheses of a task proof: `(h, n, v)` for each `h : SvState.lookup I n = some v` with `n` a string
literal, and the transfer hypothesis `hin : ∀ n ∈ L, ∀ v, SvState.lookup I n = some v → SvState.lookup S n = some v`. -/
private def findTransfer : TacticM (Option (Name × Lean.Expr × Lean.Expr)) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let r ← forallTelescopeReducing t fun xs body => do
      unless xs.size == 4 do return none
      unless body.isAppOfArity ``Eq 3 && (body.getArg! 1).isAppOfArity ``LeanModels.Sv.SvState.lookup 2 do return none
      let prem ← inferType xs[3]!
      unless prem.isAppOfArity ``Eq 3 && (prem.getArg! 1).isAppOfArity ``LeanModels.Sv.SvState.lookup 2 do return none
      let I := (prem.getArg! 1).getArg! 0
      let S := (body.getArg! 1).getArg! 0
      if I.hasLooseBVars || S.hasLooseBVars || I.containsFVar xs[0]!.fvarId! then return none
      return some (I, S)
    if let some (I, S) := r then return some (d.userName, I, S)
  return none

/-- `sv_inputs`: the stimulus-to-snapshot step of a task proof (see the module docstring). -/
elab "sv_inputs" : tactic => withMainContext do
  let some (hinN, I, S) ← findTransfer
    | throwError "sv_inputs: no transfer hypothesis `∀ n ∈ L, ∀ v, SvState.lookup inputs n = some v → SvState.lookup st n = some v` in the context (`CombTask.of_comb`, `Models2.of_comb_ports`)"
  -- 1. every input hypothesis, carried to the snapshot
  let ins ← do
    let mut acc : Array (Name × String) := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``Eq 3 && (t.getArg! 1).isAppOfArity ``LeanModels.Sv.SvState.lookup 2 &&
          (t.getArg! 1).getArg! 0 == I then
        if let .lit (.strVal n) := (t.getArg! 1).getArg! 1 then acc := acc.push (d.userName, n)
    pure acc
  for (h, n) in ins do
    let hId := mkIdent h
    let nLit := Syntax.mkStrLit n
    evalTactic (← `(tactic| replace $hId:ident := $(mkIdent hinN):ident $nLit (by simp) _ $hId:ident))
  -- 2. a one-bit port's `BitVec 1` as the `Bool` it holds
  for (h, _) in ins do
    withMainContext do
      let some d := (← getLCtx).findFromUserName? h | return
      let t ← instantiateMVars d.type
      let v := t.getArg! 2
      unless v.isAppOfArity ``Option.some 2 && v.appArg!.isAppOfArity ``LeanModels.Sv.LVec.ofBitVec 2 do return
      let x := v.appArg!.appArg!
      unless x.isFVar do return
      let ty ← whnf (← inferType x)
      unless ty.isAppOfArity ``BitVec 1 && (← isDefEq ty.appArg! (toExpr (1 : Nat))) do return
      let xId := mkIdent (← x.fvarId!.getUserName)
      evalTactic (← `(tactic| (obtain ⟨$xId:ident, hx⟩ : ∃ b : Bool, $xId:ident = BitVec.ofBool b :=
        ⟨_, LeanModels.Sv.CombTask.bv1_eq_ofBool $xId:ident⟩; subst hx)))
  evalTactic (← `(tactic| try simp only [BitVec.toNat_ofBool]))
  -- 3. the bits of each port, as the equations read them
  for (h, n) in ins do
    withMainContext do
      let some d := (← getLCtx).findFromUserName? h | return
      let t ← instantiateMVars d.type
      let v := t.getArg! 2
      unless v.isAppOfArity ``Option.some 2 && v.appArg!.isAppOfArity ``LeanModels.Sv.LVec.ofBitVec 2 do return
      let x := v.appArg!.appArg!
      let w := v.appArg!.getArg! 0
      let nE := toExpr n
      let bitN := Name.mkSimple ("bit_" ++ n)
      let (ty, pf) ← if x.isAppOfArity ``BitVec.ofBool 1 then do
          let b := x.appArg!
          let lhs := mkApp3 (mkConst ``LeanModels.Sv.SvState.boolAt) S nE (toExpr (0 : Nat))
          let h1 ← mkAppM ``LeanModels.Sv.SvState.boolAt_ofBitVec #[d.toExpr, ← mkDecideProof (← mkAppM ``LT.lt #[toExpr (0 : Nat), toExpr (1 : Nat)])]
          let pf ← mkEqTrans h1 (← mkAppM ``LeanModels.Sv.CombTask.getLsbD_ofBool_zero #[b])
          pure (← mkEq lhs b, pf)
        else
          withLocalDeclD `i (mkConst ``Nat) fun i => do
            withLocalDeclD `hi (← mkAppM ``LT.lt #[i, w]) fun hi => do
              let pf ← mkAppM ``LeanModels.Sv.SvState.boolAt_ofBitVec #[d.toExpr, hi]
              let ty ← mkForallFVars #[i, hi] (← inferType pf)
              pure (ty, ← mkLambdaFVars #[i, hi] pf)
      let g ← getMainGoal
      let g ← g.assert bitN ty pf
      let (_, g) ← g.intro1P
      replaceMainGoal [g]

/-- `sv_known_inputs`: an `inputsKnown` obligation of `sv_equations` (`∃ v, SvState.lookup st n = some v ∧ v.allKnown =
true ∧ v.width = W`) from a port hypothesis `h : SvState.lookup st n = some (LVec.ofBitVec x)` in context
(`inKnown_ofBitVec`, the width by `omega`). -/
elab "sv_known_inputs" : tactic => withMainContext do
  let hs ← do
    let mut acc : Array Name := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``Eq 3 && (t.getArg! 1).isAppOfArity ``LeanModels.Sv.SvState.lookup 2 &&
          (t.getArg! 2).isAppOfArity ``Option.some 2 &&
          (t.getArg! 2).appArg!.isAppOfArity ``LeanModels.Sv.LVec.ofBitVec 2 then
        acc := acc.push d.userName
    pure acc
  for h in hs do
    let st ← saveState
    try
      evalTactic (← `(tactic| (refine LeanModels.Sv.CombEq.inKnown_ofBitVec $(mkIdent h):ident ?_; omega)))
      if (← getGoals).isEmpty then return
      st.restore
    catch _ => st.restore
  throwError "sv_known_inputs: no port hypothesis `SvState.lookup st n = some (LVec.ofBitVec x)` in the context gives this obligation"

/-- `sv_obligations`: the standard closers of the obligations `sv_equations` returns, chosen by each goal's tag (so no
closer is tried on an obligation of another kind, where it fails at a cost: `sv_pow_omega` on a coverage goal runs its
whole bisection before failing). `inputsKnown_k` by `sv_known_inputs`; `cover_k` by `sv_cover`, then
`sv_pow_facts <;> sv_cover` (the other order where the goal holds a wrapped constant, a `$clog2` or a power); `auto_k`, `inRange_k`, `width_k`, `bitRead_k` by `intros; omega`, then `sv_pow_omega`. A goal
of another tag (the main goal) is left untouched, and so is an obligation none of its closers proves. The closers run
without info trees (tac10): a failed attempt's trees would otherwise stay alive after its state is restored. -/
elab "sv_obligations" : tactic => do
  let gs ← getGoals
  let mut rest : Array MVarId := #[]
  for g in gs do
    if ← g.isAssigned then continue
    let tag := (← g.getTag).eraseMacroScopes.toString
    let isTag (p : String) : Bool := tag == p || tag.startsWith (p ++ "_")
    let tac? : Option (TSyntax `tactic) ←
      if isTag "inputsKnown" then pure (some (← `(tactic| sv_known_inputs)))
      else if isTag "cover" then
        -- a goal with a wrapped constant, a `$clog2` or a power needs their facts first (`sv_pow_facts`); without them
        -- `sv_cover` fails after its whole search
        let ty ← instantiateMVars (← g.getType)
        let atoms := (ty.find? fun x => x.isConstOf ``LeanModels.Sv.canonInt || x.isConstOf ``LeanModels.Sv.clog2 ||
          x.isConstOf ``HPow.hPow).isSome
        if atoms then pure (some (← `(tactic| first | (sv_pow_facts <;> sv_cover) | sv_cover)))
        else pure (some (← `(tactic| first | sv_cover | (sv_pow_facts <;> sv_cover))))
      else if isTag "auto" || isTag "inRange" || isTag "width" || isTag "bitRead" then
        pure (some (← `(tactic| first | (intros; omega) | sv_pow_omega)))
      else pure none
    let some tac := tac? | rest := rest.push g; continue
    setGoals [g]
    let st ← saveState
    try
      withEnableInfoTree false (evalTactic tac)
      rest := rest ++ (← getGoals).toArray
    catch _ =>
      st.restore
      rest := rest.push g
  setGoals rest.toList
