import Lean
import LeanModels.Sv.CombViewTactic
import LeanModels.Sv.CombCover

/-!
# `sv_cover`, slot windows: the writer's index map inverted (quotient and forced witnesses)

The 2-D rule (`CombCover.lean`) solves each writer's `∃`-variables from the equations of the read's row and of a one-bit
window's column. A design whose slots have a symbolic width (the Karatsuba record's level slots `P >> l`, `P = 4·2^L`)
or whose writers fix a variable by a one-iteration loop (the Dadda record's `E ≤ x < E + 1`) gives coverage goals it does
not read: the column `3·(t'·(P >> (l+1))) + c·(P >> (l+1))` of a writer has no equation with the read's column
`t·(P >> l) + k`, only the window `c₀ ≤ C + k < c₀ + w`. This module extends the rule; `sv_cover` tries it after the
2-D rule fails, and first on a goal holding a product of two non-numeral factors (which the 2-D rule cannot read)
(`sv_comb.cover_units`, default on): every other goal the 2-D rule proves is proved as before.

**The writer's index map inverted.** Every witness is SOLVED, never searched:
* rows: an equation of the read's row; through a nested row-major offset `↑(rmN W a b) = ↑(rmN W a' b')` its two
  components (`rmN_cast_congr`, sufficient);
* forced variables: `E ≤ x ∧ x < E + 1` gives `x = E`; a natural `x < B` with `B` a closed term of value `1` gives `x = 0`;
* SLOT WINDOWS: the writer's column `c₀ = U·a + b` and the read's column `C = Y·a' + b'` are split syntactically by a
  UNIT (`ulin`: `+`, `-`, `-·`, products with the unit as a factor; each step a lemma): `U` the factor of a writer's
  unknown (`t'·U`, or a numeral coefficient), `Y` the factor of the read's own variable. The two units are related
  (`U = kw·u`, `Y = kr·u`, numerals `kw`, `kr`): the same term, two slot widths `X / 2^e` of a power-of-two `X = c·2^t`
  whose exponents differ by a constant, or a slot width and a numeral (its value). Where the read's unit is `ρ` times
  the writer's, the writer's column is regrouped in the read's unit (`ulin_regroup`: the multiples of `U` below `ρ` are
  an offset inside the read's slot). The UNIT EQUATION `kw·a = kr·a'` is linear in the unknowns with numeral
  coefficients: solving it gives the quotient witnesses (`(i₁ - c)/3`, `3·i₁ + c`). The window then follows from
  `rmN_win_unit`: the products cancel, and what is left is linear (`b ≤ b' + k < b + w`, the units' relations, the
  unit equation, `0 ≤ Y, a', b'`).

**The facts of the atoms**, which `omega` reads as opaque: slot widths (non-negative, at most `X`, at least `c` where
`e ≤ t`, their shifts `X/2^e₂ = 2^d·X/2^e₁` and congruence, the values the plans ask for), powers of a numeral base
(positive, `1` at exponent `0`, monotone in the base, exponent shifts, congruence), products (non-negative, zero with a
zero factor), truncated quotients of a non-negative numerator, and `$clog2` (as `sv_pow_facts` states them). Each is a
GUARDED fact, its guards decided by `omega` against the goal's hypotheses: all proved, the fact is added; one refuted,
nothing; otherwise it is kept PENDING and decided again where it is needed (a leaf's last resort, as a disjunction).
Every fact is a proved lemma.

**The walk.** A writer's row equation between terms of the context that the context does not decide (`L = 0`,
`L = i + 1`, `0 = s`) is split first: in each branch the facts' guards are decided. Then: a writer refuted by the
context is never a case; a writer whose condition the context proves closes the goal; otherwise `Classical.em` of each
writer's condition but the last one's, the negation keeping only the components the context does not prove; the last
writer's condition is proved component by component, the equations first, each with the earlier ones as hypotheses.
Each writer the context does not refute is tried as the last one.

Kernel-checked: the proof term is built from the lemmas below, `omega`'s proofs and the decided facts; nothing is
assumed. -/

register_option sv_comb.cover_units : Bool := {
  defValue := true
  descr := "sv_cover: after the 2-D rule fails, the rule with slot windows, forced witnesses and nested rows" }

namespace LeanModels.Sv
namespace CombCoverUnit

open CombView Lean Meta Elab Tactic


/-! ## Lemmas -/

/-- **A slot window by its unit**: the window's column `c0 = U·a + b` and the read's column `C = Y·a' + b'`, the units
two multiples `kw·u`, `kr·u` of one `u` with `kw·a = kr·a'`: the products cancel, and the window holds when the rest
does. The column `c0` may be negative (the window then starts at its row's first cell). -/
theorem rmN_win_unit {W r R c0 C U Y u a a' b b' kw kr : Int} {e wd : Nat}
    (hc0 : c0 = U * a + b) (hC : C = Y * a' + b') (hr : r = R) (hU : U = kw * u) (hY : Y = kr * u)
    (ha : kw * a = kr * a') (hY0 : 0 ≤ Y) (ha0 : 0 ≤ a') (hb0 : 0 ≤ b') (h1 : b ≤ b' + (e : Int))
    (h2 : b' + (e : Int) < b + (wd : Int)) :
    rmN W r c0 ≤ rmN W R C + e ∧ rmN W R C + e < rmN W r c0 + wd := by
  have hm : U * a = Y * a' := by
    rw [hU, hY, Int.mul_right_comm kw u a, ha, Int.mul_right_comm kr a' u]
  have hp : 0 ≤ Y * a' := Int.mul_nonneg hY0 ha0
  subst hr
  unfold rmN
  constructor <;> omega

theorem rmN_cast_congr {W a b a' b' : Int} (h1 : a = a') (h2 : b = b') :
    ((rmN W a b : Nat) : Int) = ((rmN W a' b' : Nat) : Int) := by rw [h1, h2]

theorem ulin_self (U : Int) : U = U * 1 + 0 := by omega
theorem ulin_free (e U : Int) : e = U * 0 + e := by omega
theorem ulin_add {x y U a1 b1 a2 b2 : Int} (h1 : x = U * a1 + b1) (h2 : y = U * a2 + b2) :
    x + y = U * (a1 + a2) + (b1 + b2) := by rw [h1, h2, Int.mul_add]; omega
theorem ulin_sub {x y U a1 b1 a2 b2 : Int} (h1 : x = U * a1 + b1) (h2 : y = U * a2 + b2) :
    x - y = U * (a1 - a2) + (b1 - b2) := by rw [h1, h2, Int.mul_sub]; omega
theorem ulin_neg {x U a b : Int} (h : x = U * a + b) : -x = U * (-a) + (-b) := by rw [h, Int.mul_neg]; omega
theorem ulin_mul_r (x U : Int) : x * U = U * x + 0 := by rw [Int.mul_comm]; omega
theorem ulin_mul_l (U y : Int) : U * y = U * y + 0 := by omega
theorem ulin_cmul {k x U a b : Int} (h : x = U * a + b) : k * x = U * (k * a) + k * b := by
  rw [h, Int.mul_add, ← Int.mul_assoc, Int.mul_comm k U, Int.mul_assoc]
theorem ulin_mulc {k x U a b : Int} (h : x = U * a + b) : x * k = U * (a * k) + b * k := by
  rw [h, Int.add_mul, Int.mul_assoc]

theorem ulin_regroup {c0 U a b aY r k : Int} (h : c0 = U * a + b) (ha : a = k * aY + r) :
    c0 = (k * U) * aY + (U * r + b) := by
  rw [h, ha, Int.mul_add, ← Int.mul_assoc, Int.mul_comm U k]; omega

theorem slot_nonneg {c X : Int} {t : Nat} (hX : c * 2 ^ t = X) (hc : 0 ≤ c) (e : Nat) : 0 ≤ X / 2 ^ e :=
  Int.ediv_nonneg (by rw [← hX]; exact Int.mul_nonneg hc (Int.pow_nonneg (by decide))) (Int.pow_nonneg (by decide))

theorem slot_shift {c X : Int} {t : Nat} (hX : c * 2 ^ t = X) {e1 e2 d : Nat} (he : e1 = e2 + d) (hle : e1 ≤ t) :
    X / 2 ^ e2 = 2 ^ d * (X / 2 ^ e1) := by
  subst hX
  have p1 : (2 : Int) ^ e1 ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  have p2 : (2 : Int) ^ e2 ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  have t1 : (2 : Int) ^ t = 2 ^ (t - e1) * 2 ^ e1 := by rw [← Int.pow_add]; congr 1; omega
  have t2 : (2 : Int) ^ t = 2 ^ d * 2 ^ (t - e1) * 2 ^ e2 := by rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
  have q1 : c * (2 : Int) ^ t / 2 ^ e1 = c * 2 ^ (t - e1) := by
    rw [t1, ← Int.mul_assoc, Int.mul_ediv_cancel _ p1]
  have q2 : c * (2 : Int) ^ t / 2 ^ e2 = 2 ^ d * (c * 2 ^ (t - e1)) := by
    rw [t2, ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_ediv_cancel _ p2, Int.mul_comm c, Int.mul_assoc]
  rw [q1, q2]

theorem slot_shift_or {c X : Int} {t : Nat} (hX : c * 2 ^ t = X) (e1 e2 d : Nat) {k : Int} (hk : 2 ^ d = k) :
    e1 ≠ e2 + d ∨ t < e1 ∨ X / 2 ^ e2 = k * (X / 2 ^ e1) := by
  by_cases h1 : e1 = e2 + d
  · by_cases h2 : t < e1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (by rw [← hk]; exact slot_shift hX h1 (by omega)))
  · exact Or.inl h1

theorem slot_congr_or (X : Int) (e1 e2 : Nat) : e1 ≠ e2 ∨ X / 2 ^ e2 = X / 2 ^ e1 := by
  by_cases h : e1 = e2
  · exact Or.inr (by rw [h])
  · exact Or.inl h

theorem slot_val {c X : Int} {t : Nat} (hX : c * 2 ^ t = X) {e d : Nat} {n : Int} (hn : c * 2 ^ d = n)
    (he : t = e + d) : X / 2 ^ e = n := by
  subst hX; subst hn; subst he
  have p : (2 : Int) ^ e ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  rw [Int.pow_add, show c * (2 ^ e * 2 ^ d) = c * 2 ^ d * 2 ^ e by ac_rfl, Int.mul_ediv_cancel _ p]

theorem slot_val_or {c X : Int} {t : Nat} (hX : c * 2 ^ t = X) (e d : Nat) {n : Int} (hn : c * 2 ^ d = n) :
    t ≠ e + d ∨ X / 2 ^ e = n := by
  by_cases h : t = e + d
  · exact Or.inr (slot_val hX hn h)
  · exact Or.inl h

theorem slot_ge {c X : Int} {t : Nat} (hX : c * 2 ^ t = X) (hc : 0 ≤ c) {e : Nat} (h : e ≤ t) : c ≤ X / 2 ^ e := by
  have hv := slot_val hX (e := e) (d := t - e) (n := c * 2 ^ (t - e)) rfl (by omega)
  rw [hv]
  have h1 : (1 : Int) ≤ 2 ^ (t - e) := Int.pow_pos (by decide)
  calc c = c * 1 := (Int.mul_one c).symm
    _ ≤ c * 2 ^ (t - e) := Int.mul_le_mul_of_nonneg_left h1 hc

theorem slot_ge_or {c X : Int} {t : Nat} (hX : c * 2 ^ t = X) (hc : 0 ≤ c) (e : Nat) : t < e ∨ c ≤ X / 2 ^ e := by
  by_cases h : e ≤ t
  · exact Or.inr (slot_ge hX hc h)
  · exact Or.inl (by omega)

theorem slot_le {c X : Int} {t : Nat} (hX : c * 2 ^ t = X) (hc : 0 ≤ c) (e : Nat) : X / 2 ^ e ≤ X :=
  Int.ediv_le_self _ (by rw [← hX]; exact Int.mul_nonneg hc (Int.pow_nonneg (by decide)))

theorem mul_zero_or (g y : Int) : g ≠ 0 ∨ g * y = 0 := by
  by_cases h : g = 0
  · exact Or.inr (by rw [h, Int.zero_mul])
  · exact Or.inl h

theorem pow_zero_or (b : Int) (t : Nat) : t ≠ 0 ∨ b ^ t = 1 := by
  by_cases h : t = 0
  · exact Or.inr (by rw [h, Int.pow_zero])
  · exact Or.inl h

/-! ## Reading a disjunct (the 2-D rule's readers, `CombCover.lean`, where they are private: the same definitions) -/

structure WinParts where
  W : Lean.Expr
  r : Lean.Expr
  c0 : Lean.Expr
  R : Lean.Expr
  C : Lean.Expr
  e : Lean.Expr
  wd : Lean.Expr
deriving Inhabited

def isRmN (x : Lean.Expr) : Bool := x.isAppOfArity ``LeanModels.Sv.CombView.rmN 3

def cmpSides? (rel : Name) (x : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if x.isAppOfArity rel 4 then some (x.getArg! 2, x.getArg! 3) else none

def readPos? (x : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr × Option Lean.Expr) :=
  if isRmN x then some (x.getArg! 0, x.getArg! 1, x.getArg! 2, none)
  else if x.isAppOfArity ``HAdd.hAdd 6 && isRmN (x.getArg! 4) then
    let y := x.getArg! 4
    some (y.getArg! 0, y.getArg! 1, y.getArg! 2, some (x.getArg! 5))
  else none

def matchWin (n : Lean.Expr) : Option WinParts := do
  guard (n.isAppOfArity ``And 2)
  let (lo, x) ← cmpSides? ``LE.le (n.appFn!.appArg!)
  let (x', hi) ← cmpSides? ``LT.lt (n.appArg!)
  guard (isRmN lo)
  guard (x == x')
  guard (hi.isAppOfArity ``HAdd.hAdd 6)
  guard (hi.getArg! 4 == lo)
  let (W', R, C, e?) ← readPos? x
  guard (W' == lo.getArg! 0)
  let nat0 := mkNatLit 0
  pure { W := W', r := lo.getArg! 1, c0 := lo.getArg! 2, R := R, C := C, e := e?.getD nat0,
         wd := hi.getArg! 5 }

def isZero (x : Lean.Expr) : Bool :=
  x.nat? == some 0 || x.int? == some 0 || (x.isAppOfArity ``Nat.cast 3 && (x.getArg! 2).nat? == some 0)

def tidy (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun x => do
    if x.isAppOfArity ``HSub.hSub 6 && isZero (x.getArg! 5) then return .done (x.getArg! 4)
    else if x.isAppOfArity ``HAdd.hAdd 6 && isZero (x.getArg! 5) then return .done (x.getArg! 4)
    else if x.isAppOfArity ``HAdd.hAdd 6 && isZero (x.getArg! 4) then return .done (x.getArg! 5)
    else if x.isAppOfArity ``Nat.cast 3 && (x.getArg! 0).isConstOf ``Int then
      match (x.getArg! 2).nat? with
      | some n => return .done (mkIntLit n)
      | none => return .continue
    else return .continue)

/-! ## Solving -/

partial def coeff (v : FVarId) (x : Lean.Expr) : MetaM (Option Int) := do
  if !x.containsFVar v then return some 0
  if x.isFVar then return (if x.fvarId! == v then some 1 else none)
  let args := x.getAppArgs
  match x.getAppFn with
  | .const n _ =>
    if n == ``Nat.cast && args.size == 3 then coeff v args[2]!
    else if (n == ``HAdd.hAdd || n == ``HSub.hSub) && args.size == 6 then
      let isSub := n == ``HSub.hSub
      if isSub && (← whnfR args[0]!).isConstOf ``Nat then return none
      match ← coeff v args[4]!, ← coeff v args[5]! with
      | some a, some b => return some (if isSub then a - b else a + b)
      | _, _ => return none
    else if n == ``HMul.hMul && args.size == 6 then
      if !args[4]!.containsFVar v then
        match ← getIntValue? args[4]!, ← coeff v args[5]! with
        | some k, some b => return some (k * b)
        | _, _ => return none
      else if !args[5]!.containsFVar v then
        match ← coeff v args[4]!, ← getIntValue? args[5]! with
        | some a, some k => return some (a * k)
        | _, _ => return none
      else return none
    else if n == ``Neg.neg && args.size == 3 then
      match ← coeff v args[2]! with
      | some a => return some (-a)
      | none => return none
    else return none
  | _ => return none

def witness (v : FVarId) (lhs T : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let some a ← coeff v lhs | return none
  if a == 0 then return none
  let rest ← tidy (lhs.replaceFVar (mkFVar v) (mkNatLit 0))
  let ty ← whnfR (← inferType lhs)
  if ty.isConstOf ``Int then
    let q ← if a > 0 then mkAppM ``HSub.hSub #[T, rest] else mkAppM ``HSub.hSub #[rest, T]
    let q ← if a == 1 || a == -1 then pure q else mkAppM ``HDiv.hDiv #[q, mkIntLit a.natAbs]
    return some (← mkAppM ``Int.toNat #[← tidy q])
  else if ty.isConstOf ``Nat && a == 1 then
    return some (← mkAppM ``HSub.hSub #[T, rest])
  else return none

/-- Solve what the equations determine: repeatedly an equation with exactly one unsolved unknown. -/
def solvePartial (unk : Array FVarId) (sol0 : Array (Option Lean.Expr)) (eqs : Array (Lean.Expr × Lean.Expr)) :
    MetaM (Array (Option Lean.Expr)) := do
  let mut sol := sol0
  let subst (sol : Array (Option Lean.Expr)) (x : Lean.Expr) : Lean.Expr := Id.run do
    let mut y := x
    for i in [0:unk.size] do
      if let some w := sol[i]! then y := y.replaceFVar (mkFVar unk[i]!) w
    pure y
  let mut progress := true
  while progress do
    progress := false
    for i in [0:unk.size] do
      if sol[i]!.isSome then continue
      let mut pick : Option (Lean.Expr × Lean.Expr) := none
      for (lhs0, T0) in eqs do
        if pick.isSome then break
        let lhs := subst sol lhs0
        let T := subst sol T0
        let some a ← coeff unk[i]! lhs | continue
        if a == 0 then continue
        let mut only := true
        for k in [0:unk.size] do
          if k != i && sol[k]!.isNone && (lhs.containsFVar unk[k]! || T.containsFVar unk[k]!) then only := false
        if only && !T.containsFVar unk[i]! then pick := some (lhs, T)
      if let some (lhs, T) := pick then
        if let some w ← witness unk[i]! lhs T then
          sol := sol.set! i (some w)
          progress := true
  return sol

/-! ## Rows through nested row-major offsets -/

def castRmN? (x : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  if x.isAppOfArity ``Nat.cast 3 && isRmN (x.getArg! 2) then
    let y := x.getArg! 2
    some (y.getArg! 0, y.getArg! 1, y.getArg! 2)
  else none

/-- The leaf equations of a row equation `r = R`: through `↑(rmN W a b) = ↑(rmN W a' b')` (the same `W`) the
equations of `a = a'` and `b = b'` (sufficient: `rmN_cast_congr`). -/
partial def rowPairs (r R : Lean.Expr) : Array (Lean.Expr × Lean.Expr) :=
  match castRmN? r, castRmN? R with
  | some (W, a, b), some (W', a', b') => if W == W' then rowPairs a a' ++ #[(b, b')] else #[(r, R)]
  | _, _ => #[(r, R)]

/-- The proof of `r = R` from the proofs of its leaf equations (in `rowPairs` order). -/
partial def rowProof (r R : Lean.Expr) (ps : List Lean.Expr) : MetaM (Lean.Expr × List Lean.Expr) := do
  match castRmN? r, castRmN? R with
  | some (W, a, b), some (W', a', b') =>
    if W == W' then
      let (pa, ps1) ← rowProof a a' ps
      let pb :: ps2 := ps1 | throwError "sv_cover: internal error (row)"
      return (← mkAppOptM ``rmN_cast_congr #[some W, some a, some b, some a', some b', some pa, some pb], ps2)
    else
      let p :: ps' := ps | throwError "sv_cover: internal error (row)"
      return (p, ps')
  | _, _ =>
    let p :: ps' := ps | throwError "sv_cover: internal error (row)"
    return (p, ps')

/-! ## Units -/

/-- `X / 2 ^ e` at type `Int`: `(X, e)`. -/
def slotAtom? (x : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if x.isAppOfArity ``HDiv.hDiv 6 && (x.getArg! 0).isConstOf ``Int then
    let d := x.getArg! 5
    if d.isAppOfArity ``HPow.hPow 6 && (d.getArg! 4).int? == some 2 then some (x.getArg! 4, d.getArg! 5) else none
  else none

def isNumeral (x : Lean.Expr) : Bool :=
  x.nat?.isSome || x.int?.isSome || (x.isAppOfArity ``OfNat.ofNat 3 && (x.getArg! 1).isRawNatLit)

def isMul (x : Lean.Expr) : Bool := x.isAppOfArity ``HMul.hMul 6
def isAddSub (x : Lean.Expr) : Bool := x.isAppOfArity ``HAdd.hAdd 6 || x.isAppOfArity ``HSub.hSub 6

/-- A product of two non-numeral factors in the sum `x` (through `+`, `-`, `-·` and numeral factors). -/
partial def hasProd (x : Lean.Expr) : Bool :=
  if isAddSub x then hasProd (x.getArg! 4) || hasProd (x.getArg! 5)
  else if x.isAppOfArity ``Neg.neg 3 then hasProd (x.getArg! 2)
  else if isMul x then
    let a := x.getArg! 4
    let b := x.getArg! 5
    if isNumeral a then hasProd b else if isNumeral b then hasProd a else true
  else false

/-- The unit of the window column `c0`: a non-numeral factor `U` free of the unknowns `us` whose cofactor mentions
one (`t * U`, `U * t`), else the numeral coefficient of an unknown (`8 * ↑x`). -/
partial def findUnit (us : Array FVarId) (c0 : Lean.Expr) : Option Lean.Expr :=
  let hasU (x : Lean.Expr) : Bool := us.any (x.containsFVar ·)
  let rec prodU (x : Lean.Expr) : Option Lean.Expr :=
    if isAddSub x then (prodU (x.getArg! 4)).orElse fun _ => prodU (x.getArg! 5)
    else if x.isAppOfArity ``Neg.neg 3 then prodU (x.getArg! 2)
    else if isMul x then
      let a := x.getArg! 4
      let b := x.getArg! 5
      if isNumeral a then prodU b
      else if isNumeral b then prodU a
      else if hasU a && !hasU b then some b
      else if hasU b && !hasU a then some a
      else none
    else none
  let rec litU (x : Lean.Expr) : Option Lean.Expr :=
    if isAddSub x then (litU (x.getArg! 4)).orElse fun _ => litU (x.getArg! 5)
    else if x.isAppOfArity ``Neg.neg 3 then litU (x.getArg! 2)
    else if isMul x then
      let a := x.getArg! 4
      let b := x.getArg! 5
      if isNumeral a && hasU b then some a else if isNumeral b && hasU a then some b else none
    else none
  (prodU c0).orElse fun _ => litU c0

/-- The read's unit candidates: the non-numeral factors of its products whose cofactor mentions a local, then the
numeral coefficients of locals. -/
partial def readUnits (C : Lean.Expr) : Array Lean.Expr :=
  if isAddSub C then readUnits (C.getArg! 4) ++ readUnits (C.getArg! 5)
  else if C.isAppOfArity ``Neg.neg 3 then readUnits (C.getArg! 2)
  else if isMul C then
    let a := C.getArg! 4
    let b := C.getArg! 5
    if isNumeral a then (if !isMul b && !isAddSub b then #[a] else readUnits b)
    else if isNumeral b then (if !isMul a && !isAddSub a then #[b] else readUnits a)
    else if (slotAtom? b).isSome then #[b]
    else if (slotAtom? a).isSome then #[a]
    else #[b, a]
  else #[]

/-- `x = U * a + b` with `a`, `b` free of `U`, and its proof (syntactic: `+`, `-`, `-·`, products with `U` as a
factor, factors free of `U`). -/
partial def ulin (U x : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let free (y : Lean.Expr) : Bool := (y.find? (· == U)).isNone
  if x == U then
    return some (mkIntLit 1, mkIntLit 0, ← mkAppM ``ulin_self #[U])
  if free x then
    return some (mkIntLit 0, x, ← mkAppM ``ulin_free #[x, U])
  if x.isAppOfArity ``HAdd.hAdd 6 || x.isAppOfArity ``HSub.hSub 6 then
    let some (a1, b1, h1) ← ulin U (x.getArg! 4) | return none
    let some (a2, b2, h2) ← ulin U (x.getArg! 5) | return none
    let isAdd := x.isAppOfArity ``HAdd.hAdd 6
    let a ← mkAppM (if isAdd then ``HAdd.hAdd else ``HSub.hSub) #[a1, a2]
    let b ← mkAppM (if isAdd then ``HAdd.hAdd else ``HSub.hSub) #[b1, b2]
    return some (a, b, ← mkAppM (if isAdd then ``ulin_add else ``ulin_sub) #[h1, h2])
  if x.isAppOfArity ``Neg.neg 3 then
    let some (a1, b1, h1) ← ulin U (x.getArg! 2) | return none
    return some (← mkAppM ``Neg.neg #[a1], ← mkAppM ``Neg.neg #[b1], ← mkAppM ``ulin_neg #[h1])
  if isMul x then
    let p := x.getArg! 4
    let q := x.getArg! 5
    if q == U && free p then return some (p, mkIntLit 0, ← mkAppM ``ulin_mul_r #[p, U])
    if p == U && free q then return some (q, mkIntLit 0, ← mkAppM ``ulin_mul_l #[U, q])
    if free p then
      let some (a1, b1, h1) ← ulin U q | return none
      return some (← mkAppM ``HMul.hMul #[p, a1], ← mkAppM ``HMul.hMul #[p, b1],
        ← mkAppOptM ``ulin_cmul #[some p, none, none, none, none, some h1])
    if free q then
      let some (a1, b1, h1) ← ulin U p | return none
      return some (← mkAppM ``HMul.hMul #[a1, q], ← mkAppM ``HMul.hMul #[b1, q],
        ← mkAppOptM ``ulin_mulc #[some q, none, none, none, none, some h1])
  return none

/-! ## Slot atoms `X / 2 ^ e` of a power-of-two `X = c · 2 ^ t` -/

/-- The power-of-two definitions in context: `(X, c, t, proof of c * 2 ^ t = X)` for every hypothesis
`c * 2 ^ t = X` / `2 ^ t = X` with `c` a numeral. -/
def slotDefs : MetaM (Array (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, X) := ty.eq? | continue
    unless (← inferType X).isConstOf ``Int do continue
    if l.isAppOfArity ``HMul.hMul 6 && isNumeral (l.getArg! 4) then
      let p := l.getArg! 5
      if p.isAppOfArity ``HPow.hPow 6 && (p.getArg! 4).int? == some 2 then
        out := out.push (X, l.getArg! 4, p.getArg! 5, d.toExpr)
    else if l.isAppOfArity ``HPow.hPow 6 && (l.getArg! 4).int? == some 2 then
      let pf ← mkAppM ``Eq.trans #[← mkAppM ``Int.one_mul #[l], d.toExpr]
      out := out.push (X, mkIntLit 1, l.getArg! 5, pf)
  return out

/-- The definition of `X`: from context, or `X` itself of the form `c * 2 ^ t`. -/
def slotDef? (defs : Array (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)) (X : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  if let some (_, c, t, pf) := defs.find? (fun (X', _, _, _) => X' == X) then return some (c, t, pf)
  if X.isAppOfArity ``HMul.hMul 6 && isNumeral (X.getArg! 4) then
    let p := X.getArg! 5
    if p.isAppOfArity ``HPow.hPow 6 && (p.getArg! 4).int? == some 2 then
      return some (X.getArg! 4, p.getArg! 5, ← mkEqRefl X)
  return none

/-- A linear form of a `Nat`/`Int` expression over atoms, with `Int.toNat` and the casts ERASED (a heuristic to
choose which facts to state; every fact is guarded by its exact condition). -/
partial def linOf (e : Lean.Expr) : MetaM (Option (Array (Lean.Expr × Int) × Int)) := do
  if let some n := e.nat? then return some (#[], n)
  if let some n := e.int? then return some (#[], n)
  if let some n ← getIntValue? e then return some (#[], n)
  if let some n ← getNatValue? e then return some (#[], n)
  if (e.isAppOfArity ``Nat.cast 3) then return ← linOf (e.getArg! 2)
  if (e.isAppOfArity ``Int.toNat 1) || (e.isAppOfArity ``Int.ofNat 1) then return ← linOf e.appArg!
  let comb (a b : Array (Lean.Expr × Int) × Int) (s : Int) : Array (Lean.Expr × Int) × Int := Id.run do
    let mut out := a.1
    for (x, k) in b.1 do
      match out.findIdx? (fun (y, _) => y == x) with
      | some i => out := out.set! i (x, out[i]!.2 + s * k)
      | none => out := out.push (x, s * k)
    (out, a.2 + s * b.2)
  if isAddSub e then
    let some a ← linOf (e.getArg! 4) | return none
    let some b ← linOf (e.getArg! 5) | return none
    return some (comb a b (if e.isAppOfArity ``HAdd.hAdd 6 then 1 else -1))
  if e.isAppOfArity ``Neg.neg 3 then
    let some a ← linOf (e.getArg! 2) | return none
    return some (comb (#[], 0) a (-1))
  if isMul e then
    if let some k ← getIntValue? (e.getArg! 4) then
      let some a ← linOf (e.getArg! 5) | return none
      return some (comb (#[], 0) a k)
    if let some k ← getIntValue? (e.getArg! 5) then
      let some a ← linOf (e.getArg! 4) | return none
      return some (comb (#[], 0) a k)
  return some (#[(e, 1)], 0)

/-- `e1 - e2` when the linear forms differ by a constant. -/
def linDiff (e1 e2 : Lean.Expr) : MetaM (Option Int) := do
  let some a ← linOf e1 | return none
  let some b ← linOf e2 | return none
  let mut rest := a.1
  for (x, k) in b.1 do
    match rest.findIdx? (fun (y, _) => y == x) with
    | some i => rest := rest.set! i (x, rest[i]!.2 - k)
    | none => rest := rest.push (x, -k)
  if rest.all (fun (_, k) => k == 0) then return some (a.2 - b.2) else return none

/-- The slot atoms in `e` (no loose bound variables). -/
partial def slotAtoms (e : Lean.Expr) : Array (Lean.Expr × Lean.Expr × Lean.Expr) :=
  let here := if e.hasLooseBVars then #[] else
    match slotAtom? e with
    | some (X, t) => #[(e, X, t)]
    | none => #[]
  let sub := match e with
    | .app f a => slotAtoms f ++ slotAtoms a
    | .lam _ t b _ => slotAtoms t ++ slotAtoms b
    | .forallE _ t b _ => slotAtoms t ++ slotAtoms b
    | .mdata _ b => slotAtoms b
    | _ => #[]
  here ++ sub

/-- Numerals a slot atom is equated to in `e` (`A = n * 1`, `A = n`). -/
partial def slotValues (e : Lean.Expr) : Array (Lean.Expr × Int) :=
  let here : Array (Lean.Expr × Int) := match e.eq? with
    | some (_, l, r) =>
      let r' := if isMul r && (r.getArg! 5).int? == some 1 then r.getArg! 4 else r
      match (slotAtom? l).isSome, r'.int? with
      | true, some n => #[(l, n)]
      | _, _ => #[]
    | none => #[]
  let sub := match e with
    | .app f a => slotValues f ++ slotValues a
    | .forallE _ t b _ => slotValues t ++ slotValues b
    | .mdata _ b => slotValues b
    | _ => #[]
  here ++ sub

/-- The powers `b ^ t` (type `Int`, `b` a numeral) in `e` (no loose bound variables). -/
partial def powAtoms (e : Lean.Expr) : Array Lean.Expr :=
  let here := if !e.hasLooseBVars && e.isAppOfArity ``HPow.hPow 6 && (e.getArg! 0).isConstOf ``Int &&
      isNumeral (e.getArg! 4) then #[e] else #[]
  let sub := match e with
    | .app f a => powAtoms f ++ powAtoms a
    | .lam _ t b _ => powAtoms t ++ powAtoms b
    | .forallE _ t b _ => powAtoms t ++ powAtoms b
    | .mdata _ b => powAtoms b
    | _ => #[]
  here ++ sub

/-- The `if-then-else` terms of type `Int` in `e` whose condition is a comparison `omega` reads. -/
partial def iteAtoms (e : Lean.Expr) : Array Lean.Expr :=
  let arith (c : Lean.Expr) : Bool :=
    let c := if c.isAppOfArity ``Not 1 then c.appArg! else c
    c.isAppOfArity ``Eq 3 || c.isAppOfArity ``LE.le 4 || c.isAppOfArity ``LT.lt 4 || c.isAppOfArity ``Ne 3
  let here := if !e.hasLooseBVars && e.isAppOfArity ``ite 5 && (e.getArg! 0).isConstOf ``Int && arith (e.getArg! 1)
    then #[e] else #[]
  let sub := match e with
    | .app f a => iteAtoms f ++ iteAtoms a
    | .lam _ t b _ => iteAtoms t ++ iteAtoms b
    | .forallE _ t b _ => iteAtoms t ++ iteAtoms b
    | .mdata _ b => iteAtoms b
    | _ => #[]
  here ++ sub

/-- The truncated quotients `Int.tdiv a k` (`k` a numeral) in `e`. -/
partial def tdivAtoms (e : Lean.Expr) : Array Lean.Expr :=
  let here := if !e.hasLooseBVars && e.isAppOfArity ``Int.tdiv 2 && isNumeral (e.getArg! 1) then #[e] else #[]
  let sub := match e with
    | .app f a => tdivAtoms f ++ tdivAtoms a
    | .lam _ t b _ => tdivAtoms t ++ tdivAtoms b
    | .forallE _ t b _ => tdivAtoms t ++ tdivAtoms b
    | .mdata _ b => tdivAtoms b
    | _ => #[]
  here ++ sub

/-- The products of two non-numeral `Int` factors in `e` (no loose bound variables). -/
partial def prodAtoms (e : Lean.Expr) : Array Lean.Expr :=
  let here := if !e.hasLooseBVars && isMul e && (e.getArg! 0).isConstOf ``Int && !isNumeral (e.getArg! 4) &&
      !isNumeral (e.getArg! 5) then #[e] else #[]
  let sub := match e with
    | .app f a => prodAtoms f ++ prodAtoms a
    | .lam _ t b _ => prodAtoms t ++ prodAtoms b
    | .forallE _ t b _ => prodAtoms t ++ prodAtoms b
    | .mdata _ b => prodAtoms b
    | _ => #[]
  here ++ sub

/-! ## Guarded facts

A fact `G₁ ∧ … → C` about the atoms (slot widths, powers, products), its guards decided by `omega` once per goal: all
proved, `C` is added; one refuted, nothing; otherwise the disjunction `¬G₁ ∨ … ∨ C`. Every fact is proved. -/

theorem slot_congr (X : Int) {e1 e2 : Nat} (h : e1 = e2) : X / 2 ^ e2 = X / 2 ^ e1 := by rw [h]

theorem pow_shift {b : Int} {t1 t2 d : Nat} (h : t2 = t1 + d) : b ^ t2 = b ^ d * b ^ t1 := by
  rw [h, Int.pow_add, Int.mul_comm]

theorem pow_shift_or (b : Int) (t1 t2 d : Nat) {k : Int} (hk : b ^ d = k) : t2 ≠ t1 + d ∨ b ^ t2 = k * b ^ t1 := by
  by_cases h : t2 = t1 + d
  · exact Or.inr (by rw [← hk]; exact pow_shift h)
  · exact Or.inl h

theorem pow_congr (b : Int) {t1 t2 : Nat} (h : t1 = t2) : b ^ t1 = b ^ t2 := by rw [h]

theorem pow_congr_or (b : Int) (t1 t2 : Nat) : t1 ≠ t2 ∨ b ^ t1 = b ^ t2 := by
  by_cases h : t1 = t2
  · exact Or.inr (by rw [h])
  · exact Or.inl h

theorem tdiv_or (a b : Int) : ¬ 0 ≤ a ∨ a.tdiv b = a / b := by
  by_cases h : 0 ≤ a
  · exact Or.inr (Int.tdiv_eq_ediv_of_nonneg h)
  · exact Or.inl h

theorem ite_pos_or {c : Prop} [Decidable c] (a b : Int) : ¬ c ∨ (if c then a else b) = a := by
  by_cases h : c
  · exact Or.inr (if_pos h)
  · exact Or.inl h

theorem ite_neg_or {c : Prop} [Decidable c] (a b : Int) : c ∨ (if c then a else b) = b := by
  by_cases h : c
  · exact Or.inl h
  · exact Or.inr (if_neg h)

theorem pow_zero_of {b : Int} {t : Nat} (h : t = 0) : b ^ t = 1 := by rw [h, Int.pow_zero]

theorem mul_zero_of {g : Int} (y : Int) (h : g = 0) : g * y = 0 := by rw [h, Int.zero_mul]

structure Cand where
  guards : Array Lean.Expr
  concl : Lean.Expr
  mkp : Array Lean.Expr → MetaM Lean.Expr
  orFact : MetaM Lean.Expr

/-- Run `x` within `lim` thousand heartbeats (in `maxHeartbeats` units) of its own (a heartbeat timeout is a runtime
exception). -/
def capped {α : Type} (lim : Nat) (x : TacticM α) : TacticM α := do
  let now ← IO.getNumHeartbeats
  withTheReader Core.Context (fun c => { c with maxHeartbeats := lim * 1000 * 1000, initHeartbeats := now }) x

/-- `omega` proves `p` in `g`'s context: the proof, or `none` (state restored). -/
def proveBy (g : MVarId) (p : Lean.Expr) (cap : Nat := 4) : TacticM (Option Lean.Expr) := do
  let saved ← saveState
  let m ← g.withContext (mkFreshExprSyntheticOpaqueMVar p)
  setGoals [m.mvarId!]
  let ok ← tryCatchRuntimeEx
      (do
        capped cap (evalTactic (← `(tactic| omega)))
        pure (← getGoals).isEmpty)
      fun _ => pure false
  if ok then return some (← instantiateMVars m)
  saved.restore
  return none

def assertIntro (g : MVarId) (ty p : Lean.Expr) : MetaM MVarId := do
  let g' ← g.assert `hfact ty p
  let (_, g'') ← g'.intro1P
  return g''

/-- The candidate facts of the atoms in `es` (closed in `g`'s context). -/
def candidates (g : MVarId) (es hyps : Array Lean.Expr) : MetaM (Array Cand) := g.withContext do
  let defs ← slotDefs
  let mut atoms : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]
  for e in es do
    for x in slotAtoms e do
      unless atoms.any (·.1 == x.1) do atoms := atoms.push x
  let mut out : Array Cand := #[]
  let mut withDef : Array (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := #[]
  for (A, X, t) in atoms do
    if let some (c, tt, pf) ← slotDef? defs X then
      withDef := withDef.push (A, X, t, c, tt, pf)
      let hc ← mkDecideProof (← mkAppM ``LE.le #[mkIntLit 0, c])
      let p ← mkAppOptM ``slot_nonneg #[some c, some X, some tt, some pf, some hc, some t]
      let ty ← inferType p
      out := out.push { guards := #[], concl := ty, mkp := fun _ => pure p, orFact := pure p }
      let p ← mkAppOptM ``slot_le #[some c, some X, some tt, some pf, some hc, some t]
      let ty ← inferType p
      out := out.push { guards := #[], concl := ty, mkp := fun _ => pure p, orFact := pure p }
      let concl ← mkAppM ``LE.le #[c, A]
      out := out.push { guards := #[← mkAppM ``LE.le #[t, tt]], concl := concl,
                        mkp := fun ps => mkAppOptM ``slot_ge #[some c, some X, some tt, some pf, some hc, some t, some ps[0]!],
                        orFact := mkAppOptM ``slot_ge_or #[some c, some X, some tt, some pf, some hc, some t] }
  for i in [0:withDef.size] do
    for j in [0:withDef.size] do
      if i == j then continue
      let (A1, X1, e1, _, tt, pf) := withDef[i]!
      let (A2, X2, e2, _, _, _) := withDef[j]!
      unless X1 == X2 do continue
      let d ← match ← linDiff e1 e2 with
        | some d => pure d
        | none => pure (-100)
      if d == -100 && i < j then
        let concl ← mkEq A2 A1
        out := out.push { guards := #[← mkEq e1 e2], concl := concl,
                          mkp := fun ps => mkAppOptM ``slot_congr #[some X1, some e1, some e2, some ps[0]!],
                          orFact := mkAppM ``slot_congr_or #[X1, e1, e2] }
      else if d == 0 && i < j then
        let concl ← mkEq A2 A1
        out := out.push { guards := #[← mkEq e1 e2], concl := concl,
                          mkp := fun ps => mkAppOptM ``slot_congr #[some X1, some e1, some e2, some ps[0]!],
                          orFact := mkAppM ``slot_congr_or #[X1, e1, e2] }
      else if 0 < d && d ≤ 3 then
        let k := mkIntLit (2 ^ d.toNat)
        let dN := mkNatLit d.toNat
        let hk ← mkDecideProof (← mkEq (← mkAppM ``HPow.hPow #[mkIntLit 2, dN]) k)
        let concl ← mkEq A2 (← mkAppM ``HMul.hMul #[k, A1])
        let g1 ← mkEq e1 (← mkAppM ``HAdd.hAdd #[e2, dN])
        let g2 ← mkAppM ``LE.le #[e1, tt]
        out := out.push { guards := #[g1, g2], concl := concl,
                          mkp := fun ps => do
                            let h ← mkAppOptM ``slot_shift #[none, some X1, none, some pf, some e1, some e2, some dN,
                              some ps[0]!, some ps[1]!]
                            -- `2 ^ d` to the numeral
                            let mot ← withLocalDeclD `z (mkConst ``Int) fun z => do
                              mkLambdaFVars #[z] (← mkEq A2 (← mkAppM ``HMul.hMul #[z, A1]))
                            mkEqMP (← mkCongrArg mot hk) h,
                          orFact := mkAppOptM ``slot_shift_or #[none, some X1, none, some pf, some e1, some e2, some dN,
                            some k, some hk] }
  -- the values the plans ask for (`A = n * 1`)
  let mut vals : Array (Lean.Expr × Int) := #[]
  for e in es do
    for v in slotValues e do
      unless vals.any (fun w => w.1 == v.1 && w.2 == v.2) do vals := vals.push v
  for (A, n) in vals do
    let some (_, X, e, c, tt, pf) := withDef.find? (·.1 == A) | continue
    let some cv ← getIntValue? c | continue
    if cv ≤ 0 || n % cv != 0 then continue
    let q := n / cv
    let mut dd : Option Nat := none
    for k in [0:31] do
      if 2 ^ k == q then dd := some k
    let some d := dd | continue
    let dN := mkNatLit d
    let hn ← mkDecideProof (← mkEq (← mkAppM ``HMul.hMul #[c, ← mkAppM ``HPow.hPow #[mkIntLit 2, dN]]) (mkIntLit n))
    let concl ← mkEq A (mkIntLit n)
    out := out.push { guards := #[← mkEq tt (← mkAppM ``HAdd.hAdd #[e, dN])], concl := concl,
                      mkp := fun ps => mkAppOptM ``slot_val #[some c, some X, some tt, some pf, some e, some dN,
                        some (mkIntLit n), some hn, some ps[0]!],
                      orFact := mkAppOptM ``slot_val_or #[some c, some X, some tt, some pf, some e, some dN,
                        some (mkIntLit n), some hn] }
  -- powers of a numeral base
  let mut pows : Array (Lean.Expr × Int × Lean.Expr) := #[]
  for e in es do
    for x in powAtoms e do
      if pows.any (·.1 == x) then continue
      if let some b ← getIntValue? (x.getArg! 4) then
        if 1 ≤ b then pows := pows.push (x, b, x.getArg! 5)
  for (x, _, t) in pows do
    let bE := x.getArg! 4
    let hb ← mkDecideProof (← mkAppM ``LT.lt #[mkIntLit 0, bE])
    let p ← mkAppOptM ``Int.pow_pos #[some bE, some t, some hb]
    let ty ← inferType p
    out := out.push { guards := #[], concl := ty, mkp := fun _ => pure p, orFact := pure p }
    let concl ← mkEq x (mkIntLit 1)
    out := out.push { guards := #[← mkEq t (mkNatLit 0)], concl := concl,
                      mkp := fun ps => mkAppOptM ``pow_zero_of #[some bE, some t, some ps[0]!],
                      orFact := mkAppM ``pow_zero_or #[bE, t] }
  for (x1, b1, t1) in pows do
    for (x2, b2, t2) in pows do
      let bE1 := x1.getArg! 4
      let bE2 := x2.getArg! 4
      if b1 < b2 && t1 == t2 then
        let h0 ← mkDecideProof (← mkAppM ``LE.le #[mkIntLit 0, bE1])
        let h ← mkDecideProof (← mkAppM ``LE.le #[bE1, bE2])
        let p ← mkAppOptM ``LeanModels.Sv.CombView.pow_le_pow_base #[some bE1, some bE2, some h0, some h, some t1]
        let ty ← inferType p
        out := out.push { guards := #[], concl := ty, mkp := fun _ => pure p, orFact := pure p }
      if b1 == b2 && x1 != x2 && (← linDiff t2 t1).isNone && x1.lt x2 then
        let concl ← mkEq x1 x2
        out := out.push { guards := #[← mkEq t1 t2], concl := concl,
                          mkp := fun ps => mkAppOptM ``pow_congr #[some bE1, some t1, some t2, some ps[0]!],
                          orFact := mkAppM ``pow_congr_or #[bE1, t1, t2] }
      if b1 == b2 && x1 != x2 then
        let some d ← linDiff t2 t1 | continue
        if 0 < d && d ≤ 3 then
          let dN := mkNatLit d.toNat
          let k := mkIntLit (b1 ^ d.toNat)
          let hk ← mkDecideProof (← mkEq (← mkAppM ``HPow.hPow #[bE1, dN]) k)
          let concl ← mkEq x2 (← mkAppM ``HMul.hMul #[k, x1])
          out := out.push { guards := #[← mkEq t2 (← mkAppM ``HAdd.hAdd #[t1, dN])], concl := concl,
                            mkp := fun ps => do
                              let h ← mkAppOptM ``pow_shift #[some bE1, some t1, some t2, some dN, some ps[0]!]
                              let mot ← withLocalDeclD `z (mkConst ``Int) fun z => do
                                mkLambdaFVars #[z] (← mkEq x2 (← mkAppM ``HMul.hMul #[z, x1]))
                              mkEqMP (← mkCongrArg mot hk) h,
                            orFact := mkAppOptM ``pow_shift_or #[some bE1, some t1, some t2, some dN, some k, some hk] }
  -- truncated quotients of a non-negative numerator: the floor ones
  let mut tds : Array Lean.Expr := #[]
  for e in hyps do
    for x in tdivAtoms e do
      unless tds.contains x do tds := tds.push x
  for x in tds do
    let aE := x.getArg! 0
    let bE := x.getArg! 1
    let concl ← mkEq x (← mkAppM ``HDiv.hDiv #[aE, bE])
    out := out.push { guards := #[← mkAppM ``LE.le #[mkIntLit 0, aE]], concl := concl,
                      mkp := fun ps => mkAppOptM ``Int.tdiv_eq_ediv_of_nonneg #[some aE, some bE, some ps[0]!],
                      orFact := mkAppM ``tdiv_or #[aE, bE] }
  -- `if-then-else` terms: the branch their condition decides
  let mut ites : Array Lean.Expr := #[]
  for e in es do
    for x in iteAtoms e do
      unless ites.contains x do ites := ites.push x
  for x in ites do
    let c := x.getArg! 1
    let inst := x.getArg! 2
    let a := x.getArg! 3
    let b := x.getArg! 4
    out := out.push { guards := #[c], concl := ← mkEq x a,
                      mkp := fun ps => mkAppOptM ``if_pos #[some c, some inst, some ps[0]!, some (mkConst ``Int), some a, some b],
                      orFact := mkAppOptM ``ite_pos_or #[some c, some inst, some a, some b] }
    out := out.push { guards := #[mkNot c], concl := ← mkEq x b,
                      mkp := fun ps => mkAppOptM ``if_neg #[some c, some inst, some ps[0]!, some (mkConst ``Int), some a, some b],
                      orFact := mkAppOptM ``ite_neg_or #[some c, some inst, some a, some b] }
  -- products of two non-numeral factors
  let mut prods : Array Lean.Expr := #[]
  for e in hyps do
    for x in prodAtoms e do
      unless prods.contains x do prods := prods.push x
  for x in prods do
    let gE := x.getArg! 4
    let yE := x.getArg! 5
    let concl ← mkAppM ``LE.le #[mkIntLit 0, x]
    out := out.push { guards := #[← mkAppM ``LE.le #[mkIntLit 0, gE], ← mkAppM ``LE.le #[mkIntLit 0, yE]], concl := concl,
                      mkp := fun ps => mkAppM ``Int.mul_nonneg #[ps[0]!, ps[1]!],
                      orFact := mkAppM ``LeanModels.Sv.CombView.mul_nonneg_or #[gE, yE] }
    let concl ← mkEq x (mkIntLit 0)
    out := out.push { guards := #[← mkEq gE (mkIntLit 0)], concl := concl,
                      mkp := fun ps => mkAppM ``mul_zero_of #[yE, ps[0]!],
                      orFact := mkAppM ``mul_zero_or #[gE, yE] }
  return out

/-- Add the facts of the candidates to `g`, each decided against the context as it grows; the undecided ones are
returned (`orAll`: added as disjunctions instead). -/
def addFacts (g : MVarId) (cands : Array Cand) (orAll : Bool := false) : TacticM (MVarId × Array Cand) := do
  let mut g := g
  let mut pend : Array Cand := #[]
  for c in cands do
    let gw := g
    let mut pfs : Array Lean.Expr := #[]
    let mut allOk := true
    for gd in c.guards do
      match ← proveBy gw gd with
      | some p => pfs := pfs.push p
      | none => allOk := false; break
    if allOk then
      let p ← gw.withContext (c.mkp pfs)
      g ← assertIntro gw c.concl p
    else
      let mut vac := false
      for gd in c.guards do
        if (← proveBy gw (mkNot gd)).isSome then
          vac := true
          break
      unless vac do
        if orAll then
          let p ← gw.withContext c.orFact
          g ← assertIntro gw (← gw.withContext (inferType p)) p
        else pend := pend.push c
  return (g, pend)

/-! ## The plan of one disjunct -/

inductive Item where
  | wit (x : FVarId)
  | atom (p : Lean.Expr)
  | win (n : Lean.Expr)

partial def spine {α : Type} (d : Lean.Expr) (items : Array Item)
    (k : Array Item → MetaM α) : MetaM α := do
  if d.isAppOfArity ``Exists 2 then
    unless (← whnfR d.appFn!.appArg!).isConstOf ``Nat do
      throwError "sv_cover: a binder that is not a Nat"
    let .lam n t b bi := d.appArg! | throwError "sv_cover: a quantifier that is not a lambda"
    withLocalDecl n bi t fun x => spine (b.instantiate1 x) (items.push (.wit x.fvarId!)) k
  else if d.isAppOfArity ``And 2 then
    if (matchWin d).isSome then k (items.push (.win d))
    else spine d.appArg! (items.push (.atom d.appFn!.appArg!)) k
  else k (items.push (.atom d))

/-- How a window is proved: `rmN_win_suff` (classic) or `rmN_win_unit` with its decomposition. -/
structure UnitData where
  U : Lean.Expr
  Y : Lean.Expr
  u : Lean.Expr
  a : Lean.Expr
  b : Lean.Expr
  ar : Lean.Expr
  br : Lean.Expr
  kw : Lean.Expr
  kr : Lean.Expr
  hc0 : Lean.Expr
  hC : Lean.Expr
deriving Inhabited

structure Plan where
  ws : Array Lean.Expr
  slots : Array (Lean.Expr × Option Lean.Expr)
  /-- per window (in order): the leaf equations of its row, and its unit decomposition if any -/
  wins : Array (Array (Lean.Expr × Lean.Expr) × Option UnitData)
  novel : Bool
deriving Inhabited

def Plan.inL (p : Plan) : Array Lean.Expr := p.slots.filterMap fun (c, pf) => if pf.isNone then some c else none

def Plan.fullHs (p : Plan) (pr : Array Lean.Expr) : Array Lean.Expr := Id.run do
  let mut out := #[]
  let mut i := 0
  for (_, pf) in p.slots do
    match pf with
    | some x => out := out.push x
    | none => out := out.push pr[i]!; i := i + 1
  pure out

/-- Forced bounds: `E ≤ x` with `x < E + 1` (or `1 + E`, or `x ≤ E`) give the equation `x = E`. -/
def forcedEqs (unk : Array FVarId) (atoms : Array Lean.Expr) : Array (Lean.Expr × Lean.Expr) := Id.run do
  let mut out := #[]
  for a in atoms do
    let some (E, x) := cmpSides? ``LE.le a | continue
    unless unk.any (x.containsFVar ·) do continue
    let forced := atoms.any fun b =>
      match cmpSides? ``LT.lt b with
      | some (x', hi) =>
        x' == x && hi.isAppOfArity ``HAdd.hAdd 6 &&
          ((hi.getArg! 4 == E && (hi.getArg! 5).int? == some 1) ||
           (hi.getArg! 5 == E && (hi.getArg! 4).int? == some 1))
      | none => match cmpSides? ``LE.le b with
        | some (x', E') => x' == x && E' == E
        | none => false
    if forced then out := out.push (x, E)
  pure out

def mkIntLe (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``LE.le #[a, b]

/-- The value of a closed `Int`/`Nat` term (by kernel-style reduction), if it is small. -/
def closedInt? (e : Lean.Expr) : MetaM (Option Int) := do
  if e.hasFVar || e.hasMVar then return none
  try
    let r ← withTransparency .default <| Meta.reduce e (skipTypes := true)
    if let some n ← getIntValue? r then return some n
    if let some n ← getNatValue? r then return some n
    if let some n := r.rawNatLit? then return some n
    if r.isAppOfArity ``Int.ofNat 1 then
      let a := r.appArg!
      if let some n := a.rawNatLit? then return some n
      if let some n ← getNatValue? a then return some n
    if r.isAppOfArity ``Int.negSucc 1 then
      let a := r.appArg!
      if let some n := a.rawNatLit? then return some (-((n : Int) + 1))
    return none
  catch _ => return none

/-- `a = ρ * aY + rem` for `a` linear in the unknowns: `aY` with every coefficient divided by `ρ` (each must divide), and
`rem` the constant's remainder; `none` otherwise. -/
def linSplit (a : Lean.Expr) (unk : Array FVarId) (ρ : Int) : MetaM (Option (Lean.Expr × Int)) := do
  let some (ts, c) ← linOf a | return none
  let mut aY : Lean.Expr := mkIntLit 0
  for (x, k) in ts do
    unless x.isFVar && unk.contains x.fvarId! do return none
    if k % ρ != 0 then return none
    let xi ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, x]
    aY ← mkAppM ``HAdd.hAdd #[aY, ← mkAppM ``HMul.hMul #[mkIntLit (k / ρ), xi]]
  let rem := c % ρ
  aY ← mkAppM ``HAdd.hAdd #[aY, mkIntLit ((c - rem) / ρ)]
  return some (aY, rem)

def planOf (d : Lean.Expr) : MetaM Plan :=
  spine d #[] fun items => do
    let unk := items.filterMap fun | .wit x => some x | _ => none
    let hasWin := items.any fun | .win _ => true | _ => false
    let atoms := items.filterMap fun | .atom a => some a | _ => none
    let mut novel := false
    -- the classic equations (unchanged, in the classic order)
    let mut eqs : Array (Lean.Expr × Lean.Expr) := #[]
    for it in items.reverse do
      match it with
      | .win n =>
        let some p := matchWin n | pure ()
        let rowHasUnk := unk.any (fun v => p.r.containsFVar v)
        let rp := if rowHasUnk then rowPairs p.r p.R else #[(p.r, p.R)]
        if rp.size > 1 then novel := true
        eqs := eqs ++ rp
        if (← getNatValue? p.wd) == some 1 && !hasProd p.C then
          let eI ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, p.e]
          eqs := eqs.push (p.c0, ← mkAppM ``HAdd.hAdd #[p.C, eI])
      | .atom a =>
        if !hasWin then
          if let some (l, r) := cmpSides? ``LE.le a then
            if unk.any (l.containsFVar ·) && !unk.any (r.containsFVar ·) then eqs := eqs.push (l, r)
            else if unk.any (r.containsFVar ·) && !unk.any (l.containsFVar ·) then eqs := eqs.push (r, l)
      | .wit _ => pure ()
    let mut sol ← solvePartial unk (unk.map fun _ => none) eqs
    -- forced bounds (`E ≤ x < E + 1`; a natural `x < B` with `B` a closed term of value at most `1`)
    if sol.any Option.isNone then
      let fe := forcedEqs unk atoms
      unless fe.isEmpty do
        eqs := eqs ++ fe
        sol ← solvePartial unk sol eqs
        novel := true
    if sol.any Option.isNone then
      let substS (x : Lean.Expr) : Lean.Expr := Id.run do
        let mut y := x
        for i in [0:unk.size] do
          if let some w := sol[i]! then y := y.replaceFVar (mkFVar unk[i]!) w
        pure y
      for a in atoms do
        let some (x, B) := cmpSides? ``LT.lt a | continue
        let x := substS x
        let B := substS B
        unless x.isAppOfArity ``Nat.cast 3 && (x.getArg! 2).isFVar && unk.contains (x.getArg! 2).fvarId! do continue
        if B.hasFVar || B.hasMVar then continue
        let some v ← closedInt? B | continue
        if v ≤ 1 then
          eqs := eqs.push (x, mkIntLit 0)
          novel := true
      sol ← solvePartial unk sol eqs
    -- unit windows: windows whose column still mentions an unknown, or whose read holds a product
    let wins := items.filterMap fun | .win n => matchWin n | _ => none
    let mut units : Array (Option UnitData) := wins.map fun _ => none
    let subst (sol : Array (Option Lean.Expr)) (x : Lean.Expr) : Lean.Expr := Id.run do
      let mut y := x
      for i in [0:unk.size] do
        if let some w := sol[i]! then y := y.replaceFVar (mkFVar unk[i]!) w
      pure y
    let mut progress := true
    while progress do
      progress := false
      for wi in [0:wins.size] do
        if units[wi]!.isSome then continue
        let p := wins[wi]!
        let c0 := subst sol p.c0
        let unsolved := (Array.range unk.size).filterMap fun i => if sol[i]!.isNone then some unk[i]! else none
        let colUnk := unsolved.any (c0.containsFVar ·)
        unless colUnk || (hasProd p.C && unk.any (p.c0.containsFVar ·)) do continue
        let us := if colUnk then unsolved else unk
        let some U := findUnit us (if colUnk then c0 else p.c0) | continue
        let c0u := if colUnk then c0 else p.c0
        let some (a, b, hc0) ← ulin U c0u | continue
        -- the read's unit
        let cands := readUnits p.C ++ (if (p.C.find? (· == U)).isSome then #[U] else #[])
        -- a read with no unit of its own (a free offset) gives no slot equation
        if cands.isEmpty then continue
        let mut pick : Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := none  -- Y, u, kw, kr
        for Y in cands do
          if pick.isSome then break
          if Y == U then pick := some (Y, U, mkIntLit 1, mkIntLit 1); break
          match slotAtom? U, slotAtom? Y with
          | some (X1, e1), some (X2, e2) =>
            if X1 == X2 then
              if let some dd ← linDiff e1 e2 then
                if 0 ≤ dd && dd ≤ 3 then pick := some (Y, U, mkIntLit 1, mkIntLit (2 ^ dd.toNat))
                else if dd < 0 && -dd ≤ 3 then pick := some (Y, Y, mkIntLit (2 ^ (-dd).toNat), mkIntLit 1)
          | some _, none =>
            if let some n ← getIntValue? Y then pick := some (Y, mkIntLit 1, mkIntLit n, mkIntLit n)
          | none, some _ =>
            if let some n ← getIntValue? U then pick := some (Y, mkIntLit 1, mkIntLit n, mkIntLit n)
          | none, none =>
            match ← getIntValue? U, ← getIntValue? Y with
            | some n, some m => pick := some (Y, mkIntLit 1, mkIntLit n, mkIntLit m)
            | _, _ => pure ()
        let (Y, u, kw, kr) := pick.getD (U, U, mkIntLit 1, mkIntLit 1)
        let some (a', b', hC) ← ulin Y p.C | continue
        -- the read's unit a multiple `ρ` of the writer's: the writer's column in the read's unit, the multiples of its
        -- own unit below `ρ` kept in the rest (an offset inside the read's slot)
        let mut (U, u, a, b, kw, kr, hc0) := (U, u, a, b, kw, kr, hc0)
        if let some ρ := kr.int? then
          if 1 < ρ && kw.int? == some 1 && u == U then
            if let some (aY, rem) ← linSplit a us ρ then
              let ha ← mkFreshExprSyntheticOpaqueMVar (← mkEq a (← mkAppM ``HAdd.hAdd #[← mkAppM ``HMul.hMul #[mkIntLit ρ, aY], mkIntLit rem]))
              let ok ← try
                  let gs ← Lean.Elab.Term.TermElabM.run' (Lean.Elab.Tactic.run ha.mvarId! (Lean.Elab.Tactic.evalTactic (← `(tactic| omega))))
                  pure gs.isEmpty
                catch _ => pure false
              if ok then
                let U' ← mkAppM ``HMul.hMul #[mkIntLit ρ, U]
                let b' ← mkAppM ``HAdd.hAdd #[← mkAppM ``HMul.hMul #[U, mkIntLit rem], b]
                hc0 ← mkAppM ``ulin_regroup #[hc0, ← instantiateMVars ha]
                U := U'; u := U'; a := aY; b := b'; kw := mkIntLit 1; kr := mkIntLit 1
        units := units.set! wi (some (UnitData.mk U Y u a b a' b' kw kr hc0 hC))
        eqs := eqs.push (← mkAppM ``HMul.hMul #[kw, a], ← mkAppM ``HMul.hMul #[kr, a'])
        novel := true
        progress := true
      if progress then sol ← solvePartial unk sol eqs
    if sol.any Option.isNone then throwError "sv_cover: cannot solve the witnesses of a disjunct"
    let mut ws : Array Lean.Expr := #[]
    for w in sol.map Option.get! do
      match ← closedInt? w with
      | some n => if 0 ≤ n then ws := ws.push (mkNatLit n.toNat) else ws := ws.push w
      | none => ws := ws.push w
    let fv := unk.map mkFVar
    let sub (x : Lean.Expr) := x.replaceFVars fv ws
    let mut comps : Array (Lean.Expr × Option Lean.Expr) := #[]
    let mut winPlans : Array (Array (Lean.Expr × Lean.Expr) × Option UnitData) := #[]
    let mut wi := 0
    let intTy := mkConst ``Int
    let zero := mkIntLit 0
    for it in items do
      match it with
      | .wit _ => pure ()
      | .atom a => comps := comps.push (sub a, none)
      | .win n =>
        let some p := matchWin n | throwError "sv_cover: internal error (window)"
        let rowHasUnk := unk.any (fun v => p.r.containsFVar v)
        let rp := (if rowHasUnk then rowPairs p.r p.R else #[(p.r, p.R)]).map fun (l, r) => (sub l, sub r)
        for (l, r) in rp do
          if l == r then comps := comps.push (← mkEq l r, some (← mkEqRefl l))
          else comps := comps.push (← mkEq l r, none)
        let eI ← mkAppOptM ``Nat.cast #[intTy, none, sub p.e]
        let wdI ← mkAppOptM ``Nat.cast #[intTy, none, sub p.wd]
        match units[wi]! with
        | none =>
          let c0 := sub p.c0
          let C := sub p.C
          let ce ← mkAppM ``HAdd.hAdd #[C, eI]
          let nonneg (x : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
            let pr ← mkIntLe zero x
            if x.isAppOfArity ``Nat.cast 3 then return (pr, some (← mkAppM ``Int.natCast_nonneg #[x.getArg! 2]))
            else return (pr, none)
          comps := comps ++ #[← nonneg c0, ← nonneg C, (← mkIntLe c0 ce, none),
            (← mkAppM ``LT.lt #[ce, ← mkAppM ``HAdd.hAdd #[c0, wdI]], none)]
          winPlans := winPlans.push (rp, none)
        | some ud =>
          let ud : UnitData := UnitData.mk (sub ud.U) (sub ud.Y) (sub ud.u) (sub ud.a) (sub ud.b) (sub ud.ar)
            (sub ud.br) ud.kw ud.kr (sub ud.hc0) (sub ud.hC)
          let triv (lhs k u : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
            let ty ← mkEq lhs (← mkAppM ``HMul.hMul #[k, u])
            if lhs == u && k.int? == some 1 then return (ty, some (← mkEqSymm (← mkAppM ``Int.one_mul #[u])))
            if (← getIntValue? lhs).isSome && (← getIntValue? u).isSome then return (ty, some (← mkDecideProof ty))
            return (ty, none)
          let hY0 ← mkIntLe zero ud.Y
          let hY0p : Option Lean.Expr ← if (← getIntValue? ud.Y).isSome then pure (some (← mkDecideProof hY0)) else pure none
          let hb0 ← mkIntLe zero ud.br
          let hb0p : Option Lean.Expr ← if (← getIntValue? ud.br).isSome then pure (some (← mkDecideProof hb0)) else pure none
          comps := comps ++ #[← triv ud.U ud.kw ud.u, ← triv ud.Y ud.kr ud.u,
            (← mkEq (← mkAppM ``HMul.hMul #[ud.kw, ud.a]) (← mkAppM ``HMul.hMul #[ud.kr, ud.ar]), none),
            (hY0, hY0p), (← mkIntLe zero ud.ar, none), (hb0, hb0p),
            (← mkIntLe ud.b (← mkAppM ``HAdd.hAdd #[ud.br, eI]), none),
            (← mkAppM ``LT.lt #[← mkAppM ``HAdd.hAdd #[ud.br, eI], ← mkAppM ``HAdd.hAdd #[ud.b, wdI]], none)]
          winPlans := winPlans.push (rp, some ud)
        wi := wi + 1
    pure { ws := ws, slots := comps, wins := winPlans, novel := novel }

def mkAndAll (cs : Array Lean.Expr) : Lean.Expr :=
  cs.foldr (init := mkConst ``True) fun c acc => if acc.isConstOf ``True then c else mkApp2 (mkConst ``And) c acc

def projs (h : Lean.Expr) (n : Nat) : MetaM (Array Lean.Expr) := do
  let mut out : Array Lean.Expr := #[]
  let mut cur := h
  for i in [0:n] do
    if i + 1 == n then out := out.push cur
    else
      out := out.push (← mkAppM ``And.left #[cur])
      cur ← mkAppM ``And.right #[cur]
  pure out

/-- The proof of the disjunct `d` from the proofs `hs` of the components of its condition. -/
partial def build (d : Lean.Expr) (ws : List Lean.Expr) (wps : List (Array (Lean.Expr × Lean.Expr) × Option UnitData))
    (hs : List Lean.Expr) : MetaM (Lean.Expr × List Lean.Expr × List Lean.Expr) := do
  if d.isAppOfArity ``Exists 2 then
    let w :: ws' := ws | throwError "sv_cover: internal error (witnesses)"
    let .lam _ _ b _ := d.appArg! | throwError "sv_cover: internal error (lambda)"
    let body := b.instantiate1 w
    let (pf, ws'', hs') ← build body ws' wps hs
    return (mkApp4 (mkConst ``Exists.intro d.getAppFn.constLevels!) d.appFn!.appArg! d.appArg! w pf, ws'', hs')
  else if d.isAppOfArity ``And 2 then
    if let some p := matchWin d then
      let (rp, ud?) :: _ := wps | throwError "sv_cover: internal error (window plans)"
      let (hr, hs1) ← if rp.size == 1 then
          (match hs with
           | h :: _ => pure (h, ([] : List Lean.Expr))
           | [] => throwError "sv_cover: internal error (row)")
        else rowProof p.r p.R (hs.take rp.size)
      unless hs1.isEmpty do throwError "sv_cover: internal error (row components)"
      let hs := hs.drop rp.size
      match ud? with
      | none =>
        match hs with
        | h0 :: hC :: h1 :: h2 :: hs' =>
          let pf ← mkAppOptM ``LeanModels.Sv.CombCover.rmN_win_suff #[some p.W, some p.r, some p.c0, some p.R, some p.C,
            some p.e, some p.wd, some hr, some h0, some hC, some h1, some h2]
          return (pf, ws, hs')
        | _ => throwError "sv_cover: internal error (window components)"
      | some ud =>
        match hs with
        | hU :: hY :: ha :: hY0 :: ha0 :: hb0 :: h1 :: h2 :: hs' =>
          let pf ← mkAppOptM ``rmN_win_unit #[some p.W, some p.r, some p.R, some p.c0, some p.C, some ud.U, some ud.Y,
            some ud.u, some ud.a, some ud.ar, some ud.b, some ud.br, some ud.kw, some ud.kr, some p.e, some p.wd,
            some ud.hc0, some ud.hC, some hr, some hU, some hY, some ha, some hY0, some ha0, some hb0, some h1, some h2]
          return (pf, ws, hs')
        | _ => throwError "sv_cover: internal error (unit window components)"
    else
      let h :: hs' := hs | throwError "sv_cover: internal error (components)"
      let (pf, ws', hs'') ← build d.appArg! ws wps hs'
      return (mkApp4 (mkConst ``And.intro) d.appFn!.appArg! d.appArg! h pf, ws', hs'')
  else
    let h :: hs' := hs | throwError "sv_cover: internal error (components)"
    return (h, ws, hs')

partial def readOf? (d : Lean.Expr) : Option Lean.Expr :=
  if d.isAppOfArity ``Exists 2 then
    match d.appArg! with
    | .lam _ _ b _ => readOf? b
    | _ => none
  else if d.isAppOfArity ``And 2 then
    match matchWin d with
    | some p => some (mkApp3 (mkConst ``LeanModels.Sv.CombView.rmN) p.W p.R p.C)
    | none => (readOf? d.appFn!.appArg!).orElse fun _ => readOf? d.appArg!
  else none

/-- The prefix of the rule's report of a goal it reads and cannot prove. -/
def diagPrefix : String := "sv_cover (slot windows): the cell is not covered"

def omegaOk (g : MVarId) (cap : Nat := 20) : TacticM Bool := do
  let saved ← saveState
  setGoals [g]
  let ok ← tryCatchRuntimeEx
      (do
        capped cap (evalTactic (← `(tactic| first | omega | trivial)))
        pure (← getGoals).isEmpty)
      fun _ => pure false
  unless ok do saved.restore
  pure ok

/-- Prove the linear goal `g` from the context (the negations `¬ D` of the writers ruled out before it are hypotheses):
one `omega` call, then one with the pending facts (decided in this context, the rest as disjunctions). -/
def proveLin (pend : Array Cand) (g : MVarId) (_negs : List (FVarId × Lean.Expr)) : TacticM Bool := do
  if ← omegaOk g 30 then return true
  if pend.isEmpty then return false
  let saved ← saveState
  let (g', _) ← addFacts g pend (orAll := true)
  if ← omegaOk g' 60 then return true
  saved.restore
  return false

/-- Prove the components `cs` of the conjunction `g` (`c₁ ∧ … ∧ cₙ`), the equations first, each with the ones proved
before it as hypotheses (`known`: proofs found before); the first component that fails is returned. -/
def proveAll (pend : Array Cand) (g : MVarId) (cs : Array Lean.Expr) (known : Array (Option Lean.Expr)) :
    TacticM (Option Lean.Expr) := do
  let isEq (c : Lean.Expr) : Bool := c.isAppOfArity ``Eq 3
  let order := (Array.range cs.size).filter (fun k => isEq cs[k]!) ++ (Array.range cs.size).filter (fun k => !isEq cs[k]!)
  let mut cur := g
  let mut hyps : Array (Option FVarId) := Array.replicate cs.size none
  for k in order do
    let c := cs[k]!
    let p ← match known[k]?.join with
      | some p => pure p
      | none =>
        let gc ← cur.withContext (mkFreshExprSyntheticOpaqueMVar c)
        unless ← proveLin pend gc.mvarId! [] do return some c
        instantiateMVars gc
    let (h, cur') ← (← cur.assert `hc c p).intro1P
    hyps := hyps.set! k (some h)
    cur := cur'
  -- the conjunction in its own order, from the hypotheses
  cur.withContext do
    let fs := hyps.map fun h? => mkFVar h?.get!
    let n := fs.size
    if n == 0 then
      cur.assign (mkConst ``True.intro)
    else
      let mut acc := fs[n - 1]!
      for k' in [0:n - 1] do
        let k := n - 2 - k'
        acc ← mkAppM ``And.intro #[fs[k]!, acc]
      cur.assign acc
  return none

/-- Is `L` refuted by the hypotheses alone? -/
def refuted (g : MVarId) (L : Lean.Expr) : TacticM Bool := g.withContext do
  let saved ← saveState
  let m ← mkFreshExprSyntheticOpaqueMVar (mkForall `h .default L (mkConst ``False))
  let (_, m') ← m.mvarId!.intro1
  if ← omegaOk m' 6 then return true
  saved.restore
  return false

def inj (ds : Array Lean.Expr) (i : Nat) (pf : Lean.Expr) : Lean.Expr := Id.run do
  let n := ds.size
  let tails : Array Lean.Expr := Id.run do
    let mut ts : Array Lean.Expr := Array.replicate n (mkConst ``True)
    ts := ts.set! (n - 1) ds[n - 1]!
    for k' in [0:n - 1] do
      let k := n - 2 - k'
      ts := ts.set! k (mkApp2 (mkConst ``Or) ds[k]! ts[k + 1]!)
    ts
  let mut p := if i + 1 == n then pf else mkApp3 (mkConst ``Or.inl) ds[i]! tails[i + 1]! pf
  for k' in [0:i] do
    let k := i - 1 - k'
    p := mkApp3 (mkConst ``Or.inr) ds[k]! tails[k + 1]! p
  p

partial def orParts (T : Lean.Expr) : Array Lean.Expr :=
  if T.isAppOfArity ``Or 2 then #[T.appFn!.appArg!] ++ orParts T.appArg! else #[T]

/-- Prove `T` (a disjunction of writers or one writer): the facts of the atoms of the plans first; then
`Classical.em` of each writer's condition but the one chosen LAST, which is proved component by component from the
context and the others' failures; each choice of the last writer is tried, the given last one first. -/
partial def coverGoal (store : IO.Ref (Array (Lean.Expr × Lean.Expr))) (g : MVarId) (depth : Nat := 0)
    (done : Array Lean.Expr := #[]) (inherited : Option (Array Cand) := none) (prep : Option Syntax := none) :
    TacticM Unit := do
  g.withContext do
    let T ← instantiateMVars (← g.getType)
    for (ty, pf) in ← store.get do
      if ty == T then
        g.assign pf
        return
    if T.isAppOfArity ``Or 2 || T.isAppOfArity ``Exists 2 || (matchWin T).isSome then
      let ds := orParts T
      let mut plans : Array Plan := #[]
      for d in ds do plans := plans.push (← planOf d)
      -- the player's facts at the solved witnesses (`sv_cover using tac`): the writers' conditions are put in context
      -- as `L → L` (no claim), `tac` runs, and they are cleared
      let g ← match prep, inherited with
        | some tac, none => do
          let mut g' := g
          let mut carriers : Array FVarId := #[]
          for p in plans do
            let L := mkAndAll p.inL
            let ty ← g'.withContext (mkArrow L L)
            let pf ← g'.withContext (withLocalDeclD `h L fun h => mkLambdaFVars #[h] h)
            let (h, g'') ← (← g'.assert `hplan ty pf).intro1P
            carriers := carriers.push h
            g' := g''
          setGoals [g']
          evalTactic tac
          let [g''] ← getGoals | throwError "sv_cover: the facts tactic left other goals"
          g''.tryClearMany (← g''.withContext do
            pure ((← getLCtx).foldl (init := #[]) fun acc d => if d.userName == `hplan then acc.push d.fvarId else acc))
        | _, _ => pure g
      -- the facts of every atom of the plans and the context, decided once
      -- the facts of `$clog2` (as `sv_pow_facts` states them)
      let mut hyps0 : Array Lean.Expr := #[]
      for d in ← getLCtx do
        unless d.isImplementationDetail do hyps0 := hyps0.push (← instantiateMVars d.type)
      let g ← if inherited.isNone && hyps0.any (fun e => (clog2Args e).size > 0) then do
          setGoals [g]
          g.withContext (LeanModels.Sv.CombView.addClog2Facts hyps0)
          (← getMainGoal).withContext (_root_.addClog2PowFacts hyps0)
          getMainGoal
        else pure g
      let hyps ← g.withContext do
        let mut hs : Array Lean.Expr := #[]
        for d in ← getLCtx do
          unless d.isImplementationDetail do hs := hs.push (← instantiateMVars d.type)
        pure hs
      let mut es : Array Lean.Expr := hyps
      for p in plans do es := es ++ p.inL
      let cands ← match inherited with
        | some p => pure p
        | none => candidates g es hyps
      let (g, pend) ← addFacts g cands
      -- a writer's row equation between context terms that the context does not decide: split on it first, so that
      -- in each branch the facts of the atoms are decided
      if depth < 3 then
        let mut split? : Option Lean.Expr := none
        for p in plans do
          if split?.isSome then break
          for c in p.inL do
            if split?.isSome then break
            let some (ty, _, _) := c.eq? | continue
            unless ty.isConstOf ``Int do continue
            if c.hasMVar || (c.find? fun x => x.isAppOfArity ``Int.toNat 1).isSome then continue
            if done.contains c then continue
            if (← proveBy g c 4).isSome then continue
            if (← proveBy g (mkNot c) 4).isSome then continue
            split? := some c
        if let some c := split? then
          let emC ← mkAppM ``Classical.em #[c]
          let gs ← g.apply (← mkAppOptM ``Or.elim #[some c, some (mkNot c), some T, some emC])
          let [gl, gr] := gs | throwError "sv_cover: internal error (split)"
          let (_, gl') ← gl.intro1
          let (_, gr') ← gr.intro1
          coverGoal store gl' (depth + 1) (done.push c) (some pend) prep
          coverGoal store gr' (depth + 1) (done.push c) (some pend) prep
          return
      -- each writer: refuted by the context, and which components of its condition the context proves
      let mut refW : Array Bool := #[]
      let mut provs : Array (Array (Option Lean.Expr)) := #[]
      let mut cache : Array (Lean.Expr × Option Lean.Expr) := #[]
      for p in plans do
        let rf ← refuted g (mkAndAll p.inL)
        refW := refW.push rf
        let mut ps : Array (Option Lean.Expr) := #[]
        unless rf do
          for c in p.inL do
            match cache.find? (·.1 == c) with
            | some (_, r) => ps := ps.push r
            | none =>
              let r ← proveBy g c 4
              cache := cache.push (c, r)
              ps := ps.push r
        provs := provs.push ps
      -- a writer whose condition the context proves outright
      for i in [0:ds.size] do
        if !refW[i]! && provs[i]!.all Option.isSome then
          let hs := plans[i]!.fullHs (provs[i]!.map Option.get!)
          let (pf, _, _) ← g.withContext (build ds[i]! plans[i]!.ws.toList plans[i]!.wins.toList hs.toList)
          if ← g.withContext (isDefEq (← inferType pf) ds[i]!) then
            g.assign (inj ds i pf)
            return
      let n := ds.size
      let order := ((Array.range n).reverse).filter (fun j => !refW[j]!)
      let mut firstErr : Option Exception := none
      for j in order do
        let saved ← saveState
        try
          walk ds plans pend refW provs j g
          return
        catch ex =>
          saved.restore
          if firstErr.isNone then firstErr := some ex
      match firstErr with
      | some ex => throw ex
      | none => throwError "sv_cover: no writer"
    else if T.isAppOfArity ``And 2 then
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      let [ga, gb] := gs | throwError "sv_cover: internal error (And.intro)"
      coverGoal store ga depth done inherited prep
      store.modify (·.push (← instantiateMVars (← ga.getType), ← instantiateMVars (mkMVar ga)))
      coverGoal store gb depth done inherited prep
    else
      setGoals [g]
      evalTactic (← `(tactic| omega))
      unless (← getGoals).isEmpty do throwError "sv_cover: a linear fact is not provable"
where
  walk (ds : Array Lean.Expr) (plans : Array Plan) (pend : Array Cand) (refW : Array Bool)
      (provs : Array (Array (Option Lean.Expr))) (j : Nat) (g : MVarId) : TacticM Unit := do
    let mut g := g
    let mut negs : List (FVarId × Lean.Expr) := []
    for i in [0:ds.size] do
      if i == j || refW[i]! then continue
      let plan := plans[i]!
      let L := mkAndAll plan.inL
      -- the components the context does not prove: the negation keeps only those
      let opn := (Array.range plan.inL.size).filter fun k => provs[i]![k]!.isNone
      let D := mkAndAll (opn.map fun k => plan.inL[k]!)
      let gi := g
      let (g', hn) ← gi.withContext do
        let T ← gi.getType
        let emL ← mkAppM ``Classical.em #[L]
        let gs ← gi.apply (← mkAppOptM ``Or.elim #[some L, some (mkNot L), some T, some emL])
        let [gl, gr] := gs | throwError "sv_cover: internal error (Or.elim)"
        let (hl, gl') ← gl.intro1
        gl'.withContext do
          let hs := plan.fullHs (← projs (mkFVar hl) plan.inL.size)
          let (pf, _, _) ← build ds[i]! plan.ws.toList plan.wins.toList hs.toList
          unless (← isDefEq (← inferType pf) ds[i]!) do throwError "sv_cover: internal error (ill-typed proof)"
          gl'.assign (inj ds i pf)
        let (hn, gr') ← gr.intro1
        -- `¬ D` from `¬ L` and the proved components
        gr'.withContext do
          let pf ← withLocalDeclD `hd D fun hd => do
            let ps ← projs hd opn.size
            let mut comps : Array Lean.Expr := #[]
            let mut q := 0
            for k in [0:plan.inL.size] do
              match provs[i]![k]! with
              | some p => comps := comps.push p
              | none => comps := comps.push ps[q]!; q := q + 1
            -- `c₁ ∧ (c₂ ∧ …)`
            let n := comps.size
            let mut acc := comps[n - 1]!
            for k' in [0:n - 1] do
              let k := n - 2 - k'
              acc ← mkAppM ``And.intro #[comps[k]!, acc]
            mkLambdaFVars #[hd] (mkApp (mkFVar hn) acc)
          let (hn', g2) ← (← gr'.assert `hneg (mkNot D) pf).intro1P
          let g3 ← g2.tryClear hn
          pure (g3, hn')
      negs := negs ++ [(hn, D)]
      g := g'
    let plan := plans[j]!
    let L := mkAndAll plan.inL
    g.withContext do
      let gL ← mkFreshExprSyntheticOpaqueMVar L
      if let some c ← proveAll pend gL.mvarId! plan.inL (if refW[j]! then #[] else provs[j]!) then
        let rd := (readOf? ds[j]!).getD ds[j]!
        throwError "{diagPrefix}{indentExpr rd}\nlast writer {j} of {ds.size}: the component that does not follow:{indentExpr (← tidy c)}\nin{indentExpr (← tidy L)}"
      let hs := plan.fullHs (← (← projs gL plan.inL.size).mapM instantiateMVars)
      let (pf, _, _) ← build ds[j]! plan.ws.toList plan.wins.toList hs.toList
      unless (← isDefEq (← inferType pf) ds[j]!) do throwError "sv_cover: internal error (ill-typed proof)"
      g.assign (inj ds j pf)

/-- **The rule on the main goal** (after `intros`): it fails with an ordinary exception wherever it does not prove the
goal (a shape it does not read, a writer it cannot solve, a condition that does not follow). -/
def coverUnits (prep : Option Syntax := none) : TacticM Unit := do
  let goal ← getMainGoal
  let store ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  coverGoal store goal (prep := prep)
  unless ← goal.isAssigned do throwError "sv_cover: internal error (goal left open)"
  setGoals []


end CombCoverUnit
end LeanModels.Sv
