import Examples.«system-verilog».mul_dadda.gen
import LeanModels.Sv.CombViewTactic
import LeanModels.Sv.CombPlumbing

/-!
# The Dadda record's structure, at every `1 ≤ N < 2^30` (`Examples/system-verilog/mul_dadda`, tac10)

`mul_dadda_comb_shared : CombDesign (mul_dadda.sem N) ∧ SharedObl mul_dadda.pdesign [N]` for every `1 ≤ N < 2^30` (the
range of the record's own height table: `d(50) < 2^30 < d(51)`), by the `sv_comb` tactics; `acyclic.lean` proves
`Acyclic` with the same closer and assembles `mul_dadda_struct : CombDesign ∧ Acyclic`:

* the parameter stage: the stage count `S` (a sum of 51 `?:`) and `NP` are bound node by node (`closeParamEnvComp`,
  CombParamComp.lean), linear in their size;
* `sv_structure` with the localparams as variables (`sv_comb.lp_atoms`) and no automatic closers (`sv_comb.auto_close
  false`) states the structural obligations: 99 goals, 73 of them holding the record's 51-leaf table of stage targets;
* the player's closer (`dadda_close`, below) proves each, in isolation (the library's `closeIsolated`,
  `CombPlumbing.lean`: the finished proof becomes an
  auxiliary lemma, so the closing's intermediate states do not accumulate over 99 goals of up to 64 000 characters):
  every copy of the table is the function `dT` of its index (`dadda_abs`, definitionally the record's `?:` chain); the
  one-iteration genvars of a stage (`t`, `u`, `f`, `h`, `c`) are substituted by their values (`dadda_pin`); the facts of
  `dT` at the indices in context and of the stage count (`dadda_facts`: the heights increase by half,
  `d(S-1) < N ≤ d(S-1) + d(S-1)/2`) are put in context; the row-major offsets are decomposed (the library's `sv_rowmajor_connected [N, S, NP]`, whose
  side conditions are proved in the part of the context connected to them); a goal about two sites is split on the
  order of their stage and column genvars (`dadda_pair`), so that where the instances coincide their terms do; and each
  branch closes by `omega`, `sv_ite_omega` or, with the pairwise facts of the table, `sv_ite_omega`.

The facts of `dT` are decided by the kernel over its 51 entries (`decide +kernel`: kernel reduction, no extra axiom;
the theorems below pin their axioms); `dadda_S` is a lemma about the count of a strictly increasing list (`cnt_spec`).

Build: `lake build Examples.«system-verilog».mul_dadda.comb_proof Examples.«system-verilog».mul_dadda.acyclic`.
-/

open Lean Elab Tactic Meta
open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».mul_dadda.gen

namespace Examples.«system-verilog».mul_dadda.comb_proof

/-! ## The heights and the stage count -/

/-- The Dadda heights `d(j)` (`d(0) = 2`, `d(j+1) = d(j) + d(j)/2`), as the record's `?:` chain over `j` (the obligations
print it so). -/
def dT (j : Int) : Int :=
  if j < 8 then (if j = 0 then 2 else if j = 1 then 3 else if j = 2 then 4 else if j = 3 then 6 else if j = 4 then 9 else if j = 5 then 13 else if j = 6 then 19 else 28) else if j < 16 then (if j = 8 then 42 else if j = 9 then 63 else if j = 10 then 94 else if j = 11 then 141 else if j = 12 then 211 else if j = 13 then 316 else if j = 14 then 474 else 711) else if j < 24 then (if j = 16 then 1066 else if j = 17 then 1599 else if j = 18 then 2398 else if j = 19 then 3597 else if j = 20 then 5395 else if j = 21 then 8092 else if j = 22 then 12138 else 18207) else if j < 32 then (if j = 24 then 27310 else if j = 25 then 40965 else if j = 26 then 61447 else if j = 27 then 92170 else if j = 28 then 138255 else if j = 29 then 207382 else if j = 30 then 311073 else 466609) else if j < 40 then (if j = 32 then 699913 else if j = 33 then 1049869 else if j = 34 then 1574803 else if j = 35 then 2362204 else if j = 36 then 3543306 else if j = 37 then 5314959 else if j = 38 then 7972438 else 11958657) else if j < 48 then (if j = 40 then 17937985 else if j = 41 then 26906977 else if j = 42 then 40360465 else if j = 43 then 60540697 else if j = 44 then 90811045 else if j = 45 then 136216567 else if j = 46 then 204324850 else 306487275) else (if j = 48 then 459730912 else if j = 49 then 689596368 else 1034394552)

theorem dT_fin_bnd : ∀ n : Fin 51, 2 ≤ dT (n : Nat) ∧ dT (n : Nat) ≤ 1034394552 := by decide +kernel
theorem dT_fin_rec : ∀ n : Fin 50, dT (n : Nat) + dT (n : Nat) / 2 = dT ((n : Nat) + 1) := by decide +kernel
theorem dT_fin_le : ∀ n : Fin 50, dT (n : Nat) ≤ dT ((n : Nat) + 1) := by decide +kernel
theorem dT_50 : dT 50 + dT 50 / 2 = 1551591828 := by decide +kernel

theorem dT_bnd (j : Int) (h0 : 0 ≤ j) (h1 : j ≤ 50) : 2 ≤ dT j ∧ dT j ≤ 1034394552 := by
  have h := dT_fin_bnd ⟨j.toNat, by omega⟩
  have e : ((j.toNat : Nat) : Int) = j := by omega
  simpa only [e] using h

theorem dT_rec (j : Int) (h0 : 0 ≤ j) (h1 : j ≤ 49) : dT j + dT j / 2 = dT (j + 1) := by
  have h := dT_fin_rec ⟨j.toNat, by omega⟩
  have e : ((j.toNat : Nat) : Int) = j := by omega
  simpa only [e] using h

theorem dT_le_succ (j : Int) (h0 : 0 ≤ j) (h1 : j ≤ 49) : dT j ≤ dT (j + 1) := by
  have h := dT_fin_le ⟨j.toNat, by omega⟩
  have e : ((j.toNat : Nat) : Int) = j := by omega
  simpa only [e] using h

theorem dT_mono_nat : ∀ (d : Nat) (j : Int), 0 ≤ j → j + d ≤ 50 → dT j ≤ dT (j + d)
  | 0, j, _, _ => by simp
  | d + 1, j, h0, h1 => by
      have a := dT_mono_nat d j h0 (by omega)
      have b := dT_le_succ (j + d) (by omega) (by omega)
      have e : j + ((d + 1 : Nat) : Int) = j + d + 1 := by omega
      rw [e]
      exact Int.le_trans a b

theorem dT_mono (j k : Int) (h0 : 0 ≤ j) (hjk : j ≤ k) (hk : k ≤ 50) : dT j ≤ dT k := by
  have h := dT_mono_nat (k - j).toNat j h0 (by omega)
  have e : j + (((k - j).toNat : Nat) : Int) = k := by omega
  rwa [e] at h

theorem dT_bnd_or (j : Int) : j < 0 ∨ 50 < j ∨ (2 ≤ dT j ∧ dT j ≤ 1034394552) := by
  by_cases h0 : 0 ≤ j
  · by_cases h1 : j ≤ 50
    · exact Or.inr (Or.inr (dT_bnd j h0 h1))
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)

theorem dT_succ_le_or (j k : Int) : j < 0 ∨ k ≤ j ∨ 50 < k ∨ dT j + dT j / 2 ≤ dT k := by
  by_cases h0 : 0 ≤ j
  · by_cases h1 : j < k
    · by_cases h2 : k ≤ 50
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [dT_rec j h0 (by omega)]
        exact dT_mono (j + 1) k (by omega) (by omega) h2
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)

theorem dT_congr_or (j k : Int) : j < k ∨ k < j ∨ dT j = dT k := by
  by_cases h : j = k
  · exact Or.inr (Or.inr (by rw [h]))
  · by_cases h' : j < k
    · exact Or.inl h'
    · exact Or.inr (Or.inl (by omega))

theorem dT_mono_or (j k : Int) : j < 0 ∨ k < j ∨ 50 < k ∨ dT j ≤ dT k := by
  by_cases h0 : 0 ≤ j
  · by_cases h1 : j ≤ k
    · by_cases h2 : k ≤ 50
      · exact Or.inr (Or.inr (Or.inr (dT_mono j k h0 h1 h2)))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)


/-- `dT_succ_le_or` with the argument inside the table. -/
theorem dT_succ_le2 (j k : Int) (hj : 0 ≤ j) (hk : k ≤ 50) : k ≤ j ∨ dT j + dT j / 2 ≤ dT k := by
  rcases dT_succ_le_or j k with h | h | h | h
  · omega
  · exact Or.inl h
  · omega
  · exact Or.inr h

/-- `dT_mono_or` with the arguments inside the table. -/
theorem dT_mono2 (j k : Int) (hj : 0 ≤ j) (hk : k ≤ 50) : k < j ∨ dT j ≤ dT k := by
  rcases dT_mono_or j k with h | h | h | h
  · omega
  · exact Or.inl h
  · omega
  · exact Or.inr h

/-- A term of the stage count: `(N > c) ? 1 : 0` as the obligations print it (`CE.eval` of the `?:`). -/
def tterm (N c : Int) : Int := if (if c < N then (1 : Int) else 0) = 0 then 0 else 1

/-- The stage count's left-nested sum `((t₀ + t₁) + t₂) + …`. -/
def tsum (N : Int) : Int → List Int → Int
  | acc, [] => acc
  | acc, c :: cs => tsum N (acc + tterm N c) cs

theorem tterm_eq (N c : Int) : tterm N c = if c < N then 1 else 0 := by
  unfold tterm; by_cases h : c < N <;> simp [h]

theorem tsum_eq (N : Int) : ∀ (acc : Int) (cs : List Int),
    tsum N acc cs = acc + ((cs.filter (fun c => decide (c < N))).length : Int)
  | acc, [] => by simp [tsum]
  | acc, c :: cs => by
      rw [tsum, tsum_eq N _ cs, tterm_eq]
      by_cases h : c < N
      · simp [h, List.filter_cons]; omega
      · simp [h, List.filter_cons]

/-- The stage count as the record writes it (definitionally its `?:` sum). -/
def dSum (N : Nat) : Int := tsum (N : Int) (tterm (N : Int) 2) [3, 4, 6, 9, 13, 19, 28, 42, 63, 94, 141, 211, 316, 474, 711, 1066, 1599, 2398, 3597, 5395, 8092, 12138, 18207, 27310, 40965, 61447, 92170, 138255, 207382, 311073, 466609, 699913, 1049869, 1574803, 2362204, 3543306, 5314959, 7972438, 11958657, 17937985, 26906977, 40360465, 60540697, 90811045, 136216567, 204324850, 306487275, 459730912, 689596368, 1034394552]

/-- The heights. -/
def dL : List Int := [2, 3, 4, 6, 9, 13, 19, 28, 42, 63, 94, 141, 211, 316, 474, 711, 1066, 1599, 2398, 3597, 5395, 8092, 12138, 18207, 27310, 40965, 61447, 92170, 138255, 207382, 311073, 466609, 699913, 1049869, 1574803, 2362204, 3543306, 5314959, 7972438, 11958657, 17937985, 26906977, 40360465, 60540697, 90811045, 136216567, 204324850, 306487275, 459730912, 689596368, 1034394552]

theorem dL_len : dL.length = 51 := by decide +kernel

theorem dL_pw : dL.Pairwise (· < ·) := by decide +kernel

theorem dT_dL : ∀ n : Nat, (h : n < 51) → dT n = dL[n]'(by rw [dL_len]; exact h) := by decide +kernel

/-- Below the count every entry of a strictly increasing list is below `N`, and the entry at the count is not. -/
theorem cnt_spec (N : Int) : ∀ (l : List Int), l.Pairwise (· < ·) →
    (∀ i, i < (l.filter (fun c => decide (c < N))).length → ∀ h : i < l.length, l[i] < N) ∧
    (∀ h : (l.filter (fun c => decide (c < N))).length < l.length, N ≤ l[(l.filter (fun c => decide (c < N))).length])
  | [], _ => by simp
  | a :: l, hp => by
      rw [List.pairwise_cons] at hp
      obtain ⟨ha, hl⟩ := hp
      obtain ⟨ih1, ih2⟩ := cnt_spec N l hl
      by_cases h : a < N
      · simp only [List.filter_cons, h, decide_true, ↓reduceIte, List.length_cons]
        refine ⟨?_, ?_⟩
        · intro i hi hil
          cases i with
          | zero => simpa using h
          | succ j => simpa using ih1 j (by omega) (by simpa using hil)
        · intro hc
          simpa using ih2 (by simpa using hc)
      · have h0 : l.filter (fun c => decide (c < N)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          have := ha x hx
          simp only [decide_eq_true_eq]
          omega
        simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, ↓reduceIte, h0, List.length_nil]
        refine ⟨fun i hi => absurd hi (by omega), fun _ => ?_⟩
        simp only [List.getElem_cons_zero]
        omega

set_option maxRecDepth 8192 in
/-- **The stage count** `S` of the record: the number of Dadda heights below `N` (a strictly increasing list's count). -/
theorem dadda_S (N : Nat) (h30 : N < 2 ^ 30) (S : Int) (hS : dSum N = S) :
    0 ≤ S ∧ S ≤ 51 ∧ ((S = 0 ∧ (N : Int) ≤ 2) ∨
      (1 ≤ S ∧ dT (S - 1) < (N : Int) ∧ (N : Int) ≤ dT (S - 1) + dT (S - 1) / 2)) := by
  have hT : tsum (N : Int) (tterm (N : Int) 2) [3, 4, 6, 9, 13, 19, 28, 42, 63, 94, 141, 211, 316, 474, 711, 1066, 1599, 2398, 3597, 5395, 8092, 12138, 18207, 27310, 40965, 61447, 92170, 138255, 207382, 311073, 466609, 699913, 1049869, 1574803, 2362204, 3543306, 5314959, 7972438, 11958657, 17937985, 26906977, 40360465, 60540697, 90811045, 136216567, 204324850, 306487275, 459730912, 689596368, 1034394552] = S := hS
  have hc : tsum (N : Int) 0 dL = S := by
    rw [← hT]
    show tsum (N : Int) (0 + tterm (N : Int) 2) _ = _
    rw [Int.zero_add]
  clear hT hS
  rw [tsum_eq, Int.zero_add] at hc
  obtain ⟨h1, h2⟩ := cnt_spec (N : Int) dL dL_pw
  generalize hm : (dL.filter (fun c => decide (c < (N : Int)))).length = m at hc h1 h2
  have hml : m ≤ 51 := by rw [← hm, ← dL_len]; exact List.length_filter_le _ _
  subst hc
  refine ⟨by omega, by omega, ?_⟩
  by_cases hm0 : m = 0
  · subst hm0
    left
    refine ⟨rfl, ?_⟩
    have := h2 (by rw [dL_len]; omega)
    simpa [dL] using this
  · right
    have e1 : ((m : Int) - 1) = ((m - 1 : Nat) : Int) := by omega
    have hd := dT_dL (m - 1) (by omega)
    have hlo := h1 (m - 1) (by omega) (by rw [dL_len]; omega)
    refine ⟨by omega, ?_, ?_⟩
    · rw [e1, hd]
      exact hlo
    · by_cases h51 : m = 51
      · subst h51
        have h50 : dT 50 + dT 50 / 2 = 1551591828 := dT_50
        have e50 : ((51 : Nat) : Int) - 1 = 50 := by decide
        rw [e50]
        omega
      · have hlt : m < dL.length := Nat.lt_of_lt_of_le (show m < 51 by omega) (Nat.le_of_eq dL_len.symm)
        have hhi := h2 hlt
        have hdm := dT_dL m (by omega)
        have hr := dT_rec ((m : Int) - 1) (by omega) (by omega)
        have e2 : (m : Int) - 1 + 1 = ((m : Nat) : Int) := by omega
        rw [e2] at hr
        rw [← hdm] at hhi
        clear h1 h2 hd hlo hdm hm
        omega



/-- `NP = (N < 2) ? 2 : N` as a two-way disjunction (`omega` sees an `if-then-else` as an atom). -/
theorem np_cases (N : Nat) (NP : Int)
    (h : (if (if (N : Int) < 2 then (1 : Int) else 0) = 0 then (N : Int) else 2) = NP) :
    ((N : Int) < 2 ∧ NP = 2) ∨ (2 ≤ (N : Int) ∧ NP = (N : Int)) := by
  by_cases hN : (N : Int) < 2
  · left
    rw [if_pos hN] at h
    simp at h
    omega
  · right
    rw [if_neg hN] at h
    simp at h
    omega

/-! ## The closer -/

/- From here on `dT` is unfolded by the kernel only: the closer's `omega` and `simp` calls see `dT X` as an atom (the
replacements of `dadda_abs` are definitional and checked by the kernel). -/
attribute [irreducible] dT

/-- Every copy of the table in the goal and its hypotheses as `dT X` (definitionally the same; the kernel checks it when it
checks the goal's proof). -/
elab "dadda_abs" : tactic => withMainContext do
  let isTbl (e : Lean.Expr) : Bool := e.isAppOfArity ``ite 5 && (e.getArg! 1).isAppOfArity ``LT.lt 4 &&
    ((e.getArg! 1).getArg! 3).int? == some 8 && (e.find? fun x => x.int? == some 1034394552).isSome
  let repl (t : Lean.Expr) : MetaM Lean.Expr := Meta.transform t (pre := fun e => do
    if isTbl e then return .done (mkApp (mkConst ``dT) ((e.getArg! 1).getArg! 2)) else return .continue)
  let mut g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let t' ← repl t
    if t' != t then g ← g.replaceLocalDeclDefEq d.fvarId t'
  let t ← instantiateMVars (← g.getType)
  let t' ← repl t
  if t' != t then g ← g.replaceTargetDefEq t'
  replaceMainGoal [g]

/-- The one-iteration genvars (`t`, `u`, `f`, `h`, `c` of a stage): for every `x` with hypotheses `E ≤ x` and `x < 1 + E`
(or `x < E + 1`), `x = E` by `omega`, substituted. -/
elab "dadda_pin" : tactic => do
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < 64 do
    changed := false
    rounds := rounds + 1
    let g ← getMainGoal
    let found? ← g.withContext do
      let lctx ← getLCtx
      let mut res : Option (Lean.Expr × Lean.Expr) := none
      for d in lctx do
        if d.isImplementationDetail || res.isSome then continue
        let t ← instantiateMVars d.type
        if t.isAppOfArity ``LE.le 4 then
          let E := t.getArg! 2
          let x := t.getArg! 3
          if x.isFVar && !E.containsFVar x.fvarId! && (← inferType x) == mkConst ``Int then
            for d2 in lctx do
              let t2 ← instantiateMVars d2.type
              if t2.isAppOfArity ``LT.lt 4 && t2.getArg! 2 == x then
                let U := t2.getArg! 3
                if U.isAppOfArity ``HAdd.hAdd 6 && ((U.getArg! 4).int? == some 1 && U.getArg! 5 == E ||
                    U.getArg! 4 == E && (U.getArg! 5).int? == some 1) then
                  res := some (x, E)
                  break
      pure res
    if let some (x, E) := found? then
      let xs ← g.withContext (Term.exprToSyntax x)
      let Es ← g.withContext (Term.exprToSyntax E)
      evalTactic (← `(tactic| (have hpin : $xs = $Es := by omega
                               subst hpin)))
      changed := true

/-- The pairs of corresponding genvars of the two sites of a disjointness goal: two `Int` locals with the same upper bound
`x < E`, `E` free of genvars (the stage loop's `S`, the column loop's `2 * N`), in the order of the context. -/
def daddaPairs : TacticM (Array (Name × Name)) := withMainContext do
  let lctx ← getLCtx
  let mut gens : Array FVarId := #[]
  for d in lctx do
    if !d.isImplementationDetail && d.userName != `S && d.userName != `NP &&
        (← instantiateMVars d.type) == mkConst ``Int then
      gens := gens.push d.fvarId
  let mut groups : Array (Lean.Expr × Array Name) := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.isAppOfArity ``LT.lt 4 do continue
    let x := t.getArg! 2
    let E := t.getArg! 3
    unless x.isFVar && gens.contains x.fvarId! do continue
    if gens.any (E.containsFVar ·) then continue
    let n := (lctx.get! x.fvarId!).userName
    match groups.findIdx? (·.1 == E) with
    | some k => groups := groups.modify k fun (e, ns) => (e, if ns.contains n then ns else ns.push n)
    | none => groups := groups.push (E, #[n])
  return groups.filterMap fun (_, ns) => if ns.size == 2 then some (ns[0]!, ns[1]!) else none

/-- Split a disjointness goal of two sites on the order of each pair of corresponding genvars (`daddaPairs`): `x < y`,
`x = y` (substituted: the two sites' terms then coincide) and `y < x`. -/
elab "dadda_pair" : tactic => do
  let ps ← daddaPairs
  let mut gs : List MVarId := [← getMainGoal]
  for (nx, ny) in ps do
    let mut next : List MVarId := []
    for g' in gs do
      setGoals [g']
      -- by name: `subst` re-creates the later locals
      let pair? ← g'.withContext do
        let lctx ← getLCtx
        match lctx.findFromUserName? nx, lctx.findFromUserName? ny with
        | some dx, some dy => pure (some (dx.toExpr, dy.toExpr))
        | _, _ => pure none
      let some (x, y) := pair? | do
        next := next ++ [g']
        continue
      let xs ← g'.withContext (Term.exprToSyntax x)
      let ys ← g'.withContext (Term.exprToSyntax y)
      evalTactic (← `(tactic| rcases Int.lt_trichotomy $xs $ys with hpair | hpair | hpair))
      let [gLt, gEq, gGt] ← getGoals | throwError "dadda_pair: trichotomy"
      setGoals [gEq]
      evalTactic (← `(tactic| subst hpair))
      next := next ++ (← getGoals) ++ [gLt, gGt]
    gs := next
  setGoals gs

/-- The arguments `X` of the `dT X` subterms of `e`. -/
partial def dtArgs (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let acc := if e.isAppOfArity ``dT 1 && !e.hasLooseBVars && !acc.contains e.appArg! then acc.push e.appArg! else acc
  match e with
  | .app f a => dtArgs a (dtArgs f acc)
  | .mdata _ b | .proj _ _ b => dtArgs b acc
  | .lam _ t b _ | .forallE _ t b _ => dtArgs b (dtArgs t acc)
  | _ => acc

/-- The facts of the table at the arguments `X` in context, and `hlp_S` cleared. Where `omega` shows `0 ≤ X ≤ 50`, the
facts are stated with that side condition discharged (a conjunction and two-way disjunctions, `dT_bnd`, `dT_succ_le2`,
`dT_mono2`): every three- or four-way disjunction left in context multiplies the cases of every later `omega` call. With
`pairwise`, the order and congruence facts of every two arguments too. -/
def daddaFactsRest (S : Lean.Expr) (pairwise : Bool) : TacticM Unit := do
  let S1 ← mkAppM ``HSub.hSub #[S, toExpr (1 : Int)]
  let mut xs : Array Lean.Expr := #[]
  for e in ← goalExprs do xs := dtArgs e xs
  let le50 (x : Lean.Expr) : TacticM Lean.Expr := mkAppM ``LE.le #[x, toExpr (50 : Int)]
  let ge0 (x : Lean.Expr) : TacticM Lean.Expr := mkAppM ``LE.le #[toExpr (0 : Int), x]
  let hS1 ← omegaProves (← le50 S1)
  let mut ins : Array (Lean.Expr × Option (Lean.Expr × Lean.Expr)) := #[]
  for x in xs do
    match ← omegaProves (← ge0 x), ← omegaProves (← le50 x) with
    | some p0, some p1 =>
      ins := ins.push (x, some (p0, p1))
      assertMainM `hdb (mkAppM ``dT_bnd #[x, p0, p1])
      if x != S1 then
        match hS1 with
        | some q => assertMainM `hds (mkAppM ``dT_succ_le2 #[x, S1, p0, q])
        | none => assertMainM `hds (mkAppM ``dT_succ_le_or #[x, S1])
        assertMainM `hdc (mkAppM ``dT_congr_or #[x, S1])
    | _, _ =>
      ins := ins.push (x, none)
      assertMainM `hdb (mkAppM ``dT_bnd_or #[x])
      if x != S1 then
        assertMainM `hds (mkAppM ``dT_succ_le_or #[x, S1])
        assertMainM `hdc (mkAppM ``dT_congr_or #[x, S1])
  if pairwise then
    for i in [0:ins.size] do
      for j in [0:ins.size] do
        if i < j then
          let (xi, pi) := ins[i]!
          let (xj, pj) := ins[j]!
          assertMainM `hdc (mkAppM ``dT_congr_or #[xi, xj])
          match pi, pj with
          | some (pi0, _), some (_, pj1) => assertMainM `hdm (mkAppM ``dT_mono2 #[xi, xj, pi0, pj1])
          | _, _ => assertMainM `hdm (mkAppM ``dT_mono_or #[xi, xj])
          match pj, pi with
          | some (pj0, _), some (_, pi1) => assertMainM `hdm (mkAppM ``dT_mono2 #[xj, xi, pj0, pi1])
          | _, _ => assertMainM `hdm (mkAppM ``dT_mono_or #[xj, xi])
  let g ← getMainGoal
  let some hS' := (← g.withContext getLCtx).findFromUserName? `hlp_S | return
  replaceMainGoal [← g.clear hS'.fvarId]

/-- The facts of the table at the arguments in context and of the stage count (from `hlp_S`, then cleared). -/
def daddaFacts (pairwise : Bool) : TacticM Unit := withMainContext do
  let some S := (← getLCtx).findFromUserName? `S | throwError "no S"
  let some hS := (← getLCtx).findFromUserName? `hlp_S | throwError "no hlp_S"
  let some N := (← getLCtx).findFromUserName? `N | throwError "no N"
  let some h30 := (← getLCtx).findFromUserName? `h30 | throwError "no h30"
  -- `hlp_S` is definitionally `dSum N = S`: its decisions' instances still name the summary's `CE.eval`, which the
  -- elaborator does not unfold inside an instance argument; the kernel checks the hint
  let want ← mkEq (mkApp (mkConst ``dSum) N.toExpr) S.toExpr
  let pf := mkAppN (mkConst ``dadda_S) #[N.toExpr, h30.toExpr, S.toExpr, ← mkExpectedTypeHint hS.toExpr want]
  assertMain `hdS pf
  -- `NP`'s definition as a two-way disjunction (`np_cases`; `hlp_NP`'s instances name `CE.eval` too: a hint)
  if let some hNPd := (← (← getMainGoal).withContext getLCtx).findFromUserName? `hlp_NP then
    if let some NPd := (← (← getMainGoal).withContext getLCtx).findFromUserName? `NP then
      let f := mkAppN (mkConst ``np_cases) #[N.toExpr, NPd.toExpr]
      let fty ← (← getMainGoal).withContext (whnf (← inferType f))
      if let .forallE _ dom _ _ := fty then
        assertMain `hNP (mkApp f (← mkExpectedTypeHint hNPd.toExpr dom))
  (← getMainGoal).withContext (daddaFactsRest S.toExpr pairwise)

elab "dadda_facts" : tactic => daddaFacts false
elab "dadda_facts_pairwise" : tactic => daddaFacts true

/-- The order and congruence facts of every two of the table's arguments in context (side conditions discharged as in
`daddaFactsRest`). -/
elab "dadda_pairwise" : tactic => withMainContext do
  let mut xs : Array Lean.Expr := #[]
  for e in ← goalExprs do xs := dtArgs e xs
  let le50 (x : Lean.Expr) : TacticM Lean.Expr := mkAppM ``LE.le #[x, toExpr (50 : Int)]
  let ge0 (x : Lean.Expr) : TacticM Lean.Expr := mkAppM ``LE.le #[toExpr (0 : Int), x]
  let mut ins : Array (Lean.Expr × Option (Lean.Expr × Lean.Expr)) := #[]
  for x in xs do
    match ← omegaProves (← ge0 x), ← omegaProves (← le50 x) with
    | some p0, some p1 => ins := ins.push (x, some (p0, p1))
    | _, _ => ins := ins.push (x, none)
  for i in [0:ins.size] do
    for j in [0:ins.size] do
      if i < j then
        let (xi, pi) := ins[i]!
        let (xj, pj) := ins[j]!
        assertMainM `hdc (mkAppM ``dT_congr_or #[xi, xj])
        match pi, pj with
        | some (pi0, _), some (_, pj1) => assertMainM `hdm (mkAppM ``dT_mono2 #[xi, xj, pi0, pj1])
        | _, _ => assertMainM `hdm (mkAppM ``dT_mono_or #[xi, xj])
        match pj, pi with
        | some (pj0, _), some (_, pi1) => assertMainM `hdm (mkAppM ``dT_mono2 #[xj, xi, pj0, pi1])
        | _, _ => assertMainM `hdm (mkAppM ``dT_mono_or #[xj, xi])

/-- The first of `alts` that closes the main goal, each attempt within `cap` heartbeats (an attempt that runs out is a
failure like any other, its state undone). -/
def firstCapped (cap : Nat) (alts : List (TSyntax `tactic)) : TacticM Unit := do
  let g ← getMainGoal
  for t in alts do
    setGoals [g]
    let st ← saveState
    let now ← IO.getNumHeartbeats
    let ok ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with maxHeartbeats := cap * 1000, initHeartbeats := now }) do
        evalTactic t
        pure (← getGoals).isEmpty)
      (fun _ => pure false)
    if ok then return
    st.restore
  throwError "dadda_close: no closer proves the goal {(← g.getTag).eraseMacroScopes}"

/-- The player's closer of one structural goal of the record (the description above), in isolation: the table as `dT`,
the one-iteration genvars substituted, the facts of the table, the row-major offsets decomposed (`sv_rowmajor_connected`), then
the split on the two sites' corresponding genvars, and per branch the first of `omega`, `sv_ite_omega`, and the pairwise
facts of the table with `sv_ite_omega`. -/
elab "dadda_close" : tactic => withEnableInfoTree false <| closeIsolated do
  evalTactic (← `(tactic| (intros; dadda_abs; dadda_pin; dadda_facts)))
  evalTactic (← `(tactic| (sv_rowmajor_connected [N, S, NP]; (try simp only [true_and, and_true]); dadda_pair)))
  let alts : List (TSyntax `tactic) :=
    [← `(tactic| omega), ← `(tactic| sv_ite_omega), ← `(tactic| (dadda_pairwise; sv_ite_omega))]
  for g in ← getGoals do
    setGoals [g]
    firstCapped 2000000 alts
  setGoals []

/-- `t` without info trees (they are of no use in a batch build, and `sv_structure`'s on this record are large). -/
elab "quiet " t:tactic : tactic => withEnableInfoTree false (evalTactic t)

/-! ## The structure -/

set_option sv_comb.lp_atoms true in
set_option sv_comb.auto_close false in
set_option maxHeartbeats 40000000 in
/-- **The Dadda record has the combinational profile** at every `1 ≤ N < 2^30`, with the shared obligations (the in-range
and range facts the rank below reuses). -/
theorem mul_dadda_comb_shared (N : Nat) (hN : 1 ≤ N) (h30 : N < 2 ^ 30) :
    CombDesign (mul_dadda.sem N) ∧ SharedObl mul_dadda.pdesign [N] := by
  quiet sv_structure
  all_goals dadda_close

/--
info: 'Examples.«system-verilog».mul_dadda.comb_proof.mul_dadda_comb_shared' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mul_dadda_comb_shared

end Examples.«system-verilog».mul_dadda.comb_proof
