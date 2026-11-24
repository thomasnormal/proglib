import LeanModels.Sv.Kernel.CoreMemFuel
/-! loopfuel-audit3, C5 (an audit check outside the repository; `lake env lean` in the tree under test).

The question C5 asks: wherever the OLD fixed-fuel semantics (the merge base) gives a decided answer, does the NEW
one (the tip) give the same answer? The tree's `coreMemFuelMono` relates the tip's executor to ITSELF at two fuels;
the old executor is no longer in the tree. So this file restores it: the block between the `-- BEGIN MERGE-BASE`
and `-- END MERGE-BASE` markers below is the merge base's `execStmtFuel`/`execStmtsFuel`/`execLoopValuesFuel` mutual
block and its `execStmt` entry (c45535fea, LeanModels/Sv/Kernel/CoreMemExec.lean), copied by `sed` with only the
names changed (`old*`). It differs from the tip's block in exactly one line: the loop arm reads `forValues2`
(unchecked) where the tip reads `forValues2Int32`.

Statement proved (`audit_execStmt_conservative`): for every design, environment, element table, state and statement,
`RC (old execStmt) (new execStmt)`, where `RC x y` says: `x` timed out, or `y = x`, or `y` is a refusal
(`.unsupported`). In words: wherever the merge base decided (a value or a refusal), the tip gives the same answer or
refuses loudly; it never gives a different value. The trace-only lemma `audit_forValues2Int32_cases` shows the only
new refusal is the range refusal. -/

namespace LeanModels.Sv.Kernel.Audit3
open LeanModels.Sv LeanModels.Sv.Kernel

set_option autoImplicit false

/-- `x` (old) against `y` (new): old timed out, or new is the same, or new refuses. -/
def RC {α : Type} (x y : Res α) : Prop :=
  x = .timeout ∨ y = x ∨ ∃ m, y = .unsupported m

theorem RC_refl {α : Type} (x : Res α) : RC x x := Or.inr (Or.inl rfl)

theorem RC_unsup {α : Type} (x : Res α) (m : String) : RC x (.unsupported m) := Or.inr (Or.inr ⟨m, rfl⟩)

theorem RC_bind {α β : Type} {x y : Res α} {f g : α → Res β}
    (h : RC x y) (hf : ∀ a, RC (f a) (g a)) : RC (x >>= f) (y >>= g) := by
  rcases h with h | h | ⟨m, h⟩
  · subst h; exact Or.inl rfl
  · subst h
    cases y with
    | ok a => exact hf a
    | timeout => exact Or.inl rfl
    | unsupported msg => exact RC_refl _
  · subst h; exact RC_unsup _ m

/-- `RC` composed with the tree's fuel order on the new side. -/
theorem RC_le {α : Type} {x y z : Res α} (h : RC x y) (hle : y ⊑ z) : RC x z := by
  rcases h with h | h | ⟨m, h⟩
  · exact Or.inl h
  · rcases hle with hl | hl
    · exact Or.inl (h ▸ hl)
    · exact Or.inr (Or.inl (hl ▸ h))
  · rcases hle with hl | hl
    · subst h; cases hl
    · exact Or.inr (Or.inr ⟨m, hl ▸ h⟩)

/-- The checked trace is the unchecked one, or the range refusal. -/
theorem audit_forValues2Int32_cases (env : IEnv) (it : String) (init cond step : PExpr) :
    forValues2Int32 env it init cond step = forValues2 env it init cond step ∨
      forValues2Int32 env it init cond step = .unsupported "for iterator leaves signed 32-bit range" := by
  unfold forValues2Int32 forValues2
  cases forFuel2 env it init cond step with
  | error e => exact Or.inl rfl
  | ok fuel =>
      simp only
      split
      · split
        · split
          · exact Or.inr rfl
          · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl

-- BEGIN MERGE-BASE (c45535fea LeanModels/Sv/Kernel/CoreMemExec.lean lines 3233-3342, names changed by sed)
mutual

def oldStmtFuel (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) : Nat → PStmt → CoreMemExec
  | 0, _ => .timeout
  | fuel + 1, .localDecl _ _ _ => .ok { state := st, scalarQ := [], memoryQ := [], locals }
  | fuel + 1, .automaticDecl name width init => do
      let locals' ← E.execAutomaticDecl env elems st locals name width init
      .ok { state := st, scalarQ := [], memoryQ := [], locals := locals' }
  | fuel + 1, .nbaAssign target value =>
      match SvState.lookup locals target with
      | some _ => .unsupported "10.4.2: nonblocking assignment to an automatic local is outside this E activation"
      | none =>
          match E.scalarTarget target with
          | none => .unsupported s!"11.5.1: scalar NBA target '{target}' is undeclared"
          | some width => do
              let v ← E.evalExprLocals env elems st (some width) locals value
              CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueTarget env elems st (.ident target) v))
  | fuel + 1, .nbaAssignL target value =>
      match target with
      | .ident name =>
          match SvState.lookup locals name with
          | some _ => .unsupported "10.4.2: nonblocking assignment to an automatic local is outside this E activation"
          | none =>
              match E.scalarTarget name with
              | none => .unsupported s!"11.5.1: scalar NBA target '{name}' is undeclared"
              | some width => do
                  let v ← E.evalExprLocals env elems st (some width) locals value
                  CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueTarget env elems st target v))
      | .arrayElem name indices =>
          match E.memDecl? name with
          | none => do
              let (_, width) ← E.scalarLhs2 env elems target
              let v ← E.evalExprLocals env elems st (some width) locals value
              CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueScalarTarget env elems st target v))
          | some md =>
              match indices with
              | [_] => do
                  let v ← E.evalExprLocals env elems st (some md.shape.elemWidth) locals value
                  CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueTarget env elems st target v))
              | _ => .unsupported s!"11.5.1: memory target '{name}' is not one-rank"
      | target => do
          let (_, width) ← E.scalarLhs2 env elems target
          let v ← E.evalExprLocals env elems st (some width) locals value
          CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueScalarTarget env elems st target v))
  | fuel + 1, .blockingAssign name value => do
      let (st', locals') ← E.execBlockingIdentLocal env elems st locals name value
      .ok { state := st', scalarQ := [], memoryQ := [], locals := locals' }
  | fuel + 1, .blockingAssignL target value =>
      match target with
      | .ident name => do
          let (st', locals') ← E.execBlockingIdentLocal env elems st locals name value
          .ok { state := st', scalarQ := [], memoryQ := [], locals := locals' }
      | _ => do
          let st' ← E.execBlockingTarget env elems st target value
          .ok { state := st', scalarQ := [], memoryQ := [], locals }
  | fuel + 1, .ifStmt cond yes no => do
      let cv ← E.evalExprLocals env elems st (some 1) locals cond
      if cv.condTrue then oldStmtFuel E env elems st locals fuel yes
      else match no with
        | none => .ok { state := st, scalarQ := [], memoryQ := [], locals }
        | some s => oldStmtFuel E env elems st locals fuel s
  | fuel + 1, .block body => oldStmtsFuel E env elems st locals fuel body
  | fuel + 1, .forLoop iterator init condition step body =>
      match forValues2 env iterator init condition step with
      | .timeout => .timeout
      | .unsupported e => .unsupported s!"ForLoopStatement: {e}"
      | .ok values => oldLoopFuel E env elems st locals fuel values body iterator
  | fuel + 1, .caseStmt subject items default? mode check => do
      let sv ← E.evalExprLocals env elems st none locals subject
      match check with
      | .none =>
          let selected ← coreMemSelectCase E env elems st sv mode items default?
          match selected with
          | none => .ok { state := st, scalarQ := [], memoryQ := [], locals }
          | some body => oldStmtFuel E env elems st locals fuel body
      | qualifier =>
          let n ← coreMemCaseHits E env elems st sv mode items
          if caseClaimOk qualifier default?.isSome n then
            let selected ← coreMemSelectCase E env elems st sv mode items default?
            match selected with
            | none => .ok { state := st, scalarQ := [], memoryQ := [], locals }
            | some body => oldStmtFuel E env elems st locals fuel body
          else
            .unsupported s!"12.5.3: {caseCheckName qualifier}"
  | fuel + 1, .unsupported kind text => .unsupported s!"{kind}: {text}"

def oldStmtsFuel (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) : Nat → List PStmt → CoreMemExec
  | 0, _ => .timeout
  | fuel + 1, [] => .ok { state := st, scalarQ := [], memoryQ := [], locals }
  | fuel + 1, stmt :: rest => do
      let a ← oldStmtFuel E env elems st locals fuel stmt
      let b ← oldStmtsFuel E env elems a.state a.locals fuel rest
      .ok (CoreMemExec.append a b)

def oldLoopFuel (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) : Nat → List Int → PStmt → String → CoreMemExec
  | 0, _, _, _ => .timeout
  | fuel + 1, [], _, _ => .ok { state := st, scalarQ := [], memoryQ := [], locals }
  | fuel + 1, i :: rest, body, iterator => do
      let a ← oldStmtFuel E (env.bindVal iterator i) elems st locals fuel body
      let b ← oldLoopFuel E env elems a.state a.locals fuel rest body iterator
      .ok (CoreMemExec.append a b)

end

def oldExecStmt (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (stmt : PStmt) : CoreMemExec :=
  oldStmtFuel E env elems st [] 4096 stmt
-- END MERGE-BASE

/-! ## Old (merge base) against new (tip), at the same fuel -/

theorem audit_old_new (fuel : Nat) :
    (∀ (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
      (st : CoreMemState) (locals : SvState) (stmt : PStmt),
      RC (oldStmtFuel E env elems st locals fuel stmt) (E.execStmtFuel env elems st locals fuel stmt)) ∧
    (∀ (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
      (st : CoreMemState) (locals : SvState) (stmts : List PStmt),
      RC (oldStmtsFuel E env elems st locals fuel stmts) (E.execStmtsFuel env elems st locals fuel stmts)) ∧
    (∀ (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
      (st : CoreMemState) (locals : SvState) (values : List Int) (body : PStmt) (iterator : String),
      RC (oldLoopFuel E env elems st locals fuel values body iterator)
        (E.execLoopValuesFuel env elems st locals fuel values body iterator)) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro E env elems st locals stmt
        simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]; exact RC_refl _
      · intro E env elems st locals stmts
        simp only [oldStmtsFuel, CoreMemDesign.execStmtsFuel]; exact RC_refl _
      · intro E env elems st locals values body iterator
        simp only [oldLoopFuel, CoreMemDesign.execLoopValuesFuel]; exact RC_refl _
  | succ k ih =>
      obtain ⟨ihStmt, ihStmts, ihLoop⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro E env elems st locals stmt
        cases stmt with
        | localDecl n t i => simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]; exact RC_refl _
        | automaticDecl n w i => simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]; exact RC_refl _
        | nbaAssign t v => simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]; exact RC_refl _
        | nbaAssignL t v => simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]; exact RC_refl _
        | blockingAssign n v => simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]; exact RC_refl _
        | blockingAssignL t v => simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]; exact RC_refl _
        | unsupported kd t => simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]; exact RC_refl _
        | ifStmt cond yes no =>
            simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]
            refine RC_bind (RC_refl _) (fun cv => ?_)
            by_cases hc : cv.condTrue = true
            · simp only [hc, ↓reduceIte]
              exact ihStmt E env elems st locals yes
            · simp only [hc, Bool.not_eq_true, ↓reduceIte]
              cases no with
              | none => exact RC_refl _
              | some s => exact ihStmt E env elems st locals s
        | block body => exact ihStmts E env elems st locals body
        | forLoop iterator init condition step body =>
            simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]
            rcases audit_forValues2Int32_cases env iterator init condition step with h | h
            · rw [h]
              cases forValues2 env iterator init condition step with
              | timeout => exact RC_refl _
              | unsupported msg => exact RC_refl _
              | ok values => exact ihLoop E env elems st locals values body iterator
            · rw [h]
              exact RC_unsup _ _
        | caseStmt subject items dflt mode check =>
            simp only [oldStmtFuel, CoreMemDesign.execStmtFuel]
            cases check
            · simp only [CaseCheck]
              exact RC_bind (RC_refl _) (fun sv =>
                RC_bind (RC_refl _) (fun selected =>
                  match selected with
                  | none => RC_refl _
                  | some body => ihStmt E env elems st locals body))
            · simp only [CaseCheck]
              exact RC_bind (RC_refl _) (fun sv =>
                RC_bind (RC_refl _) (fun n => by
                  by_cases hclaim : caseClaimOk .unique dflt.isSome n = true
                  · simp only [hclaim, ↓reduceIte]
                    exact RC_bind (RC_refl _) (fun selected =>
                      match selected with
                      | none => RC_refl _
                      | some body => ihStmt E env elems st locals body)
                  · simp only [hclaim, Bool.not_eq_true, ↓reduceIte]
                    exact RC_refl _))
            · simp only [CaseCheck]
              exact RC_bind (RC_refl _) (fun sv =>
                RC_bind (RC_refl _) (fun n => by
                  by_cases hclaim : caseClaimOk .unique0 dflt.isSome n = true
                  · simp only [hclaim, ↓reduceIte]
                    exact RC_bind (RC_refl _) (fun selected =>
                      match selected with
                      | none => RC_refl _
                      | some body => ihStmt E env elems st locals body)
                  · simp only [hclaim, Bool.not_eq_true, ↓reduceIte]
                    exact RC_refl _))
            · simp only [CaseCheck]
              exact RC_bind (RC_refl _) (fun sv =>
                RC_bind (RC_refl _) (fun n => by
                  by_cases hclaim : caseClaimOk .priority dflt.isSome n = true
                  · simp only [hclaim, ↓reduceIte]
                    exact RC_bind (RC_refl _) (fun selected =>
                      match selected with
                      | none => RC_refl _
                      | some body => ihStmt E env elems st locals body)
                  · simp only [hclaim, Bool.not_eq_true, ↓reduceIte]
                    exact RC_refl _))
      · intro E env elems st locals stmts
        cases stmts with
        | nil => simp only [oldStmtsFuel, CoreMemDesign.execStmtsFuel]; exact RC_refl _
        | cons stmt rest =>
            simp only [oldStmtsFuel, CoreMemDesign.execStmtsFuel]
            exact RC_bind (ihStmt E env elems st locals stmt) (fun a =>
              RC_bind (ihStmts E env elems a.state a.locals rest) (fun b => RC_refl _))
      · intro E env elems st locals values body iterator
        cases values with
        | nil => simp only [oldLoopFuel, CoreMemDesign.execLoopValuesFuel]; exact RC_refl _
        | cons i rest =>
            simp only [oldLoopFuel, CoreMemDesign.execLoopValuesFuel]
            exact RC_bind (ihStmt E (env.bindVal iterator i) elems st locals body) (fun a =>
              RC_bind (ihLoop E env elems a.state a.locals rest body iterator) (fun b => RC_refl _))

/-! ## The entry points: old `execStmt` (fixed 4096) against new `execStmt` (4096 + need + runtimeNeed) -/

theorem audit_execStmt_conservative (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (stmt : PStmt) :
    RC (oldExecStmt E env elems st stmt) (E.execStmt env elems st stmt) := by
  unfold oldExecStmt CoreMemDesign.execStmt
  exact RC_le ((audit_old_new 4096).1 E env elems st [] stmt)
    (coreMemFuelMono_stmt (by omega) E env elems st [] stmt)

/-- The decided reading: an old value is the new value unless the new route refuses. -/
theorem audit_execStmt_ok (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (stmt : PStmt) {r : CoreMemExecResult}
    (h : oldExecStmt E env elems st stmt = .ok r) :
    E.execStmt env elems st stmt = .ok r ∨ ∃ m, E.execStmt env elems st stmt = .unsupported m := by
  rcases audit_execStmt_conservative E env elems st stmt with h1 | h1 | h1
  · rw [h] at h1; cases h1
  · exact Or.inl (h1.trans h)
  · exact Or.inr h1

/-! The statement C5 names literally ("the same answer wherever the old decided") is FALSE at the tip, by design:
the merge base decides lf_wrap1's header (one trip, a wrong answer: SV runs 4) and the tip refuses it. -/
#guard forValues2 {} "i" (.int 1342177279)
      (.binary .slt (.genvarRef "i") (.int 1342177280))
      (.binary (.m0 .add) (.genvarRef "i") (.int 1073741825)) == .ok [1342177279]
#guard forValues2Int32 {} "i" (.int 1342177279)
      (.binary .slt (.genvarRef "i") (.int 1342177280))
      (.binary (.m0 .add) (.genvarRef "i") (.int 1073741825)) ==
      .unsupported "for iterator leaves signed 32-bit range"

#print axioms audit_forValues2Int32_cases
#print axioms audit_old_new
#print axioms audit_execStmt_conservative
#print axioms audit_execStmt_ok

end LeanModels.Sv.Kernel.Audit3
