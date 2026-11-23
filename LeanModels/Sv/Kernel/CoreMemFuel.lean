import LeanModels.Sv.Kernel.CoreMemExec
namespace LeanModels.Sv.Kernel
open LeanModels.Sv

 theorem coreMemFuelMono (fuel : Nat) :
    (∀ (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
      (st : CoreMemState) (locals : SvState) (stmt : PStmt) (fuel' : Nat), fuel ≤ fuel' →
      E.execStmtFuel env elems st locals fuel stmt ⊑ E.execStmtFuel env elems st locals fuel' stmt) ∧
    (∀ (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
      (st : CoreMemState) (locals : SvState) (stmts : List PStmt) (fuel' : Nat), fuel ≤ fuel' →
      E.execStmtsFuel env elems st locals fuel stmts ⊑ E.execStmtsFuel env elems st locals fuel' stmts) ∧
    (∀ (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
      (st : CoreMemState) (locals : SvState) (values : List Int) (body : PStmt) (iterator : String) (fuel' : Nat), fuel ≤ fuel' →
      E.execLoopValuesFuel env elems st locals fuel values body iterator ⊑ E.execLoopValuesFuel env elems st locals fuel' values body iterator) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro E env elems st locals stmt fuel' hf
        simp only [CoreMemDesign.execStmtFuel]
        exact Res.timeout_le _
      · intro E env elems st locals stmts fuel' hf
        simp only [CoreMemDesign.execStmtsFuel]
        exact Res.timeout_le _
      · intro E env elems st locals values body iterator fuel' hf
        simp only [CoreMemDesign.execLoopValuesFuel]
        exact Res.timeout_le _
  | succ fuel ih =>
      obtain ⟨ihStmt, ihStmts, ihLoop⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro E env elems st locals stmt fuel' hf
        cases fuel' with
        | zero => omega
        | succ k =>
          have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
          cases stmt with
          | localDecl n t i => simp only [CoreMemDesign.execStmtFuel]; exact Res.le_refl _
          | automaticDecl n w i => simp only [CoreMemDesign.execStmtFuel]; exact Res.le_refl _
          | nbaAssign t v => simp only [CoreMemDesign.execStmtFuel]; exact Res.le_refl _
          | nbaAssignL t v => simp only [CoreMemDesign.execStmtFuel]; exact Res.le_refl _
          | blockingAssign n v => simp only [CoreMemDesign.execStmtFuel]; exact Res.le_refl _
          | blockingAssignL t v => simp only [CoreMemDesign.execStmtFuel]; exact Res.le_refl _
          | unsupported k t => simp only [CoreMemDesign.execStmtFuel]; exact Res.le_refl _
          | ifStmt cond yes no =>
              simp only [CoreMemDesign.execStmtFuel]
              refine Res.le_bind (Res.le_refl _) (fun cv => ?_)
              by_cases hc : cv.condTrue = true
              · simp only [hc, ↓reduceIte]
                exact ihStmt E env elems st locals yes k hk
              · simp only [hc, Bool.not_eq_true, ↓reduceIte]
                cases no with
                | none => exact Res.le_refl _
                | some s => exact ihStmt E env elems st locals s k hk
          | block body => exact ihStmts E env elems st locals body k hk
          | forLoop iterator init condition step body =>
              simp only [CoreMemDesign.execStmtFuel]
              generalize hv : forValues2Int32 env iterator init condition step = result
              cases result with
              | timeout => exact Res.le_refl _
              | unsupported msg => exact Res.le_refl _
              | ok values => exact ihLoop E env elems st locals values body iterator k hk
          | caseStmt subject items dflt mode check =>
              simp only [CoreMemDesign.execStmtFuel]
              cases check
              · simp only [CaseCheck]
                exact Res.le_bind (Res.le_refl _) (fun sv =>
                  Res.le_bind (Res.le_refl _) (fun selected =>
                    match selected with
                    | none => Res.le_refl _
                    | some body => ihStmt E env elems st locals body k hk))
              · simp only [CaseCheck]
                exact Res.le_bind (Res.le_refl _) (fun sv =>
                  Res.le_bind (Res.le_refl _) (fun n => by
                    by_cases hclaim : caseClaimOk .unique dflt.isSome n = true
                    · simp only [hclaim, ↓reduceIte]
                      exact Res.le_bind (Res.le_refl _) (fun selected =>
                        match selected with
                        | none => Res.le_refl _
                        | some body => ihStmt E env elems st locals body k hk)
                    · simp only [hclaim, Bool.not_eq_true, ↓reduceIte]
                      exact Res.le_refl _))
              · simp only [CaseCheck]
                exact Res.le_bind (Res.le_refl _) (fun sv =>
                  Res.le_bind (Res.le_refl _) (fun n => by
                    by_cases hclaim : caseClaimOk .unique0 dflt.isSome n = true
                    · simp only [hclaim, ↓reduceIte]
                      exact Res.le_bind (Res.le_refl _) (fun selected =>
                        match selected with
                        | none => Res.le_refl _
                        | some body => ihStmt E env elems st locals body k hk)
                    · simp only [hclaim, Bool.not_eq_true, ↓reduceIte]
                      exact Res.le_refl _))
              · simp only [CaseCheck]
                exact Res.le_bind (Res.le_refl _) (fun sv =>
                  Res.le_bind (Res.le_refl _) (fun n => by
                    by_cases hclaim : caseClaimOk .priority dflt.isSome n = true
                    · simp only [hclaim, ↓reduceIte]
                      exact Res.le_bind (Res.le_refl _) (fun selected =>
                        match selected with
                        | none => Res.le_refl _
                        | some body => ihStmt E env elems st locals body k hk)
                    · simp only [hclaim, Bool.not_eq_true, ↓reduceIte]
                      exact Res.le_refl _))
      · intro E env elems st locals stmts fuel' hf
        cases fuel' with
        | zero => omega
        | succ k =>
          have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
          cases stmts with
          | nil => simp only [CoreMemDesign.execStmtsFuel]; exact Res.le_refl _
          | cons stmt rest =>
              simp only [CoreMemDesign.execStmtsFuel]
              exact Res.le_bind (ihStmt E env elems st locals stmt k hk) (fun a =>
                Res.le_bind (ihStmts E env elems a.state a.locals rest k hk)
                  (fun b => Res.le_refl _))
      · intro E env elems st locals values body iterator fuel' hf
        cases fuel' with
        | zero => omega
        | succ k =>
          have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
          cases values with
          | nil => simp only [CoreMemDesign.execLoopValuesFuel]; exact Res.le_refl _
          | cons i rest =>
              simp only [CoreMemDesign.execLoopValuesFuel]
              exact Res.le_bind
                (ihStmt E (env.bindVal iterator i) elems st locals body k hk)
                (fun a => Res.le_bind
                  (ihLoop E env elems a.state a.locals rest body iterator k hk)
                  (fun b => Res.le_refl _))
end LeanModels.Sv.Kernel
