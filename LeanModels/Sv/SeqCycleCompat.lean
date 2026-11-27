import LeanModels.Sv.SeqCycle

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

def CoreMemDesign.ProcOkI_prev (E : CoreMemDesign) (i : Nat) : CoreMemProc → Prop
  | .assign (.ident n) v => LeanModels.Sv.PExpr.hasFunctionCall v = false ∧
      (LeanModels.Sv.PExpr.hasMemoryRead v = false → ∃ c, E.compiledAssigns[i]? = some (some c)) ∧
      (E.scalarWidth? n).isSome = true ∧ n ∉ E.resolvedNets
  | .edge f => f.body.edgeOkB = true ∧ f.body.need E.env ≤ 4096
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.edgeOkB = true ∧ f.body.need E.env ≤ 4096
      | none => False
  | _ => False

def CoreMemDesign.ProcOk_prev (E : CoreMemDesign) (clk : String) (i : Nat) : CoreMemProc → Prop
  | .assign (.ident n) v => LeanModels.Sv.PExpr.hasFunctionCall v = false ∧
      (LeanModels.Sv.PExpr.hasMemoryRead v = false → ∃ c, E.compiledAssigns[i]? = some (some c)) ∧
      (E.scalarWidth? n).isSome = true ∧ n ∉ E.resolvedNets
  | .edge f => f.clock = clk ∧ f.edge = .posedge ∧ f.body.edgeOkB = true ∧ f.body.need E.env ≤ 4096
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.clock = clk ∧ f.edge = .posedge ∧ f.body.edgeOkB = true ∧ f.body.need E.env ≤ 4096
      | none => False
  | _ => False

def CoreMemDesign.procOkIB_prev (E : CoreMemDesign) (i : Nat) : CoreMemProc → Bool
  | .assign (.ident n) v => !LeanModels.Sv.PExpr.hasFunctionCall v &&
      (LeanModels.Sv.PExpr.hasMemoryRead v || (match E.compiledAssigns[i]? with
        | some (some _) => true
        | _ => false)) && (E.scalarWidth? n).isSome && !E.resolvedNets.contains n
  | .edge f => f.body.edgeOkB && decide (f.body.need E.env ≤ 4096)
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.edgeOkB && decide (f.body.need E.env ≤ 4096)
      | none => false
  | _ => false

def CoreMemDesign.procOkB_prev (E : CoreMemDesign) (clk : String) (i : Nat) : CoreMemProc → Bool
  | .assign (.ident n) v => !LeanModels.Sv.PExpr.hasFunctionCall v &&
      (LeanModels.Sv.PExpr.hasMemoryRead v || (match E.compiledAssigns[i]? with
        | some (some _) => true
        | _ => false)) && (E.scalarWidth? n).isSome && !E.resolvedNets.contains n
  | .edge f => f.clock == clk && decide (f.edge = .posedge) && f.body.edgeOkB && decide (f.body.need E.env ≤ 4096)
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.clock == clk && decide (f.edge = .posedge) && f.body.edgeOkB && decide (f.body.need E.env ≤ 4096)
      | none => false
  | _ => false

def CoreMemDesign.ProcShapeI_prev (E : CoreMemDesign) : CoreMemProc → Prop
  | .assign _ _ => True
  | .edge f => f.body.edgeOkB = true ∧ f.body.need E.env ≤ 4096
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.edgeOkB = true ∧ f.body.need E.env ≤ 4096
      | none => False
  | _ => False

theorem CoreMemDesign.ProcOkI_prev_conservative {E : CoreMemDesign} {i : Nat} {p : CoreMemProc}
    (h : E.ProcOkI_prev i p) : E.ProcOkI i p := by
  cases p with
  | assign t v => cases t <;> simpa [CoreMemDesign.ProcOkI_prev, CoreMemDesign.ProcOkI]
  | edge f => simpa [CoreMemDesign.ProcOkI_prev, CoreMemDesign.ProcOkI] using h
  | event evs body =>
      cases hfe : coreMemEventEdge? evs body with
      | none => simp [CoreMemDesign.ProcOkI_prev, CoreMemDesign.ProcOkI, hfe] at h
      | some f => simp [CoreMemDesign.ProcOkI_prev, CoreMemDesign.ProcOkI, hfe] at h ⊢; exact h
  | comb body => simp [CoreMemDesign.ProcOkI_prev] at h
  | primitive _ _ _ | initial _ | implicit _ | latch _ | unsupported _ _ =>
      simp [CoreMemDesign.ProcOkI_prev] at h

theorem CoreMemDesign.ProcOk_prev_conservative {E : CoreMemDesign} {clk : String} {i : Nat} {p : CoreMemProc}
    (h : E.ProcOk_prev clk i p) : E.ProcOk clk i p := by
  cases p with
  | assign t v => cases t <;> simpa [CoreMemDesign.ProcOk_prev, CoreMemDesign.ProcOk]
  | edge f => simpa [CoreMemDesign.ProcOk_prev, CoreMemDesign.ProcOk] using h
  | event evs body =>
      cases hfe : coreMemEventEdge? evs body with
      | none => simp [CoreMemDesign.ProcOk_prev, CoreMemDesign.ProcOk, hfe] at h
      | some f => simp [CoreMemDesign.ProcOk_prev, CoreMemDesign.ProcOk, hfe] at h ⊢; exact h
  | comb body => simp [CoreMemDesign.ProcOk_prev] at h
  | primitive _ _ _ | initial _ | implicit _ | latch _ | unsupported _ _ =>
      simp [CoreMemDesign.ProcOk_prev] at h

theorem CoreMemDesign.procOkIB_prev_conservative {E : CoreMemDesign} {i : Nat} {p : CoreMemProc}
    (h : E.procOkIB_prev i p = true) : E.procOkIB i p = true := by
  cases p with
  | assign t v =>
      cases t with
      | ident n =>
          simp only [CoreMemDesign.procOkIB_prev, CoreMemDesign.procOkIB] at h ⊢
          assumption
      | _ => simp [CoreMemDesign.procOkIB_prev] at h
  | edge f => simpa [CoreMemDesign.procOkIB_prev, CoreMemDesign.procOkIB] using h
  | event evs body =>
      cases hfe : coreMemEventEdge? evs body with
      | none => simp [CoreMemDesign.procOkIB_prev, CoreMemDesign.procOkIB, hfe] at h
      | some f => simp [CoreMemDesign.procOkIB_prev, CoreMemDesign.procOkIB, hfe] at h ⊢; exact h
  | comb body => simp [CoreMemDesign.procOkIB_prev] at h
  | primitive _ _ _ | initial _ | implicit _ | latch _ | unsupported _ _ =>
      simp [CoreMemDesign.procOkIB_prev] at h

theorem CoreMemDesign.procOkB_prev_conservative {E : CoreMemDesign} {clk : String} {i : Nat} {p : CoreMemProc}
    (h : E.procOkB_prev clk i p = true) : E.procOkB clk i p = true := by
  cases p with
  | assign t v =>
      cases t with
      | ident n =>
          simp only [CoreMemDesign.procOkB_prev, CoreMemDesign.procOkB] at h ⊢
          assumption
      | _ => simp [CoreMemDesign.procOkB_prev] at h
  | edge f => simpa [CoreMemDesign.procOkB_prev, CoreMemDesign.procOkB] using h
  | event evs body =>
      cases hfe : coreMemEventEdge? evs body with
      | none => simp [CoreMemDesign.procOkB_prev, CoreMemDesign.procOkB, hfe] at h
      | some f => simp [CoreMemDesign.procOkB_prev, CoreMemDesign.procOkB, hfe] at h ⊢; exact h
  | comb body => simp [CoreMemDesign.procOkB_prev] at h
  | primitive _ _ _ | initial _ | implicit _ | latch _ | unsupported _ _ =>
      simp [CoreMemDesign.procOkB_prev] at h

theorem CoreMemDesign.ProcShapeI_prev_conservative {E : CoreMemDesign} {p : CoreMemProc}
    (h : E.ProcShapeI_prev p) : E.ProcShapeI p := by
  cases p with
  | assign _ _ => trivial
  | edge f => simpa [CoreMemDesign.ProcShapeI_prev, CoreMemDesign.ProcShapeI] using h
  | event evs body =>
      cases hfe : coreMemEventEdge? evs body with
      | none => simp [CoreMemDesign.ProcShapeI_prev, CoreMemDesign.ProcShapeI, hfe] at h
      | some f => simp [CoreMemDesign.ProcShapeI_prev, CoreMemDesign.ProcShapeI, hfe] at h ⊢; exact h
  | comb body => simp [CoreMemDesign.ProcShapeI_prev] at h
  | primitive _ _ _ | initial _ | implicit _ | latch _ | unsupported _ _ =>
      simp [CoreMemDesign.ProcShapeI_prev] at h

end LeanModels.Sv.Kernel
