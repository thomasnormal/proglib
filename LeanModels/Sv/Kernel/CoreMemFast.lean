import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Kernel.ArrayFast

/-!
# Scalar-array instrument for canonical memory E

This is an executor view over `CoreMemState`: native `MemState` remains the
only memory representation, while scalar declarations use the existing
`ArrayFast` snapshot.  The scalar write and NBA bridges are used by a
whole-cycle `fastStep`; this remains an executable optimization view and has
no refinement theorem until its event-ordering obligations are reproved.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

structure CoreMemFastState where
  scalar : FastConfig
  /-- The canonical state's data-backed scalar cache, retained alongside the
      array view so this bridge remains a full `CoreMemState` bridge. -/
  scalarCache : Array Val
  memory : MemState

def CoreMemFastState.toState (s : CoreMemFastState) : CoreMemState :=
  { scalar := s.scalar.store, scalarCache := s.scalarCache, memory := s.memory }

def CoreMemFastState.ofState (E : CoreMemDesign) (s : CoreMemState) : CoreMemFastState :=
  { scalar := FastConfig.ofConfig E.scalar
      { store := s.scalar, active := [], k := 0 }
    scalarCache := s.scalarCache
    memory := s.memory }

theorem CoreMemFastState.ofState_toState (E : CoreMemDesign) (s : CoreMemState) :
    (CoreMemFastState.ofState E s).toState = s := by
  cases s
  simp [CoreMemFastState.ofState, CoreMemFastState.toState,
    FastConfig.ofConfig_store]

def CoreMemDesign.fastScalarWrite (E : CoreMemDesign) (s : CoreMemFastState)
    (name : String) (v : LVec) : Res CoreMemFastState :=
  match E.scalar.resolve name with
  | none => .unsupported s!"10.3: continuous target '{name}' is undeclared"
  | some x =>
      match x.path with
      | [] =>
          let old := s.scalar.cells.getD x.decl (s.scalar.fallback x)
          let converted := Val.ofLVec old.ty v
          let cells := s.scalar.cells.setIfInBounds x.decl converted
          .ok { s with scalar := { s.scalar with cells }, scalarCache := cells }
      | _ => .unsupported "10.3.2: non-flat scalar target"

def CoreMemDesign.fastScalarAssignAt (E : CoreMemDesign) (s : CoreMemFastState)
    (view : SvState) (index : Nat) (name : String) (value : PExpr) : Res CoreMemFastState := do
  let width ← match E.scalarWidth? name with
    | some w => .ok w
    | none => .unsupported s!"10.3: continuous target '{name}' is undeclared"
  let v ← E.evalScalarAssignAtView E.env E.elems s.toState view (some width) index value
  E.fastScalarWrite s name v

/-! A fast scalar write is valid only while the resolved target is a flat
    cell in the current array.  The check is deliberately a Bool so the
    executor can fall back to the authoritative source-shaped settle for
    declarations outside this instrument's invariant. -/
def CoreMemDesign.fastScalarFlatB (E : CoreMemDesign) (s : CoreMemFastState)
    (name : String) : Bool :=
  match E.scalar.resolve name with
  | some x => x.path == [] && x.decl < s.scalar.cells.size
  | none => false

def CoreMemDesign.fastSettleFallback (E : CoreMemDesign)
    (env : IEnv) (elems : List (String × Nat)) (s : CoreMemFastState)
    (view : SvState) (index : Nat) (procs : List CoreMemProc) :
    Res (CoreMemFastState × SvState) :=
  match E.settleAssignAt env elems s.toState view index procs with
  | .ok (st', view') => .ok (CoreMemFastState.ofState E st', view')
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

def CoreMemDesign.fastSettleAssignAt (E : CoreMemDesign)
    (env : IEnv) (elems : List (String × Nat)) (s : CoreMemFastState)
    (view : SvState) (index : Nat) : List CoreMemProc →
    Res (CoreMemFastState × SvState)
  | [] => .ok (s, view)
  | .assign (.ident name) value :: rest => do
      if E.resolvedNets.contains name then
        E.fastSettleFallback env elems s view index
          (.assign (.ident name) value :: rest)
      else if E.fastScalarFlatB s name then
        let s' ← E.fastScalarAssignAt s view index name value
        let v ← E.evalScalarAssignAtView env elems s.toState view
          (E.scalarWidth? name |>.map some |>.getD none) index value
        E.fastSettleAssignAt env elems s' (SvState.set view name v) (index + 1) rest
      else
        E.fastSettleFallback env elems s view index (.assign (.ident name) value :: rest)
  | .assign (.arrayElem name [indexExpr]) value :: rest => do
      match E.memDecl? name with
      | none =>
          E.fastSettleFallback env elems s view index
            (.assign (.arrayElem name [indexExpr]) value :: rest)
      | some md =>
          let st := s.toState
          let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
          let st' ← E.writeMemoryAssign env elems st
            (.arrayElem name [indexExpr]) md v
          E.fastSettleAssignAt env elems (CoreMemFastState.ofState E st')
            view (index + 1) rest
  | .edge _ :: rest => E.fastSettleAssignAt env elems s view (index + 1) rest
  | .initial _ :: rest => E.fastSettleAssignAt env elems s view (index + 1) rest
  | .comb _ :: rest => E.fastSettleAssignAt env elems s view (index + 1) rest
  | .implicit _ :: rest => E.fastSettleAssignAt env elems s view (index + 1) rest
  | .latch _ :: rest => E.fastSettleAssignAt env elems s view (index + 1) rest
  | .event _ _ :: rest => E.fastSettleAssignAt env elems s view (index + 1) rest
  | .assign target value :: rest =>
      E.fastSettleFallback env elems s view index (.assign target value :: rest)
  | .unsupported kind text :: _ => .unsupported s!"{kind}: {text}"

theorem CoreMemDesign.fastScalarWrite_toState
    (E : CoreMemDesign) (s s' : CoreMemFastState) (name : String) (v : LVec)
    (x : VarId)
    (hresolve : E.scalar.resolve name = some x)
    (hpath : x.path = [])
    (hbound : x.decl < s.scalar.cells.size)
    (h : E.fastScalarWrite s name v = .ok s') :
    s'.toState = { s.toState with
      scalar := E.scalar.setName s.toState.scalar name v
      scalarCache := s'.scalarCache } := by
  unfold CoreMemDesign.fastScalarWrite at h
  rw [hresolve] at h
  cases x with
  | mk path decl =>
    cases path with
    | nil =>
      simp only [Res.ok.injEq] at h
      cases h
      unfold CoreMemFastState.toState
      simp only [FastConfig.store]
      rw [arrayStore_set_flat_store s.scalar.cells s.scalar.fallback
        { path := [], decl } (Val.ofLVec
          ((s.scalar.cells.getD decl (s.scalar.fallback { path := [], decl })).ty) v)
        rfl hbound]
      simp [Elab.setName, hresolve, arrayStore, hbound]
    | cons head tail =>
      simp_all

theorem CoreMemDesign.fastScalarAssignAt_toState
    (E : CoreMemDesign) (s s' : CoreMemFastState) (view : SvState)
    (index : Nat) (name : String) (value : PExpr) (width : Nat) (v : LVec)
    (x : VarId)
    (hwidth : E.scalarWidth? name = some width)
    (hresolve : E.scalar.resolve name = some x)
    (hpath : x.path = [])
    (hbound : x.decl < s.scalar.cells.size)
    (hv : E.evalScalarAssignAtView E.env E.elems s.toState view
      (some width) index value = .ok v)
    (h : E.fastScalarAssignAt s view index name value = .ok s') :
    s'.toState = { s.toState with
      scalar := E.scalar.setName s.toState.scalar name v
      scalarCache := s'.scalarCache } := by
  unfold CoreMemDesign.fastScalarAssignAt at h
  simp [hwidth] at h
  rw [hv] at h
  obtain ⟨a, ha, hwrite⟩ := h
  have hav : a = v := (Res.ok.inj ha).symm
  subst a
  exact E.fastScalarWrite_toState s s' name v x hresolve hpath hbound hwrite

theorem CoreMemDesign.fastSettleAssignAt_single_ident_toState
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s s' : CoreMemFastState) (view view' : SvState) (index : Nat)
    (name : String) (value : PExpr) (width : Nat) (v : LVec) (x : VarId)
    (hwidth : E.scalarWidth? name = some width)
    (hresolve : E.scalar.resolve name = some x)
    (hpath : x.path = []) (hbound : x.decl < s.scalar.cells.size)
    (hnet : name ∉ E.resolvedNets)
    (hflat : E.fastScalarFlatB s name = true)
    (henv : env = E.env) (helems : elems = E.elems)
    (hv : E.evalScalarAssignAtView env elems s.toState view
      (some width) index value = .ok v)
    (h : E.fastSettleAssignAt env elems s view index
      [.assign (.ident name) value] = .ok (s', view')) :
    s'.toState = { s.toState with
      scalar := E.scalar.setName s.toState.scalar name v
      scalarCache := s'.scalarCache } ∧
      view' = SvState.set view name v := by
  simp [CoreMemDesign.fastSettleAssignAt, hflat, hwidth, hv, hnet] at h
  obtain ⟨a, ha, hs⟩ := h
  rcases hs with ⟨rfl, rfl⟩
  have hv' : E.evalScalarAssignAtView E.env E.elems s.toState view
      (some width) index value = .ok v := by simpa [henv, helems] using hv
  have hstate := E.fastScalarAssignAt_toState s a view index name value
    width v x hwidth hresolve hpath hbound hv' ha
  exact ⟨hstate, rfl⟩

theorem CoreMemDesign.fastSettleAssignAt_skip_cons_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (rest : List CoreMemProc) (s' : CoreMemFastState) (view' : SvState)
    (e : CoreMemEdge)
    (hfast : E.fastSettleAssignAt env elems s view index (.edge e :: rest) =
      .ok (s', view'))
    (htail : E.settleAssignAt env elems s.toState view (index + 1) rest =
      .ok (s'.toState, view')) :
    E.settleAssignAt env elems s.toState view index (.edge e :: rest) =
      .ok (s'.toState, view') := by
  simpa [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt] using htail

theorem CoreMemDesign.fastSettleAssignAt_initial_cons_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (body : PStmt) (rest : List CoreMemProc) (s' : CoreMemFastState) (view' : SvState)
    (hfast : E.fastSettleAssignAt env elems s view index (.initial body :: rest) =
      .ok (s', view'))
    (htail : E.settleAssignAt env elems s.toState view (index + 1) rest =
      .ok (s'.toState, view')) :
    E.settleAssignAt env elems s.toState view index (.initial body :: rest) =
      .ok (s'.toState, view') := by
  simpa [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt] using htail

theorem CoreMemDesign.fastSettleAssignAt_comb_cons_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (body : PStmt) (rest : List CoreMemProc) (s' : CoreMemFastState) (view' : SvState)
    (hfast : E.fastSettleAssignAt env elems s view index (.comb body :: rest) =
      .ok (s', view'))
    (htail : E.settleAssignAt env elems s.toState view (index + 1) rest =
      .ok (s'.toState, view')) :
    E.settleAssignAt env elems s.toState view index (.comb body :: rest) =
      .ok (s'.toState, view') := by
  simpa [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt] using htail

theorem CoreMemDesign.fastSettleAssignAt_implicit_cons_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (body : PStmt) (rest : List CoreMemProc) (s' : CoreMemFastState) (view' : SvState)
    (hfast : E.fastSettleAssignAt env elems s view index (.implicit body :: rest) =
      .ok (s', view'))
    (htail : E.settleAssignAt env elems s.toState view (index + 1) rest =
      .ok (s'.toState, view')) :
    E.settleAssignAt env elems s.toState view index (.implicit body :: rest) =
      .ok (s'.toState, view') := by
  simpa [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt] using htail

theorem CoreMemDesign.fastSettleAssignAt_single_array_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (name : String) (indexExpr : PExpr) (value : PExpr)
    (md : CoreMemDecl) (v : LVec) (s' : CoreMemFastState) (view' : SvState)
    (hmem : E.memDecl? name = some md)
    (hv : E.evalExpr env elems s.toState (some md.shape.elemWidth) value = .ok v)
    (h : E.fastSettleAssignAt env elems s view index
      [.assign (.arrayElem name [indexExpr]) value] = .ok (s', view')) :
    E.settleAssignAt env elems s.toState view index
      [.assign (.arrayElem name [indexExpr]) value] =
      .ok (s'.toState, view') := by
  simp [CoreMemDesign.fastSettleAssignAt, hmem, hv] at h
  simp [CoreMemDesign.settleAssignAt, hmem, hv]
  rcases h with ⟨a, ha, hof, hview⟩
  have hstate : a = s'.toState := by
    calc
      a = (CoreMemFastState.ofState E a).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = s'.toState := congrArg CoreMemFastState.toState hof
  exact ⟨a, ha, hstate, hview⟩

theorem CoreMemDesign.fastSettleAssignAt_two_array_refines
    (E : CoreMemDesign) (s a₁ a₂ : CoreMemFastState) (view : SvState)
    (index : Nat) (name₁ name₂ : String) (indexExpr₁ indexExpr₂ value₁ value₂ : PExpr)
    (md₁ md₂ : CoreMemDecl) (v₁ v₂ : LVec)
    (hmem₁ : E.memDecl? name₁ = some md₁)
    (hmem₂ : E.memDecl? name₂ = some md₂)
    (hv₁ : E.evalExpr E.env E.elems s.toState (some md₁.shape.elemWidth) value₁ = .ok v₁)
    (hv₂ : E.evalExpr E.env E.elems a₁.toState (some md₂.shape.elemWidth) value₂ = .ok v₂)
    (h₁ : E.fastSettleAssignAt E.env E.elems s view index
      [.assign (.arrayElem name₁ [indexExpr₁]) value₁] = .ok (a₁, view))
    (h₂ : E.fastSettleAssignAt E.env E.elems a₁ view (index + 1)
      [.assign (.arrayElem name₂ [indexExpr₂]) value₂] = .ok (a₂, view)) :
    E.settleAssignAt E.env E.elems s.toState view index
      [.assign (.arrayElem name₁ [indexExpr₁]) value₁,
       .assign (.arrayElem name₂ [indexExpr₂]) value₂] =
      .ok (a₂.toState, view) := by
  simp [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt,
    hmem₁, hmem₂, hv₁, hv₂] at h₁ h₂ ⊢
  rcases h₁ with ⟨a, ha, ha₁⟩
  rcases h₂ with ⟨b, hb, hb₂⟩
  have ha_to : a = a₁.toState := by
    calc
      a = (CoreMemFastState.ofState E a).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = a₁.toState := congrArg CoreMemFastState.toState ha₁
  have hb_to : b = a₂.toState := by
    calc
      b = (CoreMemFastState.ofState E b).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = a₂.toState := congrArg CoreMemFastState.toState hb₂
  refine ⟨a, ha, v₂, ?_, ?_⟩
  · simpa [ha_to] using hv₂
  · simpa [ha_to, hb_to] using hb

theorem CoreMemDesign.fastSettleAssignAt_scalar_array_refines
    (E : CoreMemDesign) (s a₁ a₂ : CoreMemFastState) (view : SvState)
    (index : Nat) (name₁ name₂ : String) (value₁ value₂ indexExpr₂ : PExpr)
    (width₁ : Nat) (v₁ v₂ : LVec) (x₁ : VarId) (md₂ : CoreMemDecl)
    (hwidth₁ : E.scalarWidth? name₁ = some width₁)
    (hresolve₁ : E.scalar.resolve name₁ = some x₁)
    (hpath₁ : x₁.path = [])
    (hbound₁ : x₁.decl < s.scalar.cells.size)
    (hnet₁ : name₁ ∉ E.resolvedNets)
    (hmem₂ : E.memDecl? name₂ = some md₂)
    (hv₁ : E.evalScalarAssignAtView E.env E.elems s.toState view
      (some width₁) index value₁ = .ok v₁)
    (hv₂ : E.evalExpr E.env E.elems a₁.toState
      (some md₂.shape.elemWidth) value₂ = .ok v₂)
    (h₁ : E.fastScalarAssignAt s view index name₁ value₁ = .ok a₁)
    (hstate₁ : a₁.toState = E.setScalarState s.toState name₁ v₁)
    (h₂ : E.fastSettleAssignAt E.env E.elems a₁
      (SvState.set view name₁ v₁) (index + 1)
      [.assign (.arrayElem name₂ [indexExpr₂]) value₂] =
      .ok (a₂, SvState.set view name₁ v₁)) :
    E.settleAssignAt E.env E.elems s.toState view index
      [.assign (.ident name₁) value₁,
       .assign (.arrayElem name₂ [indexExpr₂]) value₂] =
      .ok (a₂.toState, SvState.set view name₁ v₁) := by
  have hs₁ := E.fastScalarAssignAt_toState s a₁ view index name₁ value₁
    width₁ v₁ x₁ hwidth₁ hresolve₁ hpath₁ hbound₁ hv₁ h₁
  have hv₂' := hv₂
  rw [hstate₁] at hv₂'
  simp [CoreMemDesign.fastSettleAssignAt, hmem₂, hv₂'] at h₂
  rcases h₂ with ⟨b, hb, hb₂⟩
  rcases hb₂ with ⟨c, hbc, hc₂⟩
  have hbv : b = v₂ := Res.ok.inj (hb.symm.trans hv₂)
  have hc_to : c = a₂.toState := by
    calc
      c = (CoreMemFastState.ofState E c).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = a₂.toState := congrArg CoreMemFastState.toState hc₂
  have hbc' := hbc
  rw [hstate₁, hbv, hc_to] at hbc'
  simp [CoreMemDesign.settleAssignAt, hwidth₁, hmem₂, hv₁, hv₂', hstate₁,
    hnet₁]
  exact hbc'

theorem CoreMemDesign.fastSettleAssignAt_array_scalar_refines
    (E : CoreMemDesign) (s a₁ a₂ : CoreMemFastState) (view : SvState)
    (index : Nat) (name₁ name₂ : String) (indexExpr₁ value₁ value₂ : PExpr)
    (md₁ : CoreMemDecl) (v₁ v₂ : LVec) (width₂ : Nat) (x₂ : VarId)
    (hmem₁ : E.memDecl? name₁ = some md₁)
    (hwidth₂ : E.scalarWidth? name₂ = some width₂)
    (hresolve₂ : E.scalar.resolve name₂ = some x₂)
    (hpath₂ : x₂.path = [])
    (hbound₂ : x₂.decl < a₁.scalar.cells.size)
    (hnet₂ : name₂ ∉ E.resolvedNets)
    (hv₁ : E.evalExpr E.env E.elems s.toState
      (some md₁.shape.elemWidth) value₁ = .ok v₁)
    (hv₂ : E.evalScalarAssignAtView E.env E.elems a₁.toState view
      (some width₂) (index + 1) value₂ = .ok v₂)
    (h₁ : E.fastSettleAssignAt E.env E.elems s view index
      [.assign (.arrayElem name₁ [indexExpr₁]) value₁] = .ok (a₁, view))
    (h₂ : E.fastScalarAssignAt a₁ view (index + 1) name₂ value₂ = .ok a₂)
    (hstate₂ : a₂.toState = E.setScalarState a₁.toState name₂ v₂) :
    E.settleAssignAt E.env E.elems s.toState view index
      [.assign (.arrayElem name₁ [indexExpr₁]) value₁,
       .assign (.ident name₂) value₂] =
      .ok (a₂.toState, SvState.set view name₂ v₂) := by
  have hs₂ := E.fastScalarAssignAt_toState a₁ a₂ view (index + 1) name₂ value₂
    width₂ v₂ x₂ hwidth₂ hresolve₂ hpath₂ hbound₂ hv₂ h₂
  simp [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt,
    hmem₁, hv₁] at h₁
  rcases h₁ with ⟨c, hc, hc₁⟩
  have hc_to : c = a₁.toState := by
    calc
      c = (CoreMemFastState.ofState E c).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = a₁.toState := congrArg CoreMemFastState.toState hc₁
  have hc' := hc
  rw [hc_to] at hc'
  simp [CoreMemDesign.settleAssignAt, hmem₁, hwidth₂, hv₁, hstate₂, hc',
    hnet₂]
  exact ⟨v₂, hv₂, rfl, rfl⟩

theorem CoreMemDesign.settleAssignAt_two_ident_fast_refines
    (E : CoreMemDesign) (s a₁ a₂ : CoreMemFastState) (view : SvState)
    (index : Nat) (name₁ name₂ : String) (value₁ value₂ : PExpr)
    (width₁ width₂ : Nat) (v₁ v₂ : LVec) (x₁ x₂ : VarId)
    (hwidth₁ : E.scalarWidth? name₁ = some width₁)
    (hwidth₂ : E.scalarWidth? name₂ = some width₂)
    (hresolve₁ : E.scalar.resolve name₁ = some x₁)
    (hresolve₂ : E.scalar.resolve name₂ = some x₂)
    (hpath₁ : x₁.path = []) (hpath₂ : x₂.path = [])
    (hbound₁ : x₁.decl < s.scalar.cells.size)
    (hbound₂ : x₂.decl < a₁.scalar.cells.size)
    (hnet₁ : name₁ ∉ E.resolvedNets)
    (hnet₂ : name₂ ∉ E.resolvedNets)
    (hv₁ : E.evalScalarAssignAtView E.env E.elems s.toState view
      (some width₁) index value₁ = .ok v₁)
    (hv₂ : E.evalScalarAssignAtView E.env E.elems a₁.toState
      (SvState.set view name₁ v₁) (some width₂) (index + 1) value₂ = .ok v₂)
    (h₁ : E.fastScalarAssignAt s view index name₁ value₁ = .ok a₁)
    (h₂ : E.fastScalarAssignAt a₁ (SvState.set view name₁ v₁)
      (index + 1) name₂ value₂ = .ok a₂)
    (hstate₁ : a₁.toState = E.setScalarState s.toState name₁ v₁)
    (hstate₂ : a₂.toState = E.setScalarState a₁.toState name₂ v₂) :
    E.settleAssignAt E.env E.elems s.toState view index
      [.assign (.ident name₁) value₁, .assign (.ident name₂) value₂] =
      .ok (a₂.toState, SvState.set (SvState.set view name₁ v₁) name₂ v₂) := by
  have hs₁ := E.fastScalarAssignAt_toState s a₁ view index name₁ value₁
    width₁ v₁ x₁ hwidth₁ hresolve₁ hpath₁ hbound₁ hv₁ h₁
  have hs₂ := E.fastScalarAssignAt_toState a₁ a₂ (SvState.set view name₁ v₁)
    (index + 1) name₂ value₂ width₂ v₂ x₂ hwidth₂ hresolve₂ hpath₂ hbound₂ hv₂ h₂
  have hv₂' := hv₂
  rw [hstate₁] at hv₂'
  simp [CoreMemDesign.settleAssignAt, hwidth₁, hwidth₂, hv₁, hv₂', hstate₁,
    hstate₂, hnet₁, hnet₂]

/-! ## Direct scalar NBA commit

The edge executor already samples scalar NBAs into `NbaQueue2`.  Committing
that queue through `Elab1.commit` rebuilds a chain of function-valued stores;
the array route applies the same source-shaped window writes to the existing
cache instead.  The refinement below is deliberately conditional on the
ordinary flat declaration invariant: a queue entry must resolve to a flat
declared cell in the cache.  Designs outside that invariant remain on the
authoritative route rather than being approximated.
-/

def CoreMemDesign.fastCommitScalar (E : CoreMemDesign) (s : CoreMemFastState) :
    NbaQueue2 → Res CoreMemFastState
  | [] => .ok s
  | (name, lo, part) :: rest =>
      match E.scalarEdge.base.resolve name with
      | none => .unsupported s!"11.5.1: scalar NBA target '{name}' is undeclared"
      | some x =>
          match x.path with
          | _ :: _ => .unsupported "11.5.1: non-flat scalar NBA target"
          | [] =>
              if x.decl < s.scalar.cells.size then
                let old := s.scalar.cells.getD x.decl (s.scalar.fallback x)
                let cells := s.scalar.cells.setIfInBounds x.decl (old.write lo part)
                E.fastCommitScalar
                  { s with
                      scalar := { s.scalar with cells }
                      scalarCache := cells } rest
              else
                .unsupported "11.5.1: scalar NBA target is outside the flat cache"

def CoreMemDesign.FlatScalarQueue (E : CoreMemDesign) (s : CoreMemFastState)
    (q : NbaQueue2) : Prop :=
  ∀ u ∈ q, ∃ x,
    E.scalarEdge.base.resolve u.1 = some x ∧
      x.path = [] ∧ x.decl < s.scalar.cells.size

theorem CoreMemDesign.fastCommitScalar_toState_scalar
    (E : CoreMemDesign) (s s' : CoreMemFastState) (q : NbaQueue2)
    (hflat : E.FlatScalarQueue s q)
    (h : E.fastCommitScalar s q = .ok s') :
    s'.toState.scalar = E.scalarEdge.commit s.toState.scalar q := by
  induction q generalizing s s' with
  | nil =>
      cases h
      rfl
  | cons u rest ih =>
      obtain ⟨x, hx, hpath, hbound⟩ := hflat u (by simp)
      cases x with
      | mk path decl =>
          cases path with
          | nil =>
              simp [CoreMemDesign.fastCommitScalar, hx, hbound] at h
              let cells := s.scalar.cells.setIfInBounds decl
                ((s.scalar.cells.getD decl (s.scalar.fallback { path := [], decl })).write
                  u.2.1 u.2.2)
              let s1 : CoreMemFastState :=
                { s with
                    scalar := { s.scalar with cells }
                    scalarCache := cells }
              have htail : E.fastCommitScalar s1 rest = .ok s' := by
                simpa [s1, cells, hbound] using h
              have hflat' : E.FlatScalarQueue s1 rest := by
                intro v hv
                obtain ⟨y, hy, hyp, hyb⟩ := hflat v (by simp [hv])
                exact ⟨y, hy, hyp, by simpa [s1, cells] using hyb⟩
              have ih' := ih s1 s' hflat' htail
              have hwrite := fastWriteWin_ok_of_flat E.scalarEdge.base
                s.scalar.fallback s.scalar.cells u.1 { path := [], decl } u.2.1 u.2.2
                hx hpath hbound
              rw [ih']
              have hwrite' := congrArg
                (fun z : Store =>
                  List.foldl
                    (fun s u => E.scalarEdge.base.writeWin s u.1 u.2.1 u.2.2)
                    z rest) hwrite
              simpa [s1, cells, CoreMemFastState.toState,
                FastConfig.store, Elab1.commit, List.foldl] using hwrite'
          | cons head tail => simp_all

theorem CoreMemDesign.fastCommitScalar_preserves_memory
    (E : CoreMemDesign) (s s' : CoreMemFastState) (q : NbaQueue2)
    (h : E.fastCommitScalar s q = .ok s') : s'.memory = s.memory := by
  induction q generalizing s s' with
  | nil => simp [CoreMemDesign.fastCommitScalar] at h ⊢; cases h; rfl
  | cons u rest ih =>
      cases hx : E.scalarEdge.base.resolve u.1 with
      | none => simp [CoreMemDesign.fastCommitScalar, hx] at h
      | some x =>
          cases hp : x.path with
          | nil =>
              by_cases hb : x.decl < s.scalar.cells.size
              · let cells := s.scalar.cells.setIfInBounds x.decl
                  ((s.scalar.cells.getD x.decl (s.scalar.fallback x)).write
                    u.2.1 u.2.2)
                let s1 : CoreMemFastState :=
                  { s with
                      scalar := { s.scalar with cells }
                      scalarCache := cells }
                have htail : E.fastCommitScalar s1 rest = .ok s' := by
                  simpa [CoreMemDesign.fastCommitScalar, hx, hp, hb,
                    s1, cells] using h
                exact ih s1 s' htail
              · simp [CoreMemDesign.fastCommitScalar, hx, hp, hb] at h
          | cons head tail => simp [CoreMemDesign.fastCommitScalar, hx, hp] at h

def CoreMemDesign.flatScalarQueueB (E : CoreMemDesign) (s : CoreMemFastState) :
    NbaQueue2 → Bool
  | [] => true
  | (name, _, _) :: rest =>
      match E.scalarEdge.base.resolve name with
      | some x => x.path == [] && x.decl < s.scalar.cells.size &&
          E.flatScalarQueueB s rest
      | none => false

theorem CoreMemDesign.flatScalarQueueB_of_success
    (E : CoreMemDesign) (s s' : CoreMemFastState) (q : NbaQueue2)
    (h : E.fastCommitScalar s q = .ok s') :
    E.FlatScalarQueue s q := by
  induction q generalizing s s' with
  | nil =>
      simp [CoreMemDesign.FlatScalarQueue]
  | cons u rest ih =>
      cases hx : E.scalarEdge.base.resolve u.1 with
      | none => simp [CoreMemDesign.fastCommitScalar, hx] at h
      | some x =>
          cases hp : x.path with
          | nil =>
              by_cases hb : x.decl < s.scalar.cells.size
              · simp [CoreMemDesign.fastCommitScalar, hx, hp, hb] at h
                let cells := s.scalar.cells.setIfInBounds x.decl
                  ((s.scalar.cells.getD x.decl (s.scalar.fallback x)).write
                    u.2.1 u.2.2)
                let s1 : CoreMemFastState :=
                  { s with
                      scalar := { s.scalar with cells }
                      scalarCache := cells }
                have htail : E.fastCommitScalar s1 rest = .ok s' := by
                  simpa [CoreMemDesign.fastCommitScalar, hx, hp, hb,
                    s1, cells] using h
                have htailFlat := ih s1 s' htail
                have hsize : s1.scalar.cells.size = s.scalar.cells.size := by
                  simp [s1, cells]
                refine fun v hv => ?_
                by_cases huv : v = u
                · subst v
                  exact ⟨x, hx, hp, hb⟩
                · obtain ⟨y, hy, hyp, hyb⟩ := htailFlat v
                    (by simp [huv] at hv; exact hv)
                  exact ⟨y, hy, hyp, by simpa [hsize] using hyb⟩
              · simp [CoreMemDesign.fastCommitScalar, hx, hp, hb] at h
          | cons head tail =>
              simp [CoreMemDesign.fastCommitScalar, hx, hp] at h

def CoreMemDesign.fastCommitScalarState (E : CoreMemDesign)
    (st : CoreMemState) (q : NbaQueue2) : Res CoreMemState :=
  let fs := CoreMemFastState.ofState E st
  match E.fastCommitScalar fs q with
  | .ok fs' => .ok (E.normalizeScalar fs'.toState fs'.toState.scalar)
  | .timeout => .ok (E.normalizeScalar st (E.scalarEdge.commit st.scalar q))
  | .unsupported _ => .ok (E.normalizeScalar st (E.scalarEdge.commit st.scalar q))

theorem CoreMemDesign.normalizeScalar_eq_of
    (E : CoreMemDesign) (a b : CoreMemState)
    (store : Store) (hscalar : a.scalar = store) (hmemory : a.memory = b.memory) :
    E.normalizeScalar a a.scalar = E.normalizeScalar b store := by
  cases a
  cases b
  cases hscalar
  cases hmemory
  rfl

theorem CoreMemDesign.fastCommitScalarState_eq
    (E : CoreMemDesign) (st : CoreMemState) (q : NbaQueue2) :
    E.fastCommitScalarState st q =
      .ok (E.normalizeScalar st (E.scalarEdge.commit st.scalar q)) := by
  unfold CoreMemDesign.fastCommitScalarState
  cases hf : E.fastCommitScalar (CoreMemFastState.ofState E st) q with
  | timeout => simp [hf]
  | unsupported msg => simp [hf]
  | ok fs' =>
      have hflat := E.flatScalarQueueB_of_success
        (CoreMemFastState.ofState E st) fs' q hf
      have hs := E.fastCommitScalar_toState_scalar
        (CoreMemFastState.ofState E st) fs' q hflat hf
      have hbase := CoreMemFastState.ofState_toState E st
      rw [hbase] at hs
      have hm := E.fastCommitScalar_preserves_memory
        (CoreMemFastState.ofState E st) fs' q hf
      have hnorm := E.normalizeScalar_eq_of fs'.toState st
        (E.scalarEdge.commit st.scalar q) hs hm
      simp [hf, hnorm]

theorem CoreMemDesign.fastCommitScalarState_refines
    (E : CoreMemDesign) (st st' : CoreMemState) (q : NbaQueue2)
    (h : E.fastCommitScalarState st q = .ok st') :
    st' = E.normalizeScalar st (E.scalarEdge.commit st.scalar q) := by
  rw [E.fastCommitScalarState_eq] at h
  cases h
  rfl

/-! A whole-cycle executor using the exact source-shaped front half and the
    array-backed scalar NBA commit.  The memory and process semantics remain
    the canonical definitions; only the scalar commit is replaced, and the
    theorem below closes that replacement back to `CoreMemDesign.step`. -/
def CoreMemDesign.fastStep (E : CoreMemDesign) (st : CoreMemState)
    (entry : SvState) : Res CoreMemState := do
  let inputStore := E.scalar.applyInputs st.scalar entry
  let memoryInput := E.applyMemoryInputs entry st.memory
  let inputState := E.normalizeScalar { st with memory := memoryInput } inputStore
  let pre0 ← E.settleAssign E.env E.elems inputState E.processes.toList
  let pre ← if E.hasComb then
      E.runComb st pre0 E.processes.toList
    else .ok pre0
  let pre ← if E.hasImplicit then
      E.runImplicit st pre E.processes.toList
    else .ok pre
  let pre ← E.settleAssign E.env E.elems pre E.processes.toList
  let combBefore := pre
  let before := E.scalar.view st.scalar
  let after := E.scalar.view pre.scalar
  let edge ← E.runEdges E.env E.elems pre before after E.processes.toList
  let committed ← E.fastCommitScalarState edge.state edge.scalarQ
  let memory ← match edge.state.memory.commitNba edge.memoryQ with
    | some m => .ok m
    | none => .unsupported "10.4.2: memory NBA commit lost its declaration identity"
  let committed := { committed with memory }
  let settled ← E.settleAssign E.env E.elems committed E.processes.toList
  let activated ← if E.hasImplicit then
      E.runImplicit pre settled E.processes.toList
    else .ok settled
  let combed ← if E.hasComb then
      E.runComb combBefore activated E.processes.toList
    else .ok activated
  E.settleAssign E.env E.elems combed E.processes.toList

/-! A row driver for the whole-cycle fast route.  The empty-input shortcut is
    the same exact optimization as `runCoreMemRows`; all other rows use the
    source-shaped `fastStep` above. -/
def runCoreMemFastRows (E : CoreMemDesign) (st : CoreMemState) : List SvState →
    Res (List CoreMemState)
  | [] => .ok []
  | row :: rest => do
      let st' ← E.fastStep st row
      let tail ← if row.isEmpty && E.scalarAssignInputsOnly then
          runCoreMemRepeat st' rest
        else runCoreMemFastRows E st' rest
      .ok (st' :: tail)

end LeanModels.Sv.Kernel
