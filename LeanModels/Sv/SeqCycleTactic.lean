import LeanModels.Sv.SeqCycle
import LeanModels.Sv.CombViewTactic

/-!
# The clocked stages at symbolic parameters (`LeanModels.Sv.Kernel`, plumbing for `SeqCycle`)

The theory (`SeqCycle.lean`) relates the ordinary E route's slot function to a cycle on views. What remains per
design is computation at the design's symbolic parameters, and these macros do it, kernel-checked by `simp` and
`omega` (no `decide` on the loaded design: its instantiation is well-founded recursion, measured):

* `sv_seq_inst [X.e, X.pdesign] at hE` turns `hE : X.e P… = .ok E` into `hE : <normal form> = E`: the route's
  instantiation (`PDesign.instantiateCoreMemFrom`) evaluated at the symbolic parameters through its definitions'
  equation lemmas; the side conditions on the parameters (the 32-bit range of an `int` parameter, a declared width
  `[P-1:0]`) are closed by `omega` from the hypotheses in context.
* `sv_seq_profile` closes `E.SeqProfile clk` on the normal form (`hE` substituted).
* `sv_seq_cycle h : E.cycleV clk v d using hE` adds `h : E.cycleV clk v d = <the computed result>`: THE CYCLE
  EQUATIONS, the pre and post sample of one cycle evaluated from the route's own definitions on a symbolic view; a
  condition on the parameters is decided by `omega` from the context.

Each macro takes extra simp lemmas in brackets for facts of the design the default sets do not know. Nothing here is
trusted: every step is a `simp` or `omega` proof the kernel checks.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Lemmas the normalizations use -/

theorem seqE_except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem seqE_except_mapError_ok {ε ε' α : Type} (g : ε → ε') (a : α) :
    (Except.ok a : Except ε α).mapError g = .ok a := rfl

theorem seqE_except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

/-- The declared width of `[P-1:0]` at a parameter `P ≥ 1`. -/
theorem seqE_natAbs_sub_one_add_one (N : Nat) (h : 1 ≤ N) : ((N : Int) - 1).natAbs + 1 = N := by omega

theorem seqE_natAbs_sub_one (N : Nat) (h : 1 ≤ N) : ((N : Int) - 1).natAbs = N - 1 := by omega

/-- No positive edge into a 0. -/
theorem seqE_isPosedge_l0 (b : Logic) : isPosedge b .l0 = false := by cases b <;> rfl

theorem seqE_bit0_zero : (LVec.ofBitVec 0#1).bits[0]? = some Logic.l0 := by decide
theorem seqE_bit0_one : (LVec.ofBitVec 1#1).bits[0]? = some Logic.l1 := by decide

theorem seqE_resizeU_resizeU (v : LVec) (w : Nat) : (v.resizeU w).resizeU w = v.resizeU w :=
  LVec.resizeU_of_width (LVec.width_resizeU v w)

theorem seqE_resizeU_l0 : (⟨#[.l0]⟩ : LVec).resizeU 1 = ⟨#[.l0]⟩ := by decide

theorem seqE_width_bit (b : Logic) : (⟨#[b]⟩ : LVec).width = 1 := rfl

/-- Vector `+` has the wider operand's width. -/
theorem seqE_width_add (a b : LVec) : (a.add b).width = max a.width b.width := by
  unfold LVec.add
  split
  · exact LVec.width_ofNat _ _
  · simp [LVec.arithWidth]

/-- A whole-signal write at offset 0 of a value of the signal's width is that value. -/
theorem seqE_insertAt_zero {v p : LVec} (h : p.width = v.width) : v.insertAt 0 p = p :=
  LVec.insertAt_zero_of_width_eq h
theorem seqE_resizeU_l1 : (⟨#[.l1]⟩ : LVec).resizeU 1 = ⟨#[.l1]⟩ := by decide

end LeanModels.Sv.Kernel

open LeanModels.Sv LeanModels.Sv.Kernel in
/-- The instantiation pass: the route's `do` block evaluated through its definitions' equation lemmas. -/
macro "sv_seq_inst_pass" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" " at " h:ident : tactic =>
  `(tactic| simp (config := {maxSteps := 4000000, decide := true}) [LeanModels.Sv.bindParamsRes,
      LeanModels.Sv.bindPackageParams, LeanModels.Sv.bindPackageEnums, LeanModels.Sv.bindLocals,
      LeanModels.Sv.bindEnums, LeanModels.Sv.typedParamWidthsE, LeanModels.Sv.Kernel.coreMemGeneratedDeclsList,
      LeanModels.Sv.Kernel.coreMemExpandList, LeanModels.Sv.bindParams, LeanModels.Sv.declConstType,
      LeanModels.Sv.PType.width_packed_cons, LeanModels.Sv.PType.width_packed_nil, LeanModels.Sv.PDim.width,
      LeanModels.Sv.IEnv.bindNVal, LeanModels.Sv.IEnv.withPDims, LeanModels.Sv.Kernel.coreMemDeclNamesUnique,
      LeanModels.Sv.Kernel.coreMemMetadataDecls, LeanModels.Sv.Kernel.coreMemFirstUnsupportedOther,
      LeanModels.Sv.Kernel.buildScalarDecls1, LeanModels.Sv.Kernel.instScalarDecl1, LeanModels.Sv.buildElems,
      LeanModels.Sv.Kernel.buildMemDecls1, LeanModels.Sv.PDecl.memShapeWithId?,
      LeanModels.Sv.Kernel.coreMemNetDecls, LeanModels.Sv.Kernel.CoreMemProc.ofPProcessAt,
      LeanModels.Sv.Kernel.CoreMemProc.ofPProcess, LeanModels.Sv.dimTable, LeanModels.Sv.dimTableStep,
      LeanModels.Sv.evalDims, LeanModels.Sv.evalInt, LeanModels.Sv.Kernel.seqE_except_ok_bind,
      LeanModels.Sv.Kernel.seqE_except_mapError_ok, LeanModels.Sv.Kernel.seqE_except_pure, List.lookup,
      LeanModels.Sv.Kernel.CoreMemDesign.compileAssigns, LeanModels.Sv.Kernel.CoreMemDesign.compileCombReads,
      LeanModels.Sv.Kernel.CoreMemDesign.compileImplicitReads, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
      LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf,
      $ls,*] at $h:ident)

/-- The arithmetic pass: side conditions on the parameters, by `omega` from the context. -/
macro "sv_seq_arith_pass" " at " h:ident : tactic =>
  `(tactic| simp (disch := omega) only [LeanModels.Sv.CombView.canonInt32_of_bounds,
      LeanModels.Sv.Kernel.seqE_natAbs_sub_one_add_one, LeanModels.Sv.Kernel.seqE_natAbs_sub_one,
      Nat.sub_add_cancel] at $h:ident)

/-- **`sv_seq_inst [X.e, X.pdesign] at hE`**: `hE : X.e P… = .ok E` becomes `hE : <normal form> = E`. -/
macro "sv_seq_inst" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" " at " h:ident : tactic =>
  `(tactic| (
    simp only [LeanModels.Sv.Kernel.PDesign.instantiateE2, LeanModels.Sv.Kernel.PDesign.instantiateCoreMem,
      LeanModels.Sv.Kernel.PDesign.instantiateCoreMemFrom, $ls,*] at $h:ident
    sv_seq_inst_pass [$ls,*] at $h:ident
    (try sv_seq_arith_pass at $h:ident)))

/-- **`sv_seq_profile`**: the clocked profile of a normal form, decided by `simp`. -/
macro "sv_seq_profile" : tactic =>
  `(tactic| (
    refine ⟨rfl, rfl, by simp, by simp [LeanModels.Sv.Kernel.AllFour], ?_⟩
    intro i p hp
    rcases i with _ | _ | _ | _ | _ | _ | i <;> simp at hp <;> subst hp <;>
      simp [LeanModels.Sv.Kernel.CoreMemDesign.ProcOk, LeanModels.Sv.PStmt.nbaWholeB,
        LeanModels.Sv.PStmt.optNbaWholeB, LeanModels.Sv.PStmt.listNbaWholeB, LeanModels.Sv.PStmt.need,
        LeanModels.Sv.PStmt.optNeed, LeanModels.Sv.PStmt.listNeed,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead, LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCallList, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
        LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf]))

/-- The evaluation pass of a cycle: the view functions and the route's evaluator unfolded. -/
macro "sv_seq_eval_pass" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : conv =>
  `(conv| simp (config := {maxSteps := 4000000, decide := true}) [-LeanModels.Sv.Res.bind_eq_ok,
      LeanModels.Sv.Kernel.CoreMemDesign.cycleV, LeanModels.Sv.Kernel.CoreMemDesign.slotV,
      LeanModels.Sv.Kernel.CoreMemDesign.settleV, LeanModels.Sv.Kernel.CoreMemDesign.settleRaw,
      LeanModels.Sv.Kernel.CoreMemDesign.matV, LeanModels.Sv.Kernel.CoreMemDesign.edgeQIf,
      LeanModels.Sv.Kernel.CoreMemDesign.edgeQV, LeanModels.Sv.Kernel.CoreMemDesign.nbaQ,
      LeanModels.Sv.Kernel.CoreMemDesign.nbaQList, LeanModels.Sv.Kernel.CoreMemDesign.nbaQOpt,
      LeanModels.Sv.Kernel.CoreMemDesign.evalV, LeanModels.Sv.Kernel.CoreMemDesign.evalListV,
      LeanModels.Sv.Kernel.CoreMemDesign.evalIdxV, LeanModels.Sv.Kernel.CoreMemDesign.evalScalarV,
      LeanModels.Sv.Kernel.CoreMemDesign.widthsOf, LeanModels.Sv.Kernel.CoreMemDesign.scalarTarget,
      LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?, LeanModels.Sv.Kernel.Elab.resolve,
      LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf, LeanModels.Sv.applyInputs2,
      LeanModels.Sv.Kernel.Elab.toDesign2, LeanModels.Sv.Kernel.lowEntry, LeanModels.Sv.Kernel.highEntry,
      LeanModels.Sv.commitNba2, LeanModels.Sv.Kernel.Val.ofLVec, LeanModels.Sv.Kernel.VType.ofDecl,
      LeanModels.Sv.Kernel.VType.conv, LeanModels.Sv.Kernel.declFallback, LeanModels.Sv.Res.ok_bind,
      LeanModels.Sv.Kernel.seqE_except_ok_bind, LeanModels.Sv.SvState.lookup, LeanModels.Sv.SvState.set,
      LeanModels.Sv.readSignal, LeanModels.Sv.SvState.bit0, LeanModels.Sv.evalPure2_ident,
      LeanModels.Sv.evalPure2_slice, LeanModels.Sv.instExpr2, LeanModels.Sv.dynPartPlan, LeanModels.Sv.evalInt,
      LeanModels.Sv.arrayPartRead, LeanModels.Sv.arrayPartGeom, LeanModels.Sv.arrayDims,
      LeanModels.Sv.walkIndices, LeanModels.Sv.partLabels, LeanModels.Sv.labelOffset, LeanModels.Sv.dimsStride,
      LeanModels.Sv.dimCount, List.lookup, LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList, LeanModels.Sv.Kernel.seqE_isPosedge_l0,
      LeanModels.Sv.Kernel.seqE_bit0_zero, LeanModels.Sv.Kernel.seqE_bit0_one,
      LeanModels.Sv.Kernel.seqE_resizeU_resizeU, LeanModels.Sv.Kernel.seqE_resizeU_l0,
      LeanModels.Sv.Kernel.seqE_resizeU_l1, LeanModels.Sv.LVec.resizeU_of_width,
      LeanModels.Sv.Kernel.seqE_width_bit, LeanModels.Sv.ctxOpWidth2, LeanModels.Sv.rigidMax2,
      LeanModels.Sv.selfWidth2, LeanModels.Sv.fitExpr2, LeanModels.Sv.rigidExpr,
      LeanModels.Sv.PExpr.ctxPropagates, LeanModels.Sv.PExpr.constLeaf, LeanModels.Sv.PExpr.negGenvarWidened,
      LeanModels.Sv.PExpr.signedCast, $ls,*])

/-- The arithmetic pass of a cycle: conditions and bounds on the parameters, by `omega`. -/
macro "sv_seq_eval_arith" : conv =>
  `(conv| simp (disch := omega) only [if_pos, if_neg, Nat.max_eq_left, Nat.max_eq_right, Int.min_eq_left,
      Int.min_eq_right, Int.max_eq_left,
      Int.max_eq_right, LeanModels.Sv.CombView.canonInt32_of_bounds,
      LeanModels.Sv.Kernel.seqE_natAbs_sub_one_add_one, LeanModels.Sv.Kernel.seqE_natAbs_sub_one,
      Nat.sub_add_cancel])

/-- **`sv_seq_cycle h : E.cycleV clk v d using hE [facts]`**: `h : E.cycleV clk v d = <the computed pre and post
views>`, where `hE : <normal form> = E` comes from `sv_seq_inst`. -/
macro "sv_seq_cycle " h:ident " : " t:term " using " hE:ident " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    have $h := (rfl : $t = $t)
    conv at $h:ident =>
      rhs
      rw [← $hE:ident]
      try sv_seq_eval_pass [$ls,*]
      try sv_seq_eval_arith
      try sv_seq_eval_pass [$ls,*]
      try sv_seq_eval_arith
      try sv_seq_eval_pass [$ls,*]
      try sv_seq_eval_arith
      try sv_seq_eval_pass [$ls,*]))
