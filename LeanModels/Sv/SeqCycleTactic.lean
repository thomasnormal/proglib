import LeanModels.Sv.SeqCycleInstant
import LeanModels.Sv.SeqCycleObl
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
* `sv_seq_cycle h : E.cycleV clk v d using hE` (or `E.cycleMV clk (v, mv) d`) adds `h : … = <the computed result>`:
  THE CYCLE EQUATIONS, the pre and post sample of one cycle evaluated from the route's own definitions on a symbolic
  view (and memory view); a condition on the parameters is decided by `omega` from the context. A decision stays an
  `if` on values (an `if`, a `case` arm, an edge that may fire, a run-time index: `seqIndexRead`/`seqIndexWin`); a
  memory's next contents come out as one write equation (`memWrite`) and its reads as one read equation (`memRd`).

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

/-- Bit 0 as the cycle stage leaves it for a vector of known nonzero width (`v.bits[0]`), as the edge table reads it. -/
theorem seqE_getElem_zero (v : LVec) (h : 0 < v.bits.size) : v.bits[0]'h = v.bits[0]?.getD .lx := by
  simp [Array.getElem?_eq_getElem h]

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

/-! ## Per-signal equations: a decision stays an `if` on the values it decides

The evaluation pass does not split the cycle at the design's decisions (an `if`, a `case` arm, an edge that may or may
not fire). It pushes each decision inward through `Res.ok`, pairs, lists and the commit, so the computed post view is
ONE list whose entries carry the decisions as `if`s on the values: the next value of each signal as its own equation
(`("q", if r.condTrue = true then … else …)`). A branch that refuses keeps the `if` at the `Res` level (no `.ok` to
merge with), so a refusal is never hidden. -/

theorem seqE_ite_ok {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then Res.ok a else Res.ok b) = Res.ok (if p then a else b) := by split <;> rfl

theorem seqE_ite_pair {α β : Type} (p : Prop) [Decidable p] (a c : α) (b d : β) :
    (if p then (a, b) else (c, d)) = (if p then a else c, if p then b else d) := by split <;> rfl

theorem seqE_ite_cons {α : Type} (p : Prop) [Decidable p] (x y : α) (xs ys : List α) :
    (if p then x :: xs else y :: ys) = (if p then x else y) :: (if p then xs else ys) := by split <;> rfl

theorem seqE_commit_ite (p : Prop) [Decidable p] (v : SvState) (q₁ q₂ : NbaQueue2) :
    commitNba2 v (if p then q₁ else q₂) = if p then commitNba2 v q₁ else commitNba2 v q₂ := by split <;> rfl

theorem seqE_resizeU_ite (p : Prop) [Decidable p] (a b : LVec) (w : Nat) :
    (if p then a else b).resizeU w = if p then a.resizeU w else b.resizeU w := by split <;> rfl

theorem seqE_width_ite (p : Prop) [Decidable p] (a b : LVec) :
    (if p then a else b).width = if p then a.width else b.width := by split <;> rfl

/-- The width of a literal vector. -/
theorem seqE_width_lit (bs : Array Logic) : (⟨bs⟩ : LVec).width = bs.size := rfl

/-- The commit of an empty queue changes nothing. -/
theorem seqE_commit_nil (v : SvState) : commitNba2 v [] = v := rfl

/-- The commit of a queue, one update at a time (so a queue that is an `if` is split by `seqE_commit_ite` before its
updates are applied, never unfolded into a `foldl` over an `if`). -/
theorem seqE_commit_cons (v : SvState) (u : String × Nat × LVec) (us : NbaQueue2) :
    commitNba2 v (u :: us) = commitNba2 (match SvState.lookup v u.1 with
      | some old => SvState.set v u.1 (old.insertAt u.2.1 u.2.2)
      | none => v) us := rfl

theorem seqE_append_ite {α : Type} (p : Prop) [Decidable p] (xs ys zs : List α) :
    xs ++ (if p then ys else zs) = if p then xs ++ ys else xs ++ zs := by split <;> rfl

theorem seqE_ite_append {α : Type} (p : Prop) [Decidable p] (xs ys zs : List α) :
    (if p then ys else zs) ++ xs = if p then ys ++ xs else zs ++ xs := by split <;> rfl

theorem seqE_ite_fst {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl

theorem seqE_ite_snd {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl

/-! ## Run-time selects: the index decision kept as a value

A run-time element read (`Expr2.index`) and a select target's window (`resolveLhs2` on `.index`) decide on the index
value (x/z or out of range: all x, or no write window, §11.5.1). The evaluation pass keeps that decision as a value
(`seqIndexRead`, `seqIndexWin`) instead of a `match` at the `Res` level, and evaluates the window resolver's fuel
evaluator by its fuel-free twin (`evalExpr2_eq_evalPure2`). -/

/-- `evalPure2`'s run-time element read, its decision a value. -/
def seqIndexRead (bv : LVec) (i? : Option Int) (w : Nat) : LVec :=
  match i? with
  | some i => if 0 ≤ i && (i + 1) * w ≤ bv.width then bv.extract (i.toNat * w) w else LVec.xVec w
  | none => LVec.xVec w

theorem seqE_evalPure2_index (st : SvState) (base idx : Expr2) (w : Nat) :
    evalPure2 st (.index base idx w) = (do
      let bv ← evalPure2 st base
      let iv ← evalPure2 st idx
      .ok (seqIndexRead bv (indexInt? idx iv) w)) := by
  rw [evalPure2_index]
  cases evalPure2 st base with
  | ok bv =>
      cases evalPure2 st idx with
      | ok iv =>
          simp only [Res.ok_bind, seqIndexRead]
          cases indexInt? idx iv with
          | none => rfl
          | some i =>
              by_cases hc : (decide (0 ≤ i) && decide ((i + 1) * (w : Int) ≤ (bv.width : Int))) = true <;>
                simp [hc]
      | timeout => rfl
      | unsupported m => rfl
  | timeout => rfl
  | unsupported m => rfl

/-- `resolveLhs2`'s window of a run-time select target, its decision a value (`none`: no write). -/
def seqIndexWin (old : LVec) (i? : Option Int) (w : Nat) : Option (Nat × Nat) :=
  match i? with
  | some i => if 0 ≤ i && (i + 1) * w ≤ old.width then some (i.toNat * w, w) else none
  | none => none

theorem seqE_resolveLhs2_index (fuel : Nat) (st : SvState) (n : String) (idx : Expr2) (w : Nat) :
    resolveLhs2 fuel st (.index n idx w) = (do
      let iv ← evalExpr2 fuel st idx
      match SvState.lookup st n with
      | none => .unsupported s!"unknown assignment target '{n}'"
      | some old => .ok (n, seqIndexWin old (indexInt? idx iv) w)) := by
  simp only [resolveLhs2]
  cases evalExpr2 fuel st idx with
  | ok iv =>
      simp only [Res.ok_bind]
      cases SvState.lookup st n with
      | none => rfl
      | some old =>
          simp only [seqIndexWin]
          cases indexInt? idx iv with
          | none => rfl
          | some i =>
              by_cases hc : (decide (0 ≤ i) && decide ((i + 1) * (w : Int) ≤ (old.width : Int))) = true <;>
                simp [hc]
  | timeout => rfl
  | unsupported m => rfl

/-! ## Memories: the write equation and the read equation through the evaluation pass

A memory's next contents come out of the evaluation pass as ONE write equation (`memWrite`) under the decisions that
issue it (pushed through `commitMemV`), its reads as ONE read equation (`memRd`) of the memory view the slot holds. -/

theorem seqE_commitMemV_ite (p : Prop) [Decidable p] (mv : MemV) (q₁ q₂ : MemQV) :
    commitMemV mv (if p then q₁ else q₂) = if p then commitMemV mv q₁ else commitMemV mv q₂ := by split <;> rfl

/-- The commit of one issued element write is the write equation. -/
theorem seqE_commitMemV_memIss (mv : MemV) (n : String) (k? : Option Int) (x : LVec) :
    commitMemV mv (memIss n k? x) = memWrite mv n k? x := by
  simpa using commitMemV_memIss mv n k? x []

theorem seqE_memRd_ite (p : Prop) [Decidable p] (a b : MemV) (n : String) (k? : Option Int) (w : Nat) :
    memRd (if p then a else b) n k? w = if p then memRd a n k? w else memRd b n k? w := by split <;> rfl

theorem seqE_memIss_ite (p : Prop) [Decidable p] (n : String) (k? : Option Int) (x y : LVec) :
    memIss n k? (if p then x else y) = if p then memIss n k? x else memIss n k? y := by split <;> rfl

/-- A read of an element: of the element width, when every element of the memory view has it. -/
theorem seqE_memRd_width {mv : MemV} {n : String} {w : Nat} (h : ∀ k, (mv n k).width = w) (k? : Option Int) :
    (memRd mv n k? w).width = w := by
  cases k? with
  | none => simp [memRd, LVec.xVec, LVec.replicate, LVec.width]
  | some k => exact h k

/-! ## The knownness bridge: the route's own decision forms on known values

Known2's simp set turns the evaluator's operators on known values (`LVec.ofBitVec`) into `BitVec` terms. The cycle
equations carry, beside them, the route's decision forms: `condTrue` of a logical not, an edge-table test on bit 0, a
case equality. On known values each is a `Bool` of the `BitVec`s, so a per-signal equation on known state and inputs
becomes a `BitVec` equation (`ite_ofBitVec` folds the `if`s). -/

/-- `!x` reads true exactly when `x` is zero. -/
theorem seqK_lnot_condTrue {w : Nat} (x : BitVec w) :
    (evalUnaryOp .lnot (LVec.ofBitVec x)).condTrue = decide (x = 0#w) := by
  by_cases hx : x = 0#w <;> simp [evalUnaryOp, LVec.lnot, hx]

/-- Bit 0 of a known vector. -/
theorem seqK_bit0 {w : Nat} (x : BitVec w) (hw : 0 < w) :
    (LVec.ofBitVec x).bits[0]?.getD Logic.lx = Logic.ofBool (x.getLsbD 0) := by
  simp [LVec.getElem?_ofBitVec, hw]

/-- The edge table (§9.4.2) on known bits: a fall is 1 → 0. -/
theorem seqK_isNegedge (a b : Bool) : isNegedge (Logic.ofBool a) (Logic.ofBool b) = (a && !b) := by
  cases a <;> cases b <;> rfl

/-- The edge table on known bits: a rise is 0 → 1. -/
theorem seqK_isPosedge (a b : Bool) : isPosedge (Logic.ofBool a) (Logic.ofBool b) = (!a && b) := by
  cases a <;> cases b <;> rfl

/-- Case equality of known vectors is `BitVec` equality. -/
theorem seqK_beq {w : Nat} (x y : BitVec w) : (LVec.ofBitVec x == LVec.ofBitVec y) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, LVec.ofBitVec_inj]

/-- A known unsigned index resolves to its value when it is in the declared range, and to the no-op otherwise. -/
theorem seqK_index? {w : Nat} (m : MemShape) (a : BitVec w) :
    m.index? false (LVec.ofBitVec a) = if m.inRange (a.toNat : Int) then some (a.toNat : Int) else none := by
  simp [MemShape.index?, LVec.toNat?_ofBitVec]

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
      LeanModels.Sv.Kernel.buildMemDecls1, LeanModels.Sv.PDecl.memShapeWithId?, LeanModels.Sv.evalMemDim,
      LeanModels.Sv.Kernel.buildAggDecls1, LeanModels.Sv.Kernel.PDecl.aggregateType?,
      LeanModels.Sv.Kernel.coreMemNetDecls, LeanModels.Sv.Kernel.CoreMemProc.ofPProcessAt,
      LeanModels.Sv.Kernel.CoreMemProc.ofPProcess, LeanModels.Sv.dimTable, LeanModels.Sv.dimTableStep,
      LeanModels.Sv.evalDims, LeanModels.Sv.evalInt, LeanModels.Sv.Kernel.seqE_except_ok_bind,
      LeanModels.Sv.Kernel.seqE_except_mapError_ok, LeanModels.Sv.Kernel.seqE_except_pure, List.lookup,
      LeanModels.Sv.Kernel.CoreMemDesign.compileAssigns, LeanModels.Sv.Kernel.CoreMemDesign.compileCombReads,
      LeanModels.Sv.Kernel.CoreMemDesign.compileImplicitReads, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
      LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf,
      LeanModels.Sv.Kernel.coreMemClockResetViol_none, LeanModels.Sv.Kernel.coreMemDropGeneratedNetMarkers,
      LeanModels.Sv.Kernel.coreMemGeneratedNetAllowed, LeanModels.Sv.Kernel.coreMemNetMetadataAllowed,
      LeanModels.Sv.Kernel.coreMemNetDriverAllowed,
      LeanModels.Sv.Kernel.coreMemEventSourceMultiWriteViol, LeanModels.Sv.Kernel.coreMemFirstRepeatedEventSource,
      LeanModels.Sv.Kernel.coreMemEventSources, LeanModels.Sv.Kernel.coreMemSourceWrittenTwiceInBody,
      LeanModels.Sv.Kernel.coreMemWritesNameTwice, LeanModels.Sv.Kernel.coreMemProcWrites,
      LeanModels.Sv.Kernel.coreMemStmtWrites, LeanModels.Sv.Kernel.coreMemStmtWritesList,
      LeanModels.Sv.Kernel.coreMemCaseWrites, LeanModels.Sv.Kernel.coreMemSourceHasBlockingWrite,
      LeanModels.Sv.Kernel.coreMemProcBlockingWrites, LeanModels.Sv.Kernel.coreMemStmtBlockingWrites,
      LeanModels.Sv.Kernel.coreMemStmtBlockingWritesList, LeanModels.Sv.Kernel.coreMemCaseBlockingWrites,
      LeanModels.Sv.Kernel.coreMemTimeZeroEventSourceViol, LeanModels.Sv.Kernel.coreMemFirstTimeZeroEventSource,
      LeanModels.Sv.Kernel.coreMemSourceWrittenAtTimeZero, LeanModels.Sv.Kernel.coreMemTimeZeroProcWrites,
      LeanModels.Sv.Kernel.coreMemPAssignMemoryTopoB, LeanModels.Sv.Kernel.coreMemHasEdgeProc,
      LeanModels.Sv.Kernel.coreMemPAssignTarget,
      LeanModels.Sv.Kernel.coreMemPAssignValue, LeanModels.Sv.Kernel.coreMemPAssignUsesMemory,
      LeanModels.Sv.Kernel.coreMemPAssignTargets, LeanModels.Sv.Kernel.coreMemPExprHasMemory,
      LeanModels.Sv.Kernel.coreMemPExprHasMemoryList, LeanModels.Sv.Kernel.coreMemPLhsHasMemory,
      LeanModels.Sv.Kernel.coreMemPLhsHasMemoryList, LeanModels.Sv.Kernel.coreMemCombDependencyViol,
      LeanModels.Sv.Kernel.coreMemReactiveDependencyViol, LeanModels.Sv.Kernel.coreMemAssignReactiveChainViol,
      LeanModels.Sv.Kernel.coreMemAssignReactiveChainViolAt, LeanModels.Sv.Kernel.coreMemReactiveProc,
      LeanModels.Sv.Kernel.coreMemReactiveWrites, LeanModels.Sv.Kernel.coreMemReactiveReads,
      LeanModels.Sv.Kernel.coreMemReactiveLaterWrites, LeanModels.Sv.Kernel.coreMemFirstReadIn,
      LeanModels.Sv.Kernel.coreMemStmtReadNames, LeanModels.Sv.Kernel.coreMemStmtReadNamesList,
      LeanModels.Sv.Kernel.coreMemCaseReadNames, LeanModels.Sv.Kernel.coreMemLhsReadNames,
      LeanModels.Sv.Kernel.coreMemLhsReadNamesList, LeanModels.Sv.Kernel.coreMemSignalNames,
      LeanModels.Sv.Kernel.coreMemSignalNamesList,
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

/-- **`sv_seq_profile`**: the clocked profile of a normal form, decided by `simp` (any number of processes). -/
macro "sv_seq_profile" : tactic =>
  `(tactic| exact LeanModels.Sv.Kernel.CoreMemDesign.SeqProfile.of_B
      (by simp (config := {decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.memOkB]) rfl (by simp)
      (by simp [LeanModels.Sv.Kernel.AllFour])
      (by simp [LeanModels.Sv.Kernel.coreMemResolvedNetNames])
      (by simp (config := {decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.procsOkFrom,
        LeanModels.Sv.Kernel.CoreMemDesign.procOkB, LeanModels.Sv.PStmt.edgeOkB, LeanModels.Sv.PStmt.optEdgeOkB,
        LeanModels.Sv.PLhs.hasCall, LeanModels.Sv.PLhs.hasCallList,
        LeanModels.Sv.PStmt.listEdgeOkB, LeanModels.Sv.PStmt.itemsEdgeOkB, LeanModels.Sv.PStmt.need,
        LeanModels.Sv.PStmt.optNeed, LeanModels.Sv.PStmt.listNeed, LeanModels.Sv.PStmt.itemsNeed,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead, LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCallList, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
        LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf]))

/-- **`sv_seq_profileI`**: the instant profile (any clocks, either edge) of a normal form, decided by `simp`. -/
macro "sv_seq_profileI" : tactic =>
  `(tactic| exact LeanModels.Sv.Kernel.CoreMemDesign.SeqProfileI.of_B
      (by simp (config := {decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.memOkB]) rfl (by simp)
      (by simp [LeanModels.Sv.Kernel.AllFour]) (by simp)
      (by simp (config := {decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.procsOkIFrom,
        LeanModels.Sv.Kernel.CoreMemDesign.procOkIB, LeanModels.Sv.PStmt.edgeOkB, LeanModels.Sv.PStmt.optEdgeOkB,
        LeanModels.Sv.PLhs.hasCall, LeanModels.Sv.PLhs.hasCallList,
        LeanModels.Sv.PStmt.listEdgeOkB, LeanModels.Sv.PStmt.itemsEdgeOkB, LeanModels.Sv.PStmt.need,
        LeanModels.Sv.PStmt.optNeed, LeanModels.Sv.PStmt.listNeed, LeanModels.Sv.PStmt.itemsNeed,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead, LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall,
        LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCallList, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
        LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf]))

/-- **`sv_seq_obligations`**: the obligations of the clocked profile (`seqOblB`) on a normal form, decided by `simp`
(the topological order on the compiled expressions: `instExpr2` evaluated, `Expr2.idents` read). -/
macro "sv_seq_obligations" : tactic =>
  `(tactic| simp (config := {maxSteps := 4000000, decide := true}) [LeanModels.Sv.Kernel.CoreMemDesign.seqOblB,
      LeanModels.Sv.Kernel.CoreMemDesign.seqOblI, LeanModels.Sv.Kernel.CoreMemDesign.oblInputsUndriven,
      LeanModels.Sv.Kernel.CoreMemDesign.oblSources, LeanModels.Sv.Kernel.CoreMemDesign.oblNoSourceRead,
      LeanModels.Sv.Kernel.CoreMemProc.sourceReadOk, LeanModels.Sv.Kernel.CoreMemDesign.sources,
      LeanModels.Sv.Kernel.CoreMemDesign.events, LeanModels.Sv.Kernel.CoreMemProc.events,
      LeanModels.Sv.Kernel.CoreMemEdge.events, LeanModels.Sv.Kernel.CoreMemEdge.clockEvent,
      LeanModels.Sv.Kernel.CoreMemEdge.resetEvent?, LeanModels.Sv.Kernel.CoreMemDesign.inputPorts,
      LeanModels.Sv.Kernel.CoreMemDesign.driven, LeanModels.Sv.Kernel.CoreMemDesign.inputNamesL,
      LeanModels.Sv.Kernel.CoreMemDesign.oblDrivers, LeanModels.Sv.Kernel.CoreMemDesign.oblNoInputWrite,
      LeanModels.Sv.Kernel.CoreMemDesign.oblNoClockRead, LeanModels.Sv.Kernel.CoreMemDesign.oblReset,
      LeanModels.Sv.Kernel.CoreMemDesign.oblEdgeOrder, LeanModels.Sv.Kernel.CoreMemDesign.oblConverted,
      LeanModels.Sv.Kernel.CoreMemDesign.oblClockInput,
      LeanModels.Sv.Kernel.CoreMemProc.targets, LeanModels.Sv.Kernel.CoreMemProc.reads,
      LeanModels.Sv.Kernel.CoreMemProc.reset?, LeanModels.Sv.Kernel.CoreMemProc.blocking,
      LeanModels.Sv.Kernel.CoreMemProc.isEdge, LeanModels.Sv.Kernel.CoreMemProc.nbaWholeP,
      LeanModels.Sv.PStmt.nbaWhole, LeanModels.Sv.PStmt.optNbaWhole, LeanModels.Sv.PStmt.listNbaWhole,
      LeanModels.Sv.PStmt.itemsNbaWhole, LeanModels.Sv.Kernel.CoreMemDesign.topoC,
      LeanModels.Sv.Kernel.CoreMemDesign.topoFrom, LeanModels.Sv.Kernel.assignTargets,
      LeanModels.Sv.Kernel.CoreMemDesign.compileAssigns, LeanModels.Sv.Expr2.idents, LeanModels.Sv.Expr2.listIdents,
      LeanModels.Sv.PExpr.sigNames, LeanModels.Sv.PExpr.sigNamesList, LeanModels.Sv.PLhs.baseNames,
      LeanModels.Sv.PLhs.baseNamesList, LeanModels.Sv.PLhs.indexNames, LeanModels.Sv.PLhs.indexNamesList,
      LeanModels.Sv.PStmt.writes, LeanModels.Sv.PStmt.optWrites, LeanModels.Sv.PStmt.listWrites,
      LeanModels.Sv.PStmt.itemsWrites, LeanModels.Sv.PStmt.hasBlocking, LeanModels.Sv.PStmt.optHasBlocking,
      LeanModels.Sv.PStmt.listHasBlocking, LeanModels.Sv.PStmt.itemsHasBlocking,
      LeanModels.Sv.PStmt.readNames, LeanModels.Sv.PStmt.optReadNames, LeanModels.Sv.PStmt.listReadNames,
      LeanModels.Sv.PStmt.itemsReadNames,
      LeanModels.Sv.Kernel.CoreMemProc.unconverted, LeanModels.Sv.PExpr.unconverted, LeanModels.Sv.PExpr.unconvertedList,
      LeanModels.Sv.PStmt.unconverted, LeanModels.Sv.PStmt.optUnconverted, LeanModels.Sv.PStmt.listUnconverted,
      LeanModels.Sv.PStmt.itemsUnconverted, LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?,
      LeanModels.Sv.Kernel.CoreMemDesign.readsV, LeanModels.Sv.Kernel.CoreMemDesign.readsIdxV,
      LeanModels.Sv.Kernel.CoreMemDesign.readsListV, LeanModels.Sv.Kernel.CoreMemDesign.memDecl?,
      LeanModels.Sv.Kernel.CoreMemDesign.widthsOf, LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryReadList,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall,
      LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCallList,
      LeanModels.Sv.Kernel.Elab.resolve, LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf,
      LeanModels.Sv.instExpr2, LeanModels.Sv.dynPartPlan, LeanModels.Sv.evalInt,
      LeanModels.Sv.arrayPartRead, LeanModels.Sv.arrayPartGeom, LeanModels.Sv.arrayDims,
      LeanModels.Sv.walkIndices, LeanModels.Sv.partLabels, LeanModels.Sv.labelOffset, LeanModels.Sv.dimsStride,
      LeanModels.Sv.dimCount, List.lookup, LeanModels.Sv.ctxOpWidth2, LeanModels.Sv.rigidMax2,
      LeanModels.Sv.selfWidth2, LeanModels.Sv.fitExpr2, LeanModels.Sv.rigidExpr,
      LeanModels.Sv.PExpr.ctxPropagates, LeanModels.Sv.PExpr.constLeaf, LeanModels.Sv.PExpr.negGenvarWidened,
      LeanModels.Sv.PExpr.signedCast])

/-- **`sv_seq_ports`**: the ports of a normal form. -/
macro "sv_seq_ports" : tactic =>
  `(tactic| simp [LeanModels.Sv.Kernel.CoreMemDesign.inputPorts, LeanModels.Sv.Kernel.CoreMemDesign.outputPorts])

/-- The evaluation pass of a cycle: the view functions and the route's evaluator unfolded. -/
macro "sv_seq_eval_pass" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : conv =>
  `(conv| simp (config := {maxSteps := 4000000, decide := true}) [-LeanModels.Sv.Res.bind_eq_ok,
      LeanModels.Sv.Kernel.CoreMemDesign.cycleV, LeanModels.Sv.Kernel.CoreMemDesign.slotV,
      LeanModels.Sv.Kernel.CoreMemDesign.settleV, LeanModels.Sv.Kernel.CoreMemDesign.settleRaw,
      LeanModels.Sv.Kernel.CoreMemDesign.matV, LeanModels.Sv.Kernel.CoreMemDesign.edgesV,
      LeanModels.Sv.Kernel.CoreMemEdge.fires, LeanModels.Sv.Kernel.CoreMemDesign.execV,
      LeanModels.Sv.Kernel.CoreMemDesign.execListV, LeanModels.Sv.Kernel.CoreMemDesign.execOptV,
      LeanModels.Sv.Kernel.CoreMemDesign.execItemsV, LeanModels.Sv.Kernel.CoreMemDesign.caseHitsV,
      LeanModels.Sv.Kernel.CoreMemDesign.setV, LeanModels.Sv.Kernel.CoreMemDesign.writeLhsV,
      LeanModels.Sv.caseHit, LeanModels.Sv.Kernel.caseClaimOk, LeanModels.Sv.Kernel.scalarNbaWindows,
      LeanModels.Sv.Kernel.scalarNbaWindows.go, LeanModels.Sv.resolveConcatLhs2, LeanModels.Sv.resolveLhs2,
      LeanModels.Sv.writeConcatLhs2, LeanModels.Sv.writeConcatLhs2.go,
      LeanModels.Sv.Kernel.CoreMemDesign.scalarLhs2, LeanModels.Sv.instLhs2, LeanModels.Sv.instLhsLeaf2,
      LeanModels.Sv.Kernel.CoreMemDesign.evalV, LeanModels.Sv.Kernel.CoreMemDesign.evalListV,
      LeanModels.Sv.Kernel.CoreMemDesign.evalIdxV, LeanModels.Sv.Kernel.CoreMemDesign.evalScalarV,
      LeanModels.Sv.Kernel.CoreMemDesign.widthsOf, LeanModels.Sv.Kernel.CoreMemDesign.scalarTarget,
      LeanModels.Sv.Kernel.CoreMemDesign.scalarWidth?, LeanModels.Sv.Kernel.Elab.resolve,
      LeanModels.Sv.Kernel.resolveAux, LeanModels.Sv.Kernel.Elab.declOf, LeanModels.Sv.applyInputs2,
      LeanModels.Sv.Kernel.Elab.toDesign2, LeanModels.Sv.Kernel.lowEntry, LeanModels.Sv.Kernel.highEntry,
      LeanModels.Sv.Kernel.seqE_commit_nil, LeanModels.Sv.Kernel.seqE_commit_cons, LeanModels.Sv.Kernel.Val.ofLVec, LeanModels.Sv.Kernel.VType.ofDecl,
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
      LeanModels.Sv.PExpr.signedCast, LeanModels.Sv.Kernel.seqE_ite_ok, LeanModels.Sv.Kernel.seqE_ite_pair,
      LeanModels.Sv.Kernel.seqE_ite_cons, LeanModels.Sv.Kernel.seqE_commit_ite, LeanModels.Sv.Kernel.seqE_append_ite,
      LeanModels.Sv.Kernel.seqE_ite_append, LeanModels.Sv.Kernel.seqE_ite_fst, LeanModels.Sv.Kernel.seqE_ite_snd,
      LeanModels.Sv.Kernel.seqE_resizeU_ite, LeanModels.Sv.Kernel.seqE_width_ite,
      LeanModels.Sv.Kernel.seqE_insertAt_zero, LeanModels.Sv.Kernel.seqE_width_lit,
      LeanModels.Sv.Kernel.seqE_width_add, LeanModels.Sv.Kernel.CoreMemDesign.cycleMV,
      LeanModels.Sv.Kernel.CoreMemDesign.dataV, LeanModels.Sv.Kernel.CoreMemDesign.tick,
      LeanModels.Sv.Kernel.Instant.row, LeanModels.Sv.Kernel.Instant.rise, LeanModels.Sv.Kernel.Instant.fall,
      LeanModels.Sv.Kernel.CoreMemDesign.memDecl?, List.find?, LeanModels.Sv.Kernel.CoreMemDecl.readV,
      LeanModels.Sv.Kernel.CoreMemDecl.issueV, LeanModels.Sv.Kernel.memNone, LeanModels.Sv.Kernel.commitMemV_nil,
      LeanModels.Sv.Kernel.commitMemV_memIss, LeanModels.Sv.Kernel.seqE_commitMemV_memIss,
      LeanModels.Sv.Kernel.seqE_commitMemV_ite, LeanModels.Sv.Kernel.seqE_memRd_ite,
      LeanModels.Sv.Kernel.seqE_memIss_ite, LeanModels.Sv.Kernel.memRd_memWrite,
      LeanModels.Sv.Kernel.MemShape.convert, LeanModels.Sv.Kernel.seqE_memRd_width,
      -LeanModels.Sv.evalPure2_index, LeanModels.Sv.Kernel.seqE_evalPure2_index,
      LeanModels.Sv.Kernel.seqE_resolveLhs2_index, LeanModels.Sv.evalExpr2_eq_evalPure2, LeanModels.Sv.Expr2.size,
      LeanModels.Sv.instIndex2, $ls,*])

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
