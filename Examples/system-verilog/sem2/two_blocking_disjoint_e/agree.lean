import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Kernel.CombPhaseFrame
import LeanModels.Sv.Kernel.EdgePhaseConfluence
import LeanModels.Sv.Kernel.ConditionalConfluence
namespace Examples.«system-verilog».sem2.two_blocking_disjoint_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 twoBlocking from "Examples/system-verilog/sem2/two_blocking_disjoint_e/two_blocking_disjoint_e.sv.json"

def guardReceipt : Bool :=
  match twoBlocking.pdesign.processes with
  | [p, q] =>
      match coreMemHasCommonEventSourceThroughAssign [p, q] p q with
      | true =>
          (coreMemProcBlockingWrites p).contains "a" &&
          (coreMemProcBlockingWrites q).contains "b"
      | false => false
  | _ => false

#guard guardReceipt

example {state : SvState} {a b a' b' : LVec} :
    SvState.agreesOutside ["a", "b"]
      (SvState.set (SvState.set state "a" a) "b" b)
      (SvState.set (SvState.set state "b" b') "a" a') := by
  exact SvState.agreesOutside_two_set_of_mem (by simp) (by simp)

example : CombPhaseGuard twoBlocking.pdesign := by
  constructor <;> decide

example : ∃ p q,
    twoBlocking.pdesign.processes = [p, q] ∧
    coreMemHasCommonEventSourceThroughAssign [p, q] p q = true := by
  exact ⟨twoBlocking.pdesign.processes[0]!, twoBlocking.pdesign.processes[1]!, by rfl, by decide⟩

example : ∃ p q,
    twoBlocking.pdesign.processes = [p, q] ∧
    (∀ x, x ∈ coreMemProcBlockingWrites p →
      x ∉ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames q)) ∧
    (∀ x, x ∈ coreMemProcBlockingWrites q →
      x ∉ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames p)) := by
  obtain ⟨p, q, hprocesses, hcommon⟩ := show ∃ p q,
      twoBlocking.pdesign.processes = [p, q] ∧
      coreMemHasCommonEventSourceThroughAssign [p, q] p q = true from
    ⟨twoBlocking.pdesign.processes[0]!, twoBlocking.pdesign.processes[1]!, by rfl, by decide⟩
  have hg : CombPhaseGuard twoBlocking.pdesign := by
    constructor <;> decide
  exact ⟨p, q, hprocesses,
    (hg.two_process_read_write_exclusions hprocesses hcommon).1,
    (hg.two_process_read_write_exclusions hprocesses hcommon).2⟩

theorem guarded_pair_receipt
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {p q : PProcess}
    (hprocesses : twoBlocking.pdesign.processes = [p, q])
    (hcommon : coreMemHasCommonEventSourceThroughAssign [p, q] p q = true)
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hdecl : xN.decl ≠ xM.decl)
    (hn : n ∈ view.map Prod.fst)
    (hm : m ∈ view.map Prod.fst)
    (hneq : n ≠ m)
    (hkeys : (view.map Prod.fst).Nodup)
    (hlocalN : SvState.lookup locals n = none)
    (hlocalM : SvState.lookup locals m = none)
    (htargetN : E.scalarTarget n = some widthN)
    (htargetM : E.scalarTarget m = some widthM)
    (htestN : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs eN = false)
    (htestM : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs eM = false)
    (hmemN : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead eN = false)
    (hcallN : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall eN = false)
    (hmemM : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead eM = false)
    (hcallM : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall eM = false)
    (hne : E.elems ≠ [])
    (hvalN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hclosureM : ∀ y ∈ E.readsV env E.elems (some widthM) eM,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames q))
    (hclosureN : ∀ y ∈ E.readsV env E.elems (some widthN) eN,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames p))
    (hnwrites : n ∈ coreMemProcBlockingWrites p)
    (hmwrites : m ∈ coreMemProcBlockingWrites q) :
    let cN : CombCursor :=
      { work := [.stmt env (.blockingAssign n eN)], locals := locals }
    let cM : CombCursor :=
      { work := [.stmt env (.blockingAssign m eM)], locals := locals }
    ∃ u₁ u₂ z,
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₁ ∧
      CombPhaseStep E { state := st, view := view, active := [cN, cM] } u₂ ∧
      CombPhaseStep E u₁ z ∧ CombPhaseStep E u₂ z := by
  have hg : CombPhaseGuard twoBlocking.pdesign := by
    constructor <;> decide
  exact CombPhaseStep.two_blocking_scalar_diamond_of_design_guard
    (d := twoBlocking.pdesign) hg hprocesses hcommon hc hxN hxM hdecl hn hm hneq
    hkeys hlocalN hlocalM htargetN htargetM htestN htestM hmemN hcallN hmemM
    hcallM hne hvalN hvalM hclosureM hclosureN hnwrites hmwrites

theorem guarded_hidden_terminal_receipt
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {xN xM : VarId} {vN vM : LVec}
    {p q : PProcess}
    (hprocesses : twoBlocking.pdesign.processes = [p, q])
    (hcommon : coreMemHasCommonEventSourceThroughAssign [p, q] p q = true)
    (hc : E.Coherent st)
    (hxN : E.scalar.resolve n = some xN)
    (hxM : E.scalar.resolve m = some xM)
    (hlocalN : SvState.lookup locals n = none)
    (hlocalM : SvState.lookup locals m = none)
    (htargetN : E.scalarTarget n = some widthN)
    (htargetM : E.scalarTarget m = some widthM)
    (htestN : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs eN = false)
    (htestM : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs eM = false)
    (hmemN : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead eN = false)
    (hcallN : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall eN = false)
    (hmemM : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasMemoryRead eM = false)
    (hcallM : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasFunctionCall eM = false)
    (hne : E.elems ≠ [])
    (hvalN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalM : E.evalExprLocals env E.elems st (some widthM) locals eM = .ok vM)
    (hclosureM : ∀ y ∈ E.readsV env E.elems (some widthM) eM,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames q))
    (hclosureN : ∀ y ∈ E.readsV env E.elems (some widthN) eN,
      y ∈ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames p))
    (hnwrites : n ∈ coreMemProcBlockingWrites p)
    (hmwrites : m ∈ coreMemProcBlockingWrites q) :
    ∃ kN tN kM tM,
      CombPhaseTerminalPath E kN
        { state := st, view := view,
          active := [ { work := [.stmt env (.blockingAssign n eN)], locals := locals },
                      { work := [.stmt env (.blockingAssign m eM)], locals := locals } ] } tN ∧
      CombPhaseTerminalPath E kM
        { state := st, view := view,
          active := [ { work := [.stmt env (.blockingAssign n eN)], locals := locals },
                      { work := [.stmt env (.blockingAssign m eM)], locals := locals } ] } tM ∧
      SvState.agreesOutside [n, m] tN.view tM.view := by
  have hg : CombPhaseGuard twoBlocking.pdesign := by
    constructor <;> decide
  exact CombPhaseTerminalPath.two_blocking_scalar_hidden_observation_of_design_guard
    (hidden := [n, m]) (d := twoBlocking.pdesign) hg hprocesses hcommon hc hxN hxM
    hlocalN hlocalM htargetN htargetM htestN htestM hmemN hcallN hmemM hcallM
    hne hvalN hvalM hclosureM hclosureN hnwrites hmwrites (by simp) (by simp)

theorem executor_bridge_receipt
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n : String} {value : PExpr} {width : Nat} {v : LVec}
    {tail : List CombWork}
    (hlocal : SvState.lookup locals n = none)
    (hlocals : locals = [])
    (htarget : E.scalarTarget n = some width)
    (htest : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs value = false)
    (hvalue : E.evalExprLocals env E.elems st (some width) locals value = .ok v) :
    E.execCombStmtAtView env E.elems st view (.blockingAssign n value) =
        .ok (E.setScalarState st n v, SvState.set view n v) ∧
      CombCursor.resume E st view
          { work := .stmt env (.blockingAssign n value) :: tail, locals := locals } =
        .ok (E.setScalarState st n v, SvState.set view n v,
          { work := tail, locals := locals }) := by
  exact CombCursor.resume_blocking_scalar_of_exec
    hlocal hlocals htarget htest hvalue

theorem initial_runner_bridge_receipt
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n : String} {value : PExpr} {width : Nat} {v : LVec}
    (hlocal : SvState.lookup locals n = none)
    (hlocals : locals = [])
    (htarget : E.scalarTarget n = some width)
    (htest : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs value = false)
    (hvalue : E.evalExprLocals env E.elems st (some width) locals value = .ok v)
    (hproc : env = E.env) :
    E.runCombInitialWithView st view
        [.comb (.blockingAssign n value)] =
      .ok (E.compactScalar (E.setScalarState st n v) (SvState.set view n v),
        SvState.set view n v) := by
  exact CoreMemDesign.runCombInitialWithView_blocking_scalar
    hlocal hlocals htarget htest hvalue hproc

theorem executor_two_statement_bridge_receipt
    {E : CoreMemDesign} {st : CoreMemState} {view locals : SvState}
    {env : IEnv} {n m : String} {eN eM : PExpr}
    {widthN widthM : Nat} {vN vM : LVec}
    (hlocalN : SvState.lookup locals n = none)
    (hlocalM : SvState.lookup locals m = none)
    (hlocals : locals = [])
    (htargetN : E.scalarTarget n = some widthN)
    (htargetM : E.scalarTarget m = some widthM)
    (htestN : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs eN = false)
    (htestM : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs eM = false)
    (hvalueN : E.evalExprLocals env E.elems st (some widthN) locals eN = .ok vN)
    (hvalueM : E.evalExprLocals env E.elems (E.setScalarState st n vN)
      (some widthM) locals eM = .ok vM) :
    E.execCombStmtAtView env E.elems st view
        (.block [.blockingAssign n eN, .blockingAssign m eM]) =
      .ok (E.setScalarState (E.setScalarState st n vN) m vM,
        SvState.set (SvState.set view n vN) m vM) := by
  exact CoreMemDesign.execCombStmtAtView_two_blocking_scalar
    hlocalN hlocalM hlocals htargetN htargetM htestN htestM hvalueN hvalueM

theorem initial_runner_two_process_bridge_receipt
    {E : CoreMemDesign} {st : CoreMemState} {view : SvState}
    {n m : String} {eN eM : PExpr} {widthN widthM : Nat} {vN vM : LVec}
    (htargetN : E.scalarTarget n = some widthN)
    (htargetM : E.scalarTarget m = some widthM)
    (htestN : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs eN = false)
    (htestM : LeanModels.Sv.Kernel.LeanModels.Sv.PExpr.hasTestPlusargs eM = false)
    (hvalueN : E.evalExprLocals E.env E.elems st (some widthN) [] eN = .ok vN)
    (hcompactN : E.compactScalar (E.setScalarState st n vN)
        (SvState.set view n vN) = E.setScalarState st n vN)
    (hvalueM : E.evalExprLocals E.env E.elems (E.setScalarState st n vN)
        (some widthM) [] eM = .ok vM) :
    E.runCombInitialWithView st view
        [.comb (.blockingAssign n eN), .comb (.blockingAssign m eM)] =
      .ok (E.compactScalar
        (E.setScalarState (E.setScalarState st n vN) m vM)
        (SvState.set (SvState.set view n vN) m vM),
        SvState.set (SvState.set view n vN) m vM) := by
  exact CoreMemDesign.runCombInitialWithView_two_blocking_scalar
    htargetN htargetM htestN htestM hvalueN hcompactN hvalueM

theorem terminal_pair_receipt
    {E : CoreMemDesign} {s : CombPhaseState}
    {c₁ c₂ n₁ n₂ : CombCursor}
    {x₁ x₂ y₁ y₂ : CoreMemState} {v₁ v₂ w₁ w₂ : SvState}
    (ha : s.active = [c₁, c₂])
    (h₁ : c₁.resume E s.state s.view = .ok (x₁, v₁, n₁))
    (h₂ : c₂.resume E s.state s.view = .ok (x₂, v₂, n₂))
    (h₂₁ : c₂.resume E x₁ v₁ = .ok (y₁, w₁, n₂))
    (h₁₂ : c₁.resume E x₂ v₂ = .ok (y₂, w₂, n₁))
    (hstate : y₁ = y₂) (hview : w₁ = w₂)
    (hn₁ : n₁.work = []) (hn₂ : n₂.work = []) :
    ∃ na ta nb tb,
      CombPhaseTerminalPath E na s ta ∧
      CombPhaseTerminalPath E nb s tb ∧
      ta = { state := y₁, view := w₁, active := [] } ∧
      tb = { state := y₁, view := w₁, active := [] } := by
  exact CombPhaseTerminalPath.two_cursor_terminal
    ha h₁ h₂ h₂₁ h₁₂ hstate hview hn₁ hn₂

#print axioms guardReceipt
#print axioms guarded_pair_receipt
#print axioms guarded_hidden_terminal_receipt
#print axioms executor_bridge_receipt
#print axioms initial_runner_bridge_receipt
#print axioms executor_two_statement_bridge_receipt
#print axioms initial_runner_two_process_bridge_receipt
#print axioms terminal_pair_receipt
end Examples.«system-verilog».sem2.two_blocking_disjoint_e
