import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages
import LeanModels.Sv.SeqCycleObl
import LeanModels.Sv.Kernel.EdgePhaseConfluence

namespace Examples.«system-verilog».sem2.edge_order_memory_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 edgeMemory
  from "Examples/system-verilog/sem2/edge_order_memory_e/edge_order_memory_e.sv.json"

#eval match edgeMemory.e 4 with
  | .ok E => (E.processes.size, E.oblDrivers, E.oblEdgeOrderMemory)
  | _ => (0, false, false)

#guard match edgeMemory.e 4 with
  | .ok E => E.oblEdgeOrderMemory == true
  | _ => false

#guard match edgeMemory.e 4 with
  | .ok E => E.seqOblIM == true
  | _ => false

end Examples.«system-verilog».sem2.edge_order_memory_e

namespace Examples.«system-verilog».sem2.edge_order_memory_e
open LeanModels.Sv LeanModels.Sv.Kernel

/-! The memory-aware terminal relation also preserves scalar queue order up to
permutation. This receipt keeps the source fixture in the same module as the
generic theorem use, while all memory commit and decode obligations remain
explicit in the kernel theorem. -/
example {E : CoreMemDesign} {s t₁ t₂ : EdgePhaseState} {n₁ n₂ : Nat}
    (ad : EdgePhaseMemoryAdmission E s)
    (q : EdgeCursor → NbaQueue2)
    (hqueue : ∀ cursor result next, cursor ∈ s.active →
      cursor.resume E s.state = .ok (result, next) → result.scalarQ = q cursor)
    (hp₁ : EdgePhaseTerminalPath E n₁ s t₁)
    (hp₂ : EdgePhaseTerminalPath E n₂ s t₂) :
    t₁.scalarQ.Perm t₂.scalarQ := by
  exact EdgePhaseTerminalPath.scalar_queue_perm_memory ad q hqueue hp₁ hp₂

example :
    commitNba2 [] (([] : NbaQueue2) ++ []) = commitNba2 [] ([] ++ []) ∧
      commitMemV memNone (([] : MemQV) ++ []) = commitMemV memNone ([] ++ []) := by
  exact commitMixed_swap (st := []) (mv := memNone) (by simp) (by simp) (by simp)

example (v : SvState) (values : List Int) (m : Int → MemQV) :
    execLoopV v (fun i => .ok (v, [], m i)) values =
      .ok (v, [], values.flatMap m) := by
  exact execLoopV_memory v m values

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (it : String) (init condition step : PExpr) (body : PStmt) (values : List Int)
    (hloop : PStmt.loopBodyB body = true)
    (hvals : forValues2 env it init condition step = .ok values)
    (hbody : ∀ i, ∃ mq, E.execV (env.bindVal it i) v mv body = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes)) :
    ∃ mq, E.execV env v mv (.forLoop it init condition step body) = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes) := by
  exact CoreMemDesign.execV_forLoop_memory_records env v mv hloop hvals hbody

example (body : PStmt) (h : PStmt.loopNbaMemory body = true) :
    PStmt.loopBodyB body = true := by
  exact PStmt.loopNbaMemory_loopBodyB body h

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (body : PStmt) (it : String) (init condition step : PExpr) (values : List Int)
    (hbodyP : PStmt.loopNbaMemory body = true)
    (hvals : forValues2 env it init condition step = .ok values)
    (hbody : ∀ i, ∃ mq, E.execV (env.bindVal it i) v mv body = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes)) :
    ∃ mq, E.execV env v mv (.forLoop it init condition step body) = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes) := by
  exact CoreMemDesign.execV_forLoop_memory_records_of_loopNbaMemory
    env v mv hbodyP hvals hbody

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (body : List PStmt) (v' : SvState) (q : NbaQueue2) (mq : MemQV)
    (hbody : ∀ s ∈ body, ∃ name index e, s = PStmt.nbaAssignL (.arrayElem name [index]) e ∧
      ∃ md, E.memDecl? name = some md)
    (h : E.execListV env v mv body = .ok (v', q, mq)) :
    v' = v ∧ q = [] ∧ (∀ u ∈ mq, u.1 ∈ PStmt.listWrites body) := by
  exact CoreMemDesign.execListV_memory_leaves env v mv body v' q mq hbody h

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (body : PStmt) (v' : SvState) (q : NbaQueue2) (mq : MemQV)
    (hshape : body.memoryLeafB = true)
    (hdecl : ∀ n ∈ body.writes, ∃ md, E.memDecl? n = some md)
    (h : E.execV env v mv body = .ok (v', q, mq)) :
    v' = v ∧ q = [] ∧ (∀ u ∈ mq, u.1 ∈ body.writes) := by
  exact CoreMemDesign.execV_memoryLeafBody env v mv body v' q mq hshape hdecl h

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (subject : PExpr) (items : List (List PExpr × PStmt)) (d : Option PStmt)
    (mode : CaseMode) (check : CaseCheck) (v' : SvState) (q : NbaQueue2) (mq : MemQV)
    (hitems : ∀ item ∈ items, item.2.memoryLeafB = true)
    (hdecl : ∀ n ∈ (PStmt.caseStmt subject items d mode check).writes,
      ∃ md, E.memDecl? n = some md)
    (hdflt : PStmt.optMemoryLeafB d = true)
    (h : E.execV env v mv (.caseStmt subject items d mode check) = .ok (v', q, mq)) :
    v' = v ∧ q = [] ∧
      (∀ u ∈ mq, u.1 ∈ (PStmt.caseStmt subject items d mode check).writes) := by
  exact CoreMemDesign.execV_case_memoryLeafBody env v mv hitems hdecl hdflt h

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (body : PStmt) (it : String) (init condition step : PExpr) (values : List Int)
    (hshape : PStmt.memoryLeafB body = true)
    (hdecl : ∀ n ∈ body.writes, ∃ md, E.memDecl? n = some md)
    (hvals : forValues2 env it init condition step = .ok values)
    (hbody : ∀ i, i ∈ values → ∃ mq,
      E.execV (env.bindVal it i) v mv body = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes)) :
    ∃ mq, E.execV env v mv (.forLoop it init condition step body) = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes) := by
  exact CoreMemDesign.execV_forLoop_memoryLeafBody env v mv hshape hdecl hvals hbody

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (body : PStmt) (it : String) (init condition step : PExpr)
    (hshape : PStmt.memoryLeafB body = true)
    (hdecl : ∀ n ∈ body.writes, ∃ md, E.memDecl? n = some md)
    {v' : SvState} {q : NbaQueue2} {mq : MemQV}
    (h : E.execV env v mv (.forLoop it init condition step body) = .ok (v', q, mq)) :
    v' = v ∧ q = [] ∧ (∀ u ∈ mq, u.1 ∈ body.writes) := by
  exact CoreMemDesign.execV_forLoop_memoryLeafBody_of_success
    env v mv hshape hdecl h

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (guard : PExpr) (it : String) (init condition step : PExpr) (body : PStmt)
    (hshape : PStmt.memoryLeafB body = true)
    (hdecl : ∀ n ∈ (PStmt.ifStmt guard (.forLoop it init condition step body) none).writes,
      ∃ md, E.memDecl? n = some md)
    (values : List Int)
    (hvals : forValues2 env it init condition step = .ok values)
    (hbody : ∀ i, i ∈ values → ∃ mq,
      E.execV (env.bindVal it i) v mv body = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes))
    {v' : SvState} {q : NbaQueue2} {mq : MemQV}
    (h : E.execV env v mv
        (.ifStmt guard (.forLoop it init condition step body) none) = .ok (v', q, mq)) :
    v' = v ∧ q = [] ∧ (∀ u ∈ mq, u.1 ∈ body.writes) := by
  exact CoreMemDesign.execV_if_forLoop_memoryLeafBody env v mv hshape hdecl hvals hbody h

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (guard : PExpr) (it : String) (init condition step : PExpr) (body : PStmt)
    (hshape : PStmt.memoryLeafB body = true)
    (hdecl : ∀ n ∈ (PStmt.ifStmt guard (.forLoop it init condition step body) none).writes,
      ∃ md, E.memDecl? n = some md)
    {v' : SvState} {q : NbaQueue2} {mq : MemQV}
    (h : E.execV env v mv
        (.ifStmt guard (.forLoop it init condition step body) none) = .ok (v', q, mq)) :
    v' = v ∧ q = [] ∧ (∀ u ∈ mq, u.1 ∈ body.writes) := by
  exact CoreMemDesign.execV_if_forLoop_memoryLeafBody_of_success
    env v mv hshape hdecl h

/-! The memory-aware edge-order successor is exercised on the real `edgesV`
    boundary.  The frame receipt stays an explicit premise until the
    predicate-to-receipt proof is widened for every admitted body shape. -/
example (E : CoreMemDesign) (before after : SvState) (v : SvState) (mv : MemV)
    (ps : List CoreMemProc) (hσ : ps.Perm E.processes.toList)
    (hv : (v.map Prod.fst).Nodup)
    (hnd : (E.processes.toList.flatMap CoreMemProc.targets).Nodup)
    (hO : E.oblEdgeOrderMemory = true)
    (hlocal : ∀ (f : CoreMemEdge) (v' : SvState) (q : NbaQueue2) (mq : MemQV),
      E.execV E.env v mv f.body = .ok (v', q, mq) →
      v' = v ∧ (∀ u ∈ q, u.1 ∈ f.body.writes) ∧ (∀ u ∈ mq, u.1 ∈ f.body.writes))
    {r : ExecV} (h : E.edgesV before after v mv E.processes.toList = .ok r) :
    ∃ r', E.edgesV before after v mv ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      commitMemV mv r'.2.2 = commitMemV mv r.2.2 := by
  exact CoreMemDesign.edgesV_order_memory hO hσ hv hnd hlocal h

/-! The exact memory-leaf profile supplies the evaluator frame receipt, so the
    edge-order theorem needs no separately duplicated semantic premise. -/
example (E : CoreMemDesign) (before after : SvState) (v : SvState) (mv : MemV)
    (ps : List CoreMemProc) (hσ : ps.Perm E.processes.toList)
    (hv : (v.map Prod.fst).Nodup)
    (hnd : (E.processes.toList.flatMap CoreMemProc.targets).Nodup)
    (hO : E.oblEdgeOrderMemory = true)
    (hshape : ∀ f : CoreMemEdge, f.body.memoryLeafB = true)
    (hdecl : ∀ f : CoreMemEdge, ∀ n ∈ f.body.writes,
      ∃ md, E.memDecl? n = some md)
    {r : ExecV} (h : E.edgesV before after v mv E.processes.toList = .ok r) :
    ∃ r', E.edgesV before after v mv ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      commitMemV mv r'.2.2 = commitMemV mv r.2.2 := by
  exact CoreMemDesign.edgesV_order_memory_memoryLeaf hO hσ hv hnd hshape hdecl h

example (E : CoreMemDesign) (before after : SvState) (v : SvState) (mv : MemV)
    (ps : List CoreMemProc) (hσ : ps.Perm E.processes.toList)
    (hv : (v.map Prod.fst).Nodup)
    (hnd : (E.processes.toList.flatMap CoreMemProc.targets).Nodup)
    (hO : E.seqOblIM = true)
    (hlocal : ∀ (f : CoreMemEdge) (v' : SvState) (q : NbaQueue2) (mq : MemQV),
      E.execV E.env v mv f.body = .ok (v', q, mq) →
      v' = v ∧ (∀ u ∈ q, u.1 ∈ f.body.writes) ∧ (∀ u ∈ mq, u.1 ∈ f.body.writes))
    {r : ExecV} (h : E.edgesV before after v mv E.processes.toList = .ok r) :
    ∃ r', E.edgesV before after v mv ps = .ok r' ∧
      commitNba2 r'.1 r'.2.1 = commitNba2 r.1 r.2.1 ∧
      commitMemV mv r'.2.2 = commitMemV mv r.2.2 := by
  exact CoreMemDesign.edgesV_order_memory_seqOblIM hO hσ hv hnd hlocal h

example (E : CoreMemDesign) (hP : E.SeqProfileI) (hO : E.seqOblIM = true)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory)
    {entry : SvState} (hty : EntryTyped E.scalar.toDesign2 entry)
    {v' : SvState} {mv' : MemV}
    (hv : E.slotV (E.scalar.view st.scalar) (E.memOf st.memory) entry = .ok (v', mv')) :
    ∃ st', E.step st entry = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.memOf st'.memory = mv' ∧ E.Coherent st' ∧ E.MemCoherent st'.memory := by
  exact CoreMemDesign.step_seqIM hP hO hc hmc hty hv

end Examples.«system-verilog».sem2.edge_order_memory_e
