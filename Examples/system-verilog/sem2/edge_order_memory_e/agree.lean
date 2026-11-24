import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages
import LeanModels.Sv.SeqCycleObl

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

end Examples.«system-verilog».sem2.edge_order_memory_e

namespace Examples.«system-verilog».sem2.edge_order_memory_e
open LeanModels.Sv LeanModels.Sv.Kernel

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

end Examples.«system-verilog».sem2.edge_order_memory_e
