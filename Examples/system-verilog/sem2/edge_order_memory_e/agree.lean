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

end Examples.«system-verilog».sem2.edge_order_memory_e
