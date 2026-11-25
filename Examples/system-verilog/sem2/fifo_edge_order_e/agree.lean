import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.SeqCycleObl

namespace Examples.«system-verilog».sem2.fifo_edge_order_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 fifo
  from "Examples/system-verilog/sem2/fifo_edge_order_e/fifo_edge_order_e.sv.json"

#guard match PDesign.instantiateCoreMem fifo.pdesign [8, 4] with
  | .ok d => d.memories.size == 1 && d.processes.size == 3
  | _ => false

#guard match PDesign.instantiateCoreMem fifo.pdesign [8, 4] with
  | .ok d => d.oblEdgeOrder == false && d.oblEdgeOrderMemory == false
  | _ => false

example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV)
    (it : String) (init condition step : PExpr) (body : PStmt) (values : List Int)
    (hloop : PStmt.loopBodyB body = true)
    (hvals : forValues2 env it init condition step = .ok values)
    (hbody : ∀ i, ∃ mq, E.execV (env.bindVal it i) v mv body = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes)) :
    ∃ mq, E.execV env v mv (.forLoop it init condition step body) = .ok (v, [], mq) ∧
      (∀ u ∈ mq, u.1 ∈ body.writes) := by
  exact CoreMemDesign.execV_forLoop_memory_records env v mv hloop hvals hbody

#print axioms CoreMemDesign.execV_forLoop_memory_records

end Examples.«system-verilog».sem2.fifo_edge_order_e
