import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

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

end Examples.«system-verilog».sem2.edge_order_memory_e
