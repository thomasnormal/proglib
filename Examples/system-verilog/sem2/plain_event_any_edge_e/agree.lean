import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleObl
open LeanModels.Sv LeanModels.Sv.Kernel
namespace Examples.«system-verilog».sem2.plain_event_any_edge_e
load_design_sv2 any from "Examples/system-verilog/sem2/plain_event_any_edge_e/plain_event_any_edge_e.sv.json"
#guard match any.e with
  | .ok E => E.processes.size == 1 && E.processes[0]?.map CoreMemProc.isEdge == some false
  | _ => false
end Examples.«system-verilog».sem2.plain_event_any_edge_e
