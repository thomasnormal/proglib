import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 disjoint_concat_edge
  from "Examples/system-verilog/cores/picorv32/walls/disjoint_concat_edge/disjoint_concat_edge.sv.json"

def result : Res CoreMemDesign :=
  disjoint_concat_edge.e

#guard match result with
  | .unsupported msg => msg.startsWith "Event:multiple-write"
  | _ => false

#guard disjoint_concat_edge.pdesign.processes.length == 2
#guard coreMemEdgeMultipleWritePair
  disjoint_concat_edge.pdesign.processes[0]!
  disjoint_concat_edge.pdesign.processes[1]!
