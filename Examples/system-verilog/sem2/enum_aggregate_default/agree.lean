import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 enumAggregate from "Examples/system-verilog/sem2/enum_aggregate_default/enum_aggregate_default.sv.json"
#guard match enumAggregate.e with | .ok _ => true | _ => false
