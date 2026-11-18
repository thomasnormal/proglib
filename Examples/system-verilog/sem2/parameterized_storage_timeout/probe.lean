import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 parameterizedStorage
  from "Examples/system-verilog/sem2/parameterized_storage_timeout/parameterized_storage_structure.sv.json"
#guard match parameterizedStorage.e 1 with
  | .unsupported msg => msg == "Comb:dependency-order: 9.2.2.2/9.4.2.2: reactive process reads 'stage' from itself or a later reactive process; canonical E has no fixed-point scheduler"
  | _ => false
#guard match parameterizedStorage.e 2 with
  | .unsupported msg => msg == "Comb:dependency-order: 9.2.2.2/9.4.2.2: reactive process reads 'stage' from itself or a later reactive process; canonical E has no fixed-point scheduler"
  | _ => false
