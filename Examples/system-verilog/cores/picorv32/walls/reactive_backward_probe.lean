import LeanModels.Sv.Ingest2

set_option maxRecDepth 100000 in
load_design_sv2 reactive_backward
  from "Examples/system-verilog/cores/picorv32/walls/reactive_backward.sv.json"

#guard match reactive_backward.e with
  | .unsupported msg =>
      msg == "Comb:dependency-order: 9.2.2.2/9.4.2.2: reactive process reads 't' from itself or a later reactive process; canonical E has no fixed-point scheduler"
  | _ => false
