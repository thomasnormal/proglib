import LeanModels.Sv.Ingest2

set_option maxRecDepth 100000 in
load_design_sv2 unary_initializer
  from "Examples/system-verilog/cores/darkriscv/walls/unary_initializer.sv.json"

open LeanModels.Sv

def accepted : Bool :=
  !(unary_initializer.pdesign.instantiateD2 [] |>.hasUnsupported)

#guard accepted
