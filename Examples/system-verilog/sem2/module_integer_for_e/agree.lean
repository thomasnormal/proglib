import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.module_integer_for_e
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 p from
  "Examples/system-verilog/sem2/module_integer_for_e/module_integer_for_e.sv.json"

#guard p.pdesign.others == []
#guard match p.e 2 with | .ok _ => true | _ => false

end Examples.«system-verilog».sem2.module_integer_for_e
