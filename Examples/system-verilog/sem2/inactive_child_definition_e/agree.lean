import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.inactive_child_definition_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 inactive from
  "Examples/system-verilog/sem2/inactive_child_definition_e/inactive_child_definition.sv.json"

#guard match inactive.e 0 with | .ok _ => true | _ => false
#guard match inactive.e 1 with | .ok d => !CoreMemDesign.Structure d | _ => false

end Examples.«system-verilog».sem2.inactive_child_definition_e
