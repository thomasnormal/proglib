import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.ibex_lockstep_offset_e
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 p from
  "Examples/system-verilog/sem2/ibex_lockstep_offset_e/ibex_lockstep_offset_e.sv.json"

#guard p.pdesign.others == []
#guard match p.e 4 with | .ok E => E.scalarWidth? "i" == some 2 && E.scalarWidth? "o" == some 2 | _ => false

end Examples.«system-verilog».sem2.ibex_lockstep_offset_e
