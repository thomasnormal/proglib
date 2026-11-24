import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.package_defaults_e
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 p from "Examples/system-verilog/sem2/package_defaults_e/package_defaults_e.sv.json"

#guard p.pdesign.others == []
#guard match p.e with
  | .ok E =>
      E.scalarWidth? "i_default" == some 4 &&
      E.scalarWidth? "o_default" == some 4 &&
      E.scalarWidth? "i_chain" == some 2 &&
      E.scalarWidth? "o_chain" == some 2 &&
      E.scalarWidth? "i_local" == some 2 &&
      E.scalarWidth? "o_local" == some 2 &&
      E.scalarWidth? "i_typed" == some 8 &&
      E.scalarWidth? "o_typed" == some 8
  | _ => false

end Examples.«system-verilog».sem2.package_defaults_e
