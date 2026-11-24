import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.package_scoped_type_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 p from "Examples/system-verilog/sem2/package_scoped_type_e/package_scoped_type_e.sv.json"
#guard p.pdesign.others == []
#guard match p.e with | .ok E => E.scalarWidth? "i_word" == some 8 && E.scalarWidth? "o_word" == some 8 | _ => false
end Examples.«system-verilog».sem2.package_scoped_type_e
