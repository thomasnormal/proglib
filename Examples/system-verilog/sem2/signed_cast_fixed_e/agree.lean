import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.signed_cast_fixed_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 cast from "Examples/system-verilog/sem2/signed_cast_fixed_e/signed_cast_fixed_e.sv.json"
#guard cast.pdesign.others == []
#guard match cast.e with | .ok E => E.scalarWidth? "y" == some 8 && E.scalarWidth? "lt" == some 1 | _ => false
end Examples.«system-verilog».sem2.signed_cast_fixed_e
