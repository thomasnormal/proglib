import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.signed_net_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 signed from "Examples/system-verilog/sem2/signed_net_e/signed_net_e.sv.json"
#guard signed.pdesign.others == []
#guard match signed.e with | .ok E => E.scalarWidth? "y" == some 4 && E.scalarWidth? "lt" == some 1 | _ => false
end Examples.«system-verilog».sem2.signed_net_e
