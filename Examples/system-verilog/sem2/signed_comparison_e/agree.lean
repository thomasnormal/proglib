import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.signed_comparison_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 signedCmp from "Examples/system-verilog/sem2/signed_comparison_e/signed_comparison_e.sv.json"
#guard signedCmp.pdesign.others == []
#guard match signedCmp.e with | .ok E => E.scalarWidth? "y" == some 1 | _ => false
end Examples.«system-verilog».sem2.signed_comparison_e
