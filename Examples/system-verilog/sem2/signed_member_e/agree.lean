import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.signed_member_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 member from "Examples/system-verilog/sem2/signed_member_e/signed_member_e.sv.json"
#guard member.pdesign.others == []
#guard match member.e with | .ok _ => true | _ => false
end Examples.«system-verilog».sem2.signed_member_e
