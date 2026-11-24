import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.generate_scope_unpacked_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 gen from "Examples/system-verilog/sem2/generate_scope_unpacked_e/generate_scope_unpacked_e.sv.json"
#guard gen.pdesign.others == []
#guard match PDesign.instantiateCoreMem gen.pdesign [1] with | .ok _ => true | _ => false
end Examples.«system-verilog».sem2.generate_scope_unpacked_e
