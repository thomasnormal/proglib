import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem
namespace Examples.«system-verilog».sem2.specify_functional_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 specify from "Examples/system-verilog/sem2/specify_functional_e/specify_functional_e.sv.json"
#guard specify.pdesign.others == []
#guard match PDesign.instantiateE2H specify.pdesign specify.plib [] with | .ok _ => true | .timeout => true | .unsupported _ => true
end Examples.«system-verilog».sem2.specify_functional_e
