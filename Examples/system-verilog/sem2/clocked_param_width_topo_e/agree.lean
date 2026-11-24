import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleObl
open LeanModels.Sv LeanModels.Sv.Kernel
namespace Examples.«system-verilog».sem2.clocked_param_width_topo_e
load_design_sv2 cnt from "Examples/system-verilog/sem2/clocked_param_width_topo_e/clocked_param_width_topo_e.sv.json"
#guard match cnt.e 8 3 with
  | .ok E => E.topoC == true
  | _ => false
#guard match PDesign.instantiateCoreMem cnt.pdesign [8, 3] with
  | .ok E => E.topoC == true
  | _ => false
end Examples.«system-verilog».sem2.clocked_param_width_topo_e
