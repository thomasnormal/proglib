import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages
open LeanModels.Sv LeanModels.Sv.Kernel
namespace Examples.«system-verilog».sem2.clocked_param_width_topo_e
load_design_sv2 cnt from "Examples/system-verilog/sem2/clocked_param_width_topo_e/clocked_param_width_topo_e.sv.json"
#guard match cnt.e 8 3 with
  | .ok E => E.topoC == true
  | _ => false
#guard match PDesign.instantiateCoreMem cnt.pdesign [8, 3] with
  | .ok E => E.topoC == true
  | _ => false

set_option maxHeartbeats 1000000 in
theorem cnt_structure (D AW : Nat) : SeqDesign (cnt.e D AW) "clk" := by
  sv_structure

end Examples.«system-verilog».sem2.clocked_param_width_topo_e
