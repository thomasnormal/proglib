import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.generate_walls_w2_per_instance
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 w2a from "Examples/system-verilog/sem2/generate_walls_w2_per_instance/w2a_gfor_scalar.json"
load_design_sv2 w2c from "Examples/system-verilog/sem2/generate_walls_w2_per_instance/w2c_gfor_unpacked.json"
load_design_sv2 w2e from "Examples/system-verilog/sem2/generate_walls_w2_per_instance/w2e_two_loops_same_name.json"
load_design_sv2 w2f from "Examples/system-verilog/sem2/generate_walls_w2_per_instance/w2f_shadow_module_name.json"
load_design_sv2 w2h from "Examples/system-verilog/sem2/generate_walls_w2_per_instance/w2h_gfor_no_decl.json"
def names (d : CoreMemDesign) : List String := d.elems.map (fun (x : String × Nat) => x.1)
#guard match PDesign.instantiateE2 w2a.pdesign [2] (PDesign.surfaceFuel [2]) with
  | .ok d => names d == ["a", "q", "g[0].t", "g[1].t"]
  | _ => false
#guard match PDesign.instantiateE2 w2c.pdesign [2] (PDesign.surfaceFuel [2]) with
  | .ok d => names d == ["a", "q", "g[0].t[0]", "g[0].t[1]", "g[1].t[0]", "g[1].t[1]"]
  | _ => false
#guard match PDesign.instantiateE2 w2e.pdesign [2] (PDesign.surfaceFuel [2]) with
  | .ok d => names d == ["a", "q", "p", "g[0].t", "g[1].t", "h[0].t", "h[1].t"]
  | _ => false
#guard match PDesign.instantiateE2 w2f.pdesign [2] (PDesign.surfaceFuel [2]) with
  | .ok d => names d == ["a", "q", "z", "t", "g[0].t", "g[1].t"]
  | _ => false
#guard match PDesign.instantiateE2 w2h.pdesign [2] (PDesign.surfaceFuel [2]) with
  | .ok d => true
  | _ => false
end Examples.«system-verilog».sem2.generate_walls_w2_per_instance
