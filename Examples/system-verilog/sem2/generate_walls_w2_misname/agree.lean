import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.generate_walls_w2_misname
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 w2 from "Examples/system-verilog/sem2/generate_walls_w2_misname/w2.json"
#guard match w2.pdesign.generates with
  | [.genFor (some "g") "k" _ _ _ (some 2) [.unsupported "GenerateDecl:instance-name" _]] => true
  | _ => false
end Examples.«system-verilog».sem2.generate_walls_w2_misname
