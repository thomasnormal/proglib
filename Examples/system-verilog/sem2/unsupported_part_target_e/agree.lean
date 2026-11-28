import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle
namespace Examples.«system-verilog».sem2.unsupported_part_target_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 unsupportedPartTarget from
  "Examples/system-verilog/sem2/unsupported_part_target_e/unsupported_part_target_e.sv.json"
private def d : MemDesign2 := unsupportedPartTarget.pdesign.instantiateMemD2 []
#guard match runMem2 d 128 [[("d", .ofNat 16 48879)]] with
  | .unsupported msg => msg == "AssignmentExpression:target: a[3 -: 1] = d[7:0]"
  | _ => false
end Examples.«system-verilog».sem2.unsupported_part_target_e
