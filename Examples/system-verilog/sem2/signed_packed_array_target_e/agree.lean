import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle
namespace Examples.«system-verilog».sem2.signed_packed_array_target_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 signedPackedArrayTarget from
  "Examples/system-verilog/sem2/signed_packed_array_target_e/signed_packed_array_target_e.sv.json"
private def d : MemDesign2 := signedPackedArrayTarget.pdesign.instantiateMemD2 []
#guard match runMem2 d 128 [[("s4", .ofInt 4 (-3)), ("u4", .ofNat 4 5)]] with
  | .unsupported msg => msg.contains "target"
  | _ => false
end Examples.«system-verilog».sem2.signed_packed_array_target_e
