/- Canonical-E admission receipt for parser-native IEEE 1800-2023 inout ports. -/
import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.inout_wall.agree
open LeanModels.Sv
load_design_sv2 inoutWall from "Examples/system-verilog/sem2/inout_wall/inout_wall.sv.json"
#guard inoutWall.pdesign.decls.any (·.isInout)
#guard match inoutWall.pdesign.generates with
  | [.inst { conns := [.inout "pad" (some (.ident "pad")), _, _], .. }] => true
  | _ => false
#guard match inoutWall.pdesign.instantiate2 [] with
  | .unsupported msg => msg.contains "inout" && msg.contains "driver resolution"
  | _ => false
end Examples.«system-verilog».sem2.inout_wall.agree
