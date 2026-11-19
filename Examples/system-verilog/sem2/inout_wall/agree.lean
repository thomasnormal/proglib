/-
Canonical-E admission receipt for IEEE 1800-2023 §§6.6 and 23.2.2 inout
ports. The parser-native bidirectional port and connection remain loud.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.inout_wall.agree

open LeanModels.Sv

load_design_sv2 inoutWall
  from "Examples/system-verilog/sem2/inout_wall/inout_wall.sv.json"

#guard inoutWall.pdesign.others == []
#guard match inoutWall.pdesign.generates with
  | [.inst { conns := [.inout "pad" (some (.ident "pad")), _, _], .. }] => true
  | _ => false

private def flat : Design2 := inoutWall.pdesign.instantiateD2 []

#guard match flat.processes.toList with
  | [.unsupported "Instantiate" _] => true
  | _ => false

end Examples.«system-verilog».sem2.inout_wall.agree
