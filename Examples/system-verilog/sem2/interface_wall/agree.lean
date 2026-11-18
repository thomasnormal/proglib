/-
Canonical-E admission receipt for IEEE 1800-2023 §§23.2.2 and 23.3.
Interface instances and their port connections remain parser-native loud
boundaries. The assignment to an interface member is retained separately.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.interface_wall.agree

open LeanModels.Sv

load_design_sv2 interfaceWall
  from "Examples/system-verilog/sem2/interface_wall/interface_wall.sv.json"

#guard match interfaceWall.pdesign.processes with
  | [.unsupported "AssignmentExpression:target" "bus.request = value"] => true
  | _ => false

#guard match interfaceWall.pdesign.generates with
  | [.unsupported "InstanceSymbol:interface" "bus(clock)",
      .inst i] => i.name == "child"
  | _ => false

#guard match interfaceWall.pdesign.generates with
  | [_, .inst { conns := [.unsupported "" "PortConnection:InterfacePortSymbol" "bus", _], .. }] => true
  | _ => false

private def flat : Design2 := interfaceWall.pdesign.instantiateD2 []

#guard match flat.processes.toList with
  | [.unsupported "AssignmentExpression:target" _,
      .unsupported "InstanceSymbol:interface" _,
      .unsupported "Instance" _] => true
  | _ => false

end Examples.«system-verilog».sem2.interface_wall.agree
