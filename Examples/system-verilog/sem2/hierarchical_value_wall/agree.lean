/-
Canonical-E admission receipt for the hierarchical value expression in IEEE
1800-2023 §23.6. The child-instance path remains parser-shaped and loud.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.hierarchical_value_wall.agree

open LeanModels.Sv

load_design_sv2 hierarchicalValueWall
  from "Examples/system-verilog/sem2/hierarchical_value_wall/hierarchical_value_wall.sv.json"

#guard match hierarchicalValueWall.pdesign.processes with
  | [.assign "result"
      (.unsupported "HierarchicalValueExpression" "u.internal_value")] => true
  | _ => false

#guard hierarchicalValueWall.pdesign.others == []

end Examples.«system-verilog».sem2.hierarchical_value_wall.agree
