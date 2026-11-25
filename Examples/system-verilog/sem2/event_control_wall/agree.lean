/-
Canonical-E admission receipt for an explicit event-list process under IEEE
1800-2023 §§9.2 and 9.4. The source event control remains a loud boundary.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.event_control_wall.agree

open LeanModels.Sv

load_design_sv2 eventControlWall
  from "Examples/system-verilog/sem2/event_control_wall/event_control_wall.sv.json"

#guard match eventControlWall.pdesign.processes with
  | [.alwaysEvent [{ signal := "en", edge := .any }] _] => true
  | _ => false

#guard match eventControlWall.sem.processes.toList with
  | [.unsupported "ProceduralBlockSymbol:Always"
      "source-level event-controlled always is retained; the frozen process AST has no event-list constructor"] => true
  | _ => false

#guard eventControlWall.pdesign.generates == []
#guard eventControlWall.pdesign.others == []

end Examples.«system-verilog».sem2.event_control_wall.agree
