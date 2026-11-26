/-
Canonical-E receipt for a source-shaped event-controlled process nested in a
single generate-for instance.  The generate expansion preserves the event
list and nonblocking body without lowering the source node.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.event_generated_wall.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 eventGeneratedWall
  from "Examples/system-verilog/sem2/event_generated_wall/event_generated_wall.sv.json"

#guard match eventGeneratedWall.e with
  | .ok d =>
      match d.processes.toList with
      | [.event [{ signal := "clk", edge := .posedge }] (.nbaAssign "q" (.ident "d"))] => true
      | _ => false
  | _ => false

#guard match eventGeneratedWall.e with
  | .ok d => d.processes.toList.length == 1
  | _ => false

end Examples.«system-verilog».sem2.event_generated_wall.agree
