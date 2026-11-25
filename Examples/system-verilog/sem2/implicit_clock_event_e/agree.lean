import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.implicit_clock_event_e
open LeanModels.Sv
load_design_sv2 implicitClockEvent from
  "Examples/system-verilog/sem2/implicit_clock_event_e/implicit_clock_event_e.sv.json"
#guard match implicitClockEvent.pdesign.processes with
  | [.alwaysEvent [{ signal := "clk", edge := .any }] _] => true
  | _ => false
#guard match implicitClockEvent.e with | .ok _ => true | _ => false
end Examples.«system-verilog».sem2.implicit_clock_event_e
