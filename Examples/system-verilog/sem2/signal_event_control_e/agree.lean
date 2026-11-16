import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.signal_event_control_e
open LeanModels.Sv
load_design_sv2 signalEventControl from
  "Examples/system-verilog/sem2/signal_event_control_e/signal_event_control_e.sv.json"
#guard match signalEventControl.pdesign.processes with
  | [.unsupported "Clock:implicit" _] => true
  | _ => false
end Examples.«system-verilog».sem2.signal_event_control_e
