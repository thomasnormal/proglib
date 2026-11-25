import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.wake_base_wrong_answer_e

load_design_sv2 wake from
  "Examples/system-verilog/sem2/wake_base_wrong_answer_e/wake_base_wrong_answer_e.sv.json"

#guard match wake.e with
  | .unsupported msg => msg == "Event:multiple-write: 4.3/10.4.1: blocking event source 'g' is written more than once in one process activation; intermediate update events are not modeled"
  | _ => false

end Examples.«system-verilog».sem2.wake_base_wrong_answer_e
