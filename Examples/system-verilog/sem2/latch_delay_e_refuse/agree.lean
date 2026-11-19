import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.latch_delay_e_refuse
open LeanModels.Sv
load_design_sv2 latchDelay
  from "Examples/system-verilog/sem2/latch_delay_e_refuse/latch_delay_e.sv.json"
#guard latchDelay.pdesign.processes.length == 1
#guard match latchDelay.pdesign.processes[0]! with
  | .alwaysLatch (.unsupported "InvalidStatement" _) => true
  | _ => false
#guard latchDelay.pdesign.others == [("SlangError:TimingInFuncNotAllowed", "latch_delay_e.sv:4: statements that pass time are not allowed in this context")]
end Examples.«system-verilog».sem2.latch_delay_e_refuse
