import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.initial_const_fatal_refuse
open LeanModels.Sv
load_design_sv2 initialConstFatal
  from "Examples/system-verilog/sem2/initial_const_fatal_refuse/initial_const_fatal.sv.json"
#guard initialConstFatal.pdesign.processes.length == 2
#guard initialConstFatal.pdesign.others == []
#guard initialConstFatal.pdesign.processes.any fun p =>
  match p with
  | .initial (.block [.ifStmt _ (.unsupported "SysCall:$fatal" _) none]) => true
  | _ => false
end Examples.«system-verilog».sem2.initial_const_fatal_refuse
