import LeanModels.Sv.ClockGuard2
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.loader_accept_areset.agree
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 activeHigh from
  "Examples/system-verilog/sem2/loader_accept_areset/loader_accept_areset.sv.json"
#guard match activeHigh.e with | .ok _ => true | _ => false
#guard match activeHigh.e with
  | .ok d => d.processes.toList.any fun p => match p with
    | .edge e => e.resetHigh
    | _ => false
  | _ => false
end Examples.«system-verilog».sem2.loader_accept_areset.agree
