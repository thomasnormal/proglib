import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.clocked_param_loop_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 loop from "Examples/system-verilog/sem2/clocked_param_loop_e/clocked_param_loop_e.sv.json"
#guard match loop.sem 4 3 with | .ok _ => true | _ => false
#guard match loop.e 4 3 with | .ok d => d.processes.size == 2 | _ => false
#guard match PDesign.instantiateE2 loop.pdesign [4, 3] with | .ok d => d.memories.size == 1 | _ => false
end Examples.«system-verilog».sem2.clocked_param_loop_e.agree
