import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.prefix_adder_unpacked_refuse_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 prefixAdder from "Examples/system-verilog/sem2/prefix_adder_unpacked_refuse_e/prefix_adder_unpacked_refuse_e.sv.json"
def outputs : Res (List String) := do
 let d ← prefixAdder.e 4
 let rs ← runCoreMemRows d d.initial [[("a",LVec.ofNat 4 0)],[ ("a",LVec.ofNat 4 3) ],[("a",LVec.xVec 4)],[("a",LVec.lit "zzzz")]]
 .ok (rs.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["0000","0011","xxxx","zzzz"]
end Examples.«system-verilog».sem2.prefix_adder_unpacked_refuse_e
