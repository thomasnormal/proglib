import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.generated_instance_timeout_e
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 generatedInstance from
  "Examples/system-verilog/sem2/generated_instance_timeout_e/generated_instance_timeout_e.sv.json"

def stimulus : List SvState :=
  [[("clk", LVec.ofLogic .l0), ("rstn", LVec.ofLogic .l0), ("d", LVec.ofLogic .l0)],
   [("clk", LVec.ofLogic .l1), ("rstn", LVec.ofLogic .l1), ("d", LVec.ofLogic .l1)],
   [("clk", LVec.ofLogic .l0), ("rstn", LVec.ofLogic .l1), ("d", LVec.ofLogic .l0)],
   [("clk", LVec.ofLogic .l1), ("rstn", LVec.ofLogic .l1), ("d", LVec.ofLogic .l0)]]

def outputs : Res (List String) := do
  let d ← generatedInstance.e 1
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard generatedInstance.pdesign.others == []
#guard match generatedInstance.e 1 with | .ok _ => true | _ => false
#guard outputs == .ok ["0", "0", "0", "1"]

end Examples.«system-verilog».sem2.generated_instance_timeout_e
