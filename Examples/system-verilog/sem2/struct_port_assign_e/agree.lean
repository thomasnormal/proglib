import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.struct_port_assign_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 structPortAssign from
  "Examples/system-verilog/sem2/struct_port_assign_e/struct_port_assign_e.sv.json"
private def stimuli : List SvState :=
  [[("instr_i", LVec.ofNat 4 0), ("valid_i", LVec.ofNat 1 0), ("tag_i", LVec.ofNat 2 0)],
   [("instr_i", LVec.ofNat 4 10), ("valid_i", LVec.ofNat 1 1), ("tag_i", LVec.ofNat 2 1)],
   [("instr_i", LVec.xVec 4), ("valid_i", LVec.lit "z"), ("tag_i", LVec.lit "xz")]]
def outputs : Res (List String) := do
  let d ← structPortAssign.e
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["0000000", "1010101", "xxxxzxz"]
end Examples.«system-verilog».sem2.struct_port_assign_e
