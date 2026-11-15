import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.net_generated_dynamic_output_port_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 netGeneratedDynamicOutput from
  "Examples/system-verilog/sem2/net_generated_dynamic_output_port_canonical_e/net_generated_dynamic_output_port_canonical_e.sv.json"
def stimuli : List SvState := [
  [("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)],
  [("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 1)],
  [("a", LVec.ofNat 1 1), ("b", LVec.ofNat 1 0)],
  [("a", LVec.ofNat 1 1), ("b", LVec.ofNat 1 1)]]
def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem netGeneratedDynamicOutput.pdesign [1]
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "wready_o")
#guard match PDesign.instantiateCoreMem netGeneratedDynamicOutput.pdesign [1] with
  | .ok d => d.scalar.decls.toList.any (fun x => x.name == "wready_o" && x.isNet && x.isOutput && x.init == some (LVec.replicate 1 .lz))
  | _ => false
#guard outputs == .ok ["1", "0", "0", "0"]
end Examples.«system-verilog».sem2.net_generated_dynamic_output_port_canonical_e
