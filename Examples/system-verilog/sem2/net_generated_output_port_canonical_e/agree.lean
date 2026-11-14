import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.net_generated_output_port_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 netGeneratedOutput from
  "Examples/system-verilog/sem2/net_generated_output_port_canonical_e/net_generated_output_port_canonical_e.sv.json"
def stimuli : List SvState := [[("clk", LVec.ofNat 1 0)], [("clk", LVec.ofNat 1 1)]]
def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem netGeneratedOutput.pdesign [1]
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "z_out")
-- A generated full-width driver turns the output net into a canonical E
-- declaration while preserving its §6.6 net startup value.
#guard match PDesign.instantiateCoreMem netGeneratedOutput.pdesign [1] with
  | .ok d => d.scalar.decls.toList.any (fun x => x.name == "z_out" && x.isNet && x.isOutput && x.init == some (LVec.replicate 1 .lz))
  | _ => false
#guard outputs == .ok ["0", "0"]
end Examples.«system-verilog».sem2.net_generated_output_port_canonical_e
