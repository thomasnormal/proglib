import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.resolved_net_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 resolvedNet from
  "Examples/system-verilog/sem2/resolved_net_canonical_e/resolved_net_canonical_e.sv.json"
#guard resolvedNet.pdesign.netMetadata.any (fun md =>
  md.name == "y" && md.driverRecords.length == 2 &&
    md.driverReason == some "two drivers on a bit")
#guard match PDesign.instantiateCoreMem resolvedNet.pdesign [] with
  | .ok d => d.resolvedNets == ["y"]
  | _ => false
def stimuli : List SvState :=
  [[("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)],
   [("a", LVec.ofNat 1 1), ("b", LVec.ofNat 1 1)],
   [("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 1)],
   [("a", LVec.ofLogic .lx), ("b", LVec.ofLogic .lz)]]
#guard match PDesign.instantiateCoreMem resolvedNet.pdesign [] with
  | .ok d => match runCoreMemRows d d.initial stimuli with
      | .ok rows => rows.map (fun st => SvState.showSignal (CoreMemState.view d st) "y") ==
          ["0", "1", "x", "x"]
      | _ => false
  | _ => false
end Examples.«system-verilog».sem2.resolved_net_canonical_e
