import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.package_signed_member_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 unsignedMember from
  "Examples/system-verilog/sem2/package_signed_member_canonical_e/package_unsigned_member_canonical_e.sv.json"

def unsignedOutputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem unsignedMember.pdesign [0]
  let s ← d.step d.initial [("i", LVec.ofNat 8 1)]
  let d' ← PDesign.instantiateCoreMem unsignedMember.pdesign [1]
  let s' ← d'.step d'.initial [("i", LVec.ofNat 8 1)]
  .ok [SvState.showSignal (CoreMemState.view d s) "o",
       SvState.showSignal (CoreMemState.view d' s') "o"]

#guard match unsignedMember.e 0 with
  | .ok _ => true
  | _ => false
#guard unsignedOutputs == .ok ["00000000000000000000000000000100", "00000000000000000000000000000110"]
#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.package_signed_member_canonical_e
