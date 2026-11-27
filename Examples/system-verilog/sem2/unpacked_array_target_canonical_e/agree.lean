import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.unpacked_array_target_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 unpackedArrayTarget from
  "Examples/system-verilog/sem2/unpacked_array_target_canonical_e/unpacked_array_target_canonical_e.sv.json"

/-! The source-shaped select is retained as `PLhs.arrayElem`; the executor
resolves its run-time index against the native one-rank `MemState` (§7.4.6,
§11.5.1, IEEE 1800-2023). -/
#guard unpackedArrayTarget.pdesign.processes.any fun p => match p with
  | .alwaysComb (.block (.blockingAssignL (.arrayElem "slot" [(.ident "idx")]) (.ident "x") ::
      .blockingAssign "y" (.arrayElem "slot" [(.ident "idx")]) :: [])) => true
  | _ => false

#guard match PDesign.instantiateCoreMem unpackedArrayTarget.pdesign [] with
  | .ok _ => true
  | _ => false

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem unpackedArrayTarget.pdesign []
  let states ← runCoreMemRows d d.initial [
    [("x", LVec.ofNat 8 90), ("idx", LVec.ofNat 1 0)],
    [("x", LVec.ofNat 8 165), ("idx", LVec.ofNat 1 1)],
    [("x", LVec.lit "xxxxxxxx"), ("idx", LVec.lit "x")]]
  .ok (states.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

end Examples.«system-verilog».sem2.unpacked_array_target_canonical_e
