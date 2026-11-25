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

end Examples.«system-verilog».sem2.unpacked_array_target_canonical_e
