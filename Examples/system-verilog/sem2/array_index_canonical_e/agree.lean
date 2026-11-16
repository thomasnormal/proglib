import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-!
Canonical-E receipt for the source-shaped unpacked-array element read in
IEEE 1800-2023 §11.5.1.  The fixed unpacked dimension is retained as an
`ArraySel` node and E evaluates the member index directly; no flattening or
source rewrite is used.
-/
namespace Examples.«system-verilog».sem2.array_index_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 arrayIndexCanonicalE from
  "Examples/system-verilog/sem2/array_index_canonical_e/array_index_canonical_e.sv.json"

def stimuli : List SvState := [
  [],
  [("i", LVec.ofNat 2 0)],
  [("i", LVec.ofNat 2 1)],
  [("i", LVec.ofNat 2 2)],
  [("i", LVec.ofNat 2 3)],
  [("i", LVec.lit "xx")],
  [("i", LVec.lit "zz")],
  [("i", LVec.ofNat 2 0)]
]

def outputs : Res (List String) := do
  let d ← arrayIndexCanonicalE.e
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#guard match arrayIndexCanonicalE.e with
  | .ok d => d.memories.size == 0 && d.processes.size == 1
  | _ => false

#guard match outputs with
  | .ok ["xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx", "xxxxxxxx",
      "xxxxxxxx", "xxxxxxxx", "xxxxxxxx"] => true
  | _ => false

end Examples.«system-verilog».sem2.array_index_canonical_e
