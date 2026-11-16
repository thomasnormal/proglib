import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-!
Canonical-E receipt for a generated packed-member range select under IEEE
1800-2023 §11.5.1.  The parser-shaped `state.value[i+1:i]` is retained with
its genvar bounds; ingestion does not flatten or unroll the source range.
-/
namespace Examples.«system-verilog».sem2.member_range_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memberRangeCanonicalE from
  "Examples/system-verilog/sem2/member_range_canonical_e/member_range_canonical_e.sv.json"

def stimuli : List SvState := [
  [],
  [("bits", LVec.ofNat 8 0)],
  [("bits", LVec.ofNat 8 3)],
  [("bits", LVec.ofNat 8 0xfc)],
  [("bits", LVec.lit "xxxxxxxx")],
  [("bits", LVec.lit "zzzzzzzz")],
  [("bits", LVec.ofNat 8 0xff)]
]

def outputs : Res (List String) := do
  let d ← memberRangeCanonicalE.e
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "result")

#guard match memberRangeCanonicalE.e with
  | .ok d => d.memories.size == 0 && d.processes.size == 2
  | _ => false

#guard match outputs with
  | .ok ["xx", "00", "11", "00", "xx", "zz", "11"] => true
  | _ => false

end Examples.«system-verilog».sem2.member_range_canonical_e
