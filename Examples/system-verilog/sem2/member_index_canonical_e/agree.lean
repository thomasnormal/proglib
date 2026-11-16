import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-!
Canonical-E receipt for a generated packed-member element index under IEEE
1800-2023 §11.5.1.  The parser-shaped `state.out_dis[i]` is retained as a
member bit select with its genvar bound; ingestion does not flatten or unroll
that source node.
-/
namespace Examples.«system-verilog».sem2.member_index_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memberIndexCanonicalE from
  "Examples/system-verilog/sem2/member_index_canonical_e/member_index_canonical_e.sv.json"

def stimuli : List SvState := [
  [],
  [("bits", LVec.ofNat 4 0)],
  [("bits", LVec.ofNat 4 1)],
  [("bits", LVec.ofNat 4 8)],
  [("bits", LVec.lit "xxxx")],
  [("bits", LVec.lit "zzzz")],
  [("bits", LVec.ofNat 4 15)]
]

def outputs : Res (List String) := do
  let d ← memberIndexCanonicalE.e
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "result")

#guard match memberIndexCanonicalE.e with
  | .ok d => d.memories.size == 0 && d.processes.size == 2
  | _ => false

#guard match outputs with
  | .ok ["x", "0", "1", "0", "x", "z", "1"] => true
  | _ => false

end Examples.«system-verilog».sem2.member_index_canonical_e
