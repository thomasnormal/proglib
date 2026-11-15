import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-!
Canonical-E receipt for IEEE 1800-2023 §§7.4.6 and 11.5.1.  The generated
assignment `state[i][0]` is retained as a packed `BitSel` over an unpacked
`ArraySel`; E evaluates both parser nodes directly, without flattening or
unrolling the source.
-/
namespace Examples.«system-verilog».sem2.generated_array_nested_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 generatedArrayNestedCanonicalE from
  "Examples/system-verilog/sem2/generated_array_nested_canonical_e/generated_array_nested_canonical_e.sv.json"

def stimuli4 : List SvState := [
  [],
  [("x", LVec.ofNat 4 0), ("taps", LVec.ofNat 4 0)],
  [("x", LVec.ofNat 4 5), ("taps", LVec.ofNat 4 0xc)],
  [("x", LVec.lit "xxxx"), ("taps", LVec.ofNat 4 1)],
  [("x", LVec.ofNat 4 6), ("taps", LVec.lit "xxxx")],
  [("x", LVec.lit "zzzz"), ("taps", LVec.ofNat 4 3)],
  [("x", LVec.ofNat 4 9), ("taps", LVec.lit "zzzz")],
  [("x", LVec.ofNat 4 15), ("taps", LVec.ofNat 4 1)]
]

def stimuli8 : List SvState := [
  [],
  [("x", LVec.ofNat 8 0), ("taps", LVec.ofNat 8 0)],
  [("x", LVec.ofNat 8 0xa5), ("taps", LVec.ofNat 8 0x3c)],
  [("x", LVec.lit "xxxxxxxx"), ("taps", LVec.ofNat 8 1)],
  [("x", LVec.ofNat 8 0x12), ("taps", LVec.lit "xxxxxxxx")],
  [("x", LVec.lit "zzzzzzzz"), ("taps", LVec.ofNat 8 3)],
  [("x", LVec.ofNat 8 0x81), ("taps", LVec.lit "zzzzzzzz")],
  [("x", LVec.ofNat 8 0xff), ("taps", LVec.ofNat 8 1)]
]

def outputs (w : Nat) (stimuli : List SvState) : Res (List String) := do
  let d ← generatedArrayNestedCanonicalE.e w
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#guard match generatedArrayNestedCanonicalE.e 4 with
  | .ok d => d.memories.size == 2 && d.processes.size == 25
  | _ => false
#guard match generatedArrayNestedCanonicalE.e 8 with
  | .ok d => d.memories.size == 2 && d.processes.size == 25
  | _ => false

#guard match outputs 4 stimuli4 with
  | .ok ["xxxxxxxx", "00000000", "00111101", "xxxxxxxx", "xxxxxx10",
      "xxxxxxxz", "xxxxxxx1", "00000101"] => true
  | _ => false
#guard match outputs 8 stimuli8 with
  | .ok ["xxxxxxxx", "00000000", "01111101", "xxxxxxxx", "xxxxxx10",
      "xxxxxxxz", "xxxxxxx1", "01010101"] => true
  | _ => false

end Examples.«system-verilog».sem2.generated_array_nested_canonical_e
