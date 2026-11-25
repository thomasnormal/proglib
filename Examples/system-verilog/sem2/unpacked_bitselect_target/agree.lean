import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.unpacked_bitselect_target
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 unpackedBitTarget from "Examples/system-verilog/sem2/unpacked_bitselect_target/unpacked_bitselect_target.sv.json"
/-! Until 75a9b0468 canonical E refused this target and this file pinned the refusal. E now admits a generated
bit-select target of an unpacked element (`PLhs.arrayBitSel`), so the pin is the value E computes on the four rows of
`unpacked_bitselect_target_tb.sv`. No oracle result is claimed here: the simulators were not re-run for this pin. -/
def stimuli : List SvState :=
  [[("a", LVec.ofNat 4 0x0), ("b", LVec.ofNat 4 0x0)],
   [("a", LVec.ofNat 4 0xa), ("b", LVec.ofNat 4 0x3)],
   [("a", LVec.lit "xxxx"), ("b", LVec.ofNat 4 0x5)],
   [("a", LVec.lit "zzzz"), ("b", LVec.ofNat 4 0x5)]]
def outputs : Res (List String) := do
  let d ← unpackedBitTarget.e 4
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["0000", "1001", "xxxx", "xxxx"]
end Examples.«system-verilog».sem2.unpacked_bitselect_target
