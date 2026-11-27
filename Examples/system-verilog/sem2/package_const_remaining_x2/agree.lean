import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.package_const_remaining_x2

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 x2 from
  "Examples/system-verilog/sem2/package_const_remaining_x2/x2_pkg_array.sv.json"

#guard match x2.e with
  | .ok d => d.env.nvals.lookup "K" == some (7, 32, false)
  | _ => false

def stimulus : List SvState :=
  [[("i", LVec.ofNat 8 0)], [("i", LVec.ofNat 8 255)],
   [("i", LVec.lit "xxxxxxxx")], [("i", LVec.lit "zzzzzzzz")]]

def outputs : Res (List String) := do
  let d ← x2.e
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "o")

#guard outputs == .ok ["00000111", "00000110", "xxxxxxxx", "xxxxxxxx"]

/- Icarus Verilog 13.0 and Xcelium 26.09-s001 both report these four
   rows on the unchanged source: 00000111, 00000110, xxxxxxxx, xxxxxxxx. -/

end Examples.«system-verilog».sem2.package_const_remaining_x2
