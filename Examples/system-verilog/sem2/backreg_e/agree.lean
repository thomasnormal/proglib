import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.backreg_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 backregE from
  "Examples/system-verilog/sem2/backreg_e/backreg_e.sv.json"

/-! The source-shaped three-deep continuous-assignment chain is deliberately
refused.  The one-pass route cannot claim IEEE 1800-2023 §§4.5 and 10.3 for a
later-target dependency, so no E value is reported for this fixture. -/
#guard match backregE.e with
  | .unsupported msg => msg ==
      "10.3: continuous assignment target is read from itself or a later assignment; canonical E requires topological source order"
  | _ => false
end Examples.«system-verilog».sem2.backreg_e
