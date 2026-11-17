import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.backreg_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 backregE from
  "Examples/system-verilog/sem2/backreg_e/backreg_e.sv.json"

/-! Scalar continuous assignments use the scalar quiescence executor.  The
memory-cell topology refusal is checked separately after generate expansion;
this scalar chain therefore has an admitted canonical-E design. -/
#guard match backregE.e with
  | .ok _ => true
  | _ => false
end Examples.«system-verilog».sem2.backreg_e
