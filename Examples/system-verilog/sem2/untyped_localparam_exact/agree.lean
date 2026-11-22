import LeanModels.Sv.Ingest2
/-!
IEEE 1800-2023 §6.20.2 gives each untyped parameter and localparam the
self-determined type and range of its final value. Xcelium 24.03-s004 agrees
with this exact constant evaluation. Icarus Verilog 13.0 has a declared
lossless-width departure for the width-observed `WIDE` concatenation row.
-/
namespace Examples.«system-verilog».sem2.untyped_localparam_exact.agree
open LeanModels.Sv
load_design_sv2 untyped_localparam_exact
  from "Examples/system-verilog/sem2/untyped_localparam_exact/untyped_localparam_exact.sv.json"
#guard !(untyped_localparam_exact.sem 10000).hasUnsupported
#guard !(untyped_localparam_exact.sem 8).hasUnsupported
end Examples.«system-verilog».sem2.untyped_localparam_exact.agree
