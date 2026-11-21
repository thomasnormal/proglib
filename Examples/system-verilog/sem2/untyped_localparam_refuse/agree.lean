import LeanModels.Sv.Ingest2
/-!
IEEE 1800-2023 §6.20.2 gives each untyped parameter and localparam the
self-determined type and range of its final value.  Xcelium 24.03-s004 agrees
with this exact constant evaluation.  Icarus Verilog 13.0 has a declared
lossless-width departure in the differential row.
-/
namespace Examples.«system-verilog».sem2.untyped_localparam_exact.agree
open LeanModels.Sv
load_design_sv2 untyped_localparam_refuse from
  "Examples/system-verilog/sem2/untyped_localparam_refuse/untyped_localparam_refuse.sv.json"
#guard !(untyped_localparam_refuse.sem 10000).hasUnsupported
#guard !(untyped_localparam_refuse.sem 8).hasUnsupported
end Examples.«system-verilog».sem2.untyped_localparam_exact.agree
