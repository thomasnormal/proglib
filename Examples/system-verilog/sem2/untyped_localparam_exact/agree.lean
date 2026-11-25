import LeanModels.Sv.Ingest2
/-!
IEEE 1800-2023 §6.20.2 gives each untyped parameter and localparam the
self-determined type and range of its final value. Xcelium 24.03-s004 agrees
with this exact constant evaluation. The public admission remains a loud
`Constant:untyped-width` refusal until the exact evaluator has passed the
independent audit, while the receipt's simulator rows retain the measured
Icarus lossless-width departure for `WIDE`.
-/
namespace Examples.«system-verilog».sem2.untyped_localparam_exact.agree
open LeanModels.Sv
/--
error: load_design_sv2: 'Examples/system-verilog/sem2/untyped_localparam_exact/untyped_localparam_exact.sv.json' REFUSED — our defaults elaboration disagrees with the envelope's `resolved` metadata (Lean vs slang differential):
  localparam 'K': Constant:untyped-width — an untyped parameter or localparam takes its expression's own type (IEEE 1800-2023 §6.20.2; slang, Yosys 0.53), while Icarus 12.0 gives it the lossless width of an expression built with + - * or ** ($bits of `SB + 1'b1` with an 8-bit SB is 9, of `N + 1` with an int N 33): the two are different constants wherever the width is observable (a concatenation part, a negative value extended into a wider unsigned context, a context it widens) — refused for every such untyped constant, at every point
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 untyped_localparam_exact
  from "Examples/system-verilog/sem2/untyped_localparam_exact/untyped_localparam_exact.sv.json"
end Examples.«system-verilog».sem2.untyped_localparam_exact.agree
