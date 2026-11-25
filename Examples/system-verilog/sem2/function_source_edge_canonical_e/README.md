# Source-shaped edge function wall

This clean-room fixture keeps an automatic input-only function as a parser
`Function` declaration and `FunctionCall` expression in an edge-triggered
body.  The ordinary E route evaluates that retained source call directly,
with the function formals as a local value environment.  The envelope is
generated with the approved source-preserving command:

```text
python3 extractors/sv/extract.py --retain-proc-rewrites \
  --top function_source_edge_canonical_e \
  -o Examples/system-verilog/sem2/function_source_edge_canonical_e/function_source_edge_canonical_e.sv.json \
  Examples/system-verilog/sem2/function_source_edge_canonical_e/function_source_edge_canonical_e.sv
```

The evaluator admits automatic functions whose formals are input-only; static
functions and output/ref/inout formals remain named refusals.  Icarus Verilog
13.0 and Xcelium 24.03-s004 both execute the eight source rows, including the
first uninitialized sample and `0`, `1`, `x`, and `z` function operands:
`q=x,1,1,x,x,x,x,0`.

The current wall-table `automatic_function_subroutine` row is the same
parser-shaped function and edge-call family; its eight seeded ordinary E rows
also match both pinned simulators.

The checker also records the default extractor route. It keeps the call's
source location and marks the existing inline representation explicitly. The
`--retain-proc-rewrites` envelope used by the E receipt retains the parser
`FunctionCall` node, so the two front-end modes cannot silently be conflated.

The current receipt confirms eight matching source rows on both pinned
simulators and the ordinary source-call boundary.
