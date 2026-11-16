# Recursive canonical-E child instances

The faithful nested scan-chain source contains `child_instance_scan ->
scan_chain -> scan_leaf` and a generated two-stage child chain. Canonical E's
hierarchy merger now recursively expands parser-native child instances and
substitutes genvar-indexed port expressions before hoisting source-shaped
processes, under IEEE 1800-2023 §§23.3 and 23.3.3. The four-row receipt agrees
with Icarus Verilog 13.0, Xcelium 24.03-s004, and direct `instantiateE2H`:
`q=0,0,0,1`. The flat one-clock loader remains loud where its child library is
not used; this receipt exercises the canonical hierarchical E route.

The ordinary hierarchical census is now also zero refusals; the checker
asserts that regression result.
