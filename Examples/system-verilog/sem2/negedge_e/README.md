# Canonical E negative-edge clock

This source-shaped B1 fixture retains `always_ff @(negedge clk)` as a canonical-E edge with IEEE 1800-2023 §9.4.2 negative-edge semantics. The ordinary run2 bridge remains a loud `Clock:edge` boundary. Eight source rows, including x/z clock values, match Icarus Verilog 13.0 and Xcelium 24.03-s004.
