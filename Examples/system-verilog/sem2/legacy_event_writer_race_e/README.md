# Legacy event writer race

This clean-room source uses `always @(ar or b or en)` as a multi-write
reactive writer. Its intermediate value can be sampled by a flop on a divided
clock in the same update batch. Canonical E now classifies legacy explicit-list
writers as reactive and refuses the source-shaped schedule with
`Schedule:preemptive` under IEEE 1800-2023 §§4.6 and 4.7.

Icarus Verilog 13.0 and Xcelium Verilog 24.03-s004 agree on the eight receipt
rows `x x`, `x 0`, `x 0`, `0 1`, `0 1`, `0 0`, `0 0`, and `0 1`.
