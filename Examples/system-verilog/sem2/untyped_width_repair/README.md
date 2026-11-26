# Untyped override-dependent localparam refusal

This clean-room source exercises IEEE 1800-2023 §6.20.2. The localparam
`L` depends on an untyped parameter `P`, whose type changes when an integer
override is supplied. The constant evaluator refuses the derived expression
before it reaches a generate condition, so it cannot select a branch using the
default-point type at an overridden point.

Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on both source rows:
`P=8'h01` produces `default=00000010`, and `P=-2` produces
`override=00000001`. No E value is claimed because the source is intentionally
refused at the constant-context boundary.
