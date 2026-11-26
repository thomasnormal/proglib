# Wide package constants are evaluated at their declared width

These two parser-native rows pin package constants wider than 32 bits under
IEEE 1800-2023 §§6.20.2, 11.6 and 11.8: `rec::P`, the 64-bit result of a
constant function, and `rec::Q`, a 64-bit expression. Both were once computed
at 32 bits (the module then read `rec::P[63:32]` as 0), and were then refused
outright. The constant evaluator now evaluates both at 64 bits, and the
loader compares each bound package constant with the parser's own value.

Xcelium 26.09-s001 reports `rec::P[63:32] = 7` and `rec::Q[63:32] = 7`.
Icarus Verilog 13.0 reports the same values for the unchanged sources.
`agree.lean` pins the 64-bit values and the instantiated `assign o = 32'd7`.
