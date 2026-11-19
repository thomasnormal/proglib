# Timing control in always_latch

This source-shaped fixture exercises IEEE 1800-2023 §9.2.2.4. A blocking
`#1` delay suspends an `always_latch` process, so canonical E refuses the
parser-native timing error instead of assigning a zero-delay meaning.

Icarus Verilog 13.0 and Xcelium 24.03-s004 both reject the source during
elaboration with their always-latch timing-control diagnostics.
