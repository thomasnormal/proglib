# Level-event/reactive activation wall

This clean-room source has a level-sensitive `always @(a or b or en)` reader
of `nxt` beside an `always_comb` writer of `nxt`. The same input update wakes
the reader and the writer, so IEEE 1800-2023 §§9.2.2.2 and 9.4.2 leave their
activation order open. Canonical E refuses the source-shaped design with
`Schedule:level-event` instead of choosing one result.

The simulator receipt has five rows. Icarus Verilog 13.0 and Xcelium
24.03-s004 both produce `x`, `0`, `0`, `0`, `0`.
