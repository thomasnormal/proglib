# Module-level integer loop-variable receipt

The parser-native module-level `integer i` used by a procedural `for` loop is
retained in the source-shaped declaration surface under IEEE 1800-2023
§6.11. The ordinary route runs the generated nonblocking writes at `N=2`.
The current receipt reports four matching rows on Icarus Verilog 13.0 and
Xcelium 24.03-s004.
