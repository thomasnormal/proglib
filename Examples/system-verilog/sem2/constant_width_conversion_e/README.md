# Runtime signed and width conversion

This source keeps integer constant arithmetic, a signed packed localparam, and
its runtime bit select source-shaped. Canonical E reads both parameter points
`E=8` and `E=4` without rewriting the expression. The checked rows include
0, 1, x, and z inputs and match Icarus Verilog 13.0 and Xcelium 24.03-s004.
