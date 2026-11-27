# Packed-dimension cross-check

The child declares two ANSI inputs in one parameterized packed dimension.
The ordinary loader preserves the declaring-scope expression
`EXPONENT+FRACTION:0` for both inputs at `EXPONENT=8`, `FRACTION=23`, and
retains the 32-bit result declaration. This follows IEEE 1800-2023 §§6.8 and
23.2.2. The receipt runs canonical E and checks the initial x result followed
by `a ^ b = 32'hff`. Icarus Verilog 13.0 and Xcelium 24.03-s004 each match the
simulator row.
