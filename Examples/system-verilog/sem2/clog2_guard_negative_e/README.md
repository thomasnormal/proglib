# Unsigned negative `$clog2` in a generate guard

IEEE 1800-2023 §20.8.1 reads the `$clog2` argument as unsigned. The
`evalGenGuard32` fallback therefore evaluates a signed 32-bit `N = -1` as the
32-bit pattern `2^32 - 1`, so `$clog2(N)` is 32. The bitwise guard selects the
same branch as Icarus Verilog 13.0 and Xcelium 24.03-s004; `N = 0` exercises
the other branch.
