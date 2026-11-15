# Unsigned negative `$clog2` canonical-E receipt

IEEE 1800-2023 §20.8.1 reads the `$clog2` argument as unsigned. For the
unsized signed `-1`, both pinned simulators therefore return 32; the 6-bit
output is `100000`. The parser-native envelope runs in canonical E and matches
Icarus Verilog 13.0 and Xcelium `xrun(64)` 24.03-s004.
