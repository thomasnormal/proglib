# `$bits` package-parameter canonical-E receipt

This clean-room source exercises IEEE 1800-2023 `$bits` on a typed package
parameter. The parameter is an 8-bit packed value, so the localparam width is
8 and the continuous output is `00001000`. The parser-native envelope loads in
canonical E and its one row matches Icarus Verilog 13.0 and Xcelium
`xrun(64)` 24.03-s004.
