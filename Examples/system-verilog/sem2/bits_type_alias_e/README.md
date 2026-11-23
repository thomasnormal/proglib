# `$bits` type-alias canonical-E receipt

This clean-room source exercises IEEE 1800-2023 §20.7 `$bits` on a parser-native
package typedef. The alias is 12 bits wide, so the localparam and output are
`12`. Canonical E, Icarus Verilog 13.0, and Xcelium 24.03-s004 match the row.
