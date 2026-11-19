# Runtime `$error` in an initial process

This source-shaped fixture isolates a runtime `$error` system task in an
`initial` process. Canonical E retains the parser-native system-task boundary
and refuses it rather than assigning runtime diagnostic behavior to the
zero-delay tier. The continuous assignment remains an ordinary E process.

Icarus Verilog 13.0 and Xcelium 24.03-s004 both emit the expected diagnostic
and preserve the four-state continuous output rows.
