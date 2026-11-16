# Inout resolved-net wall

This source exercises IEEE 1800-2023 §6.6 bidirectional net resolution and
§23.2.2 inout port connections. The ordinary census retains exact
`PortSymbol:InOut`, `PortConnection:InOut`, and canonical-E boundaries.
Canonical E has no driver-set/resolution relation, so the wall stays loud; no
scalar alias or x/z approximation is used. Icarus Verilog 13.0 and Xcelium
24.03-s004 match the known, z, and conflicting-driver rows.
