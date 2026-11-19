# Inout resolved-net wall

This source exercises IEEE 1800-2023 §6.6 bidirectional net resolution and
§23.2.2 inout port connections. The symbolic envelope retains the parser's
`inout` direction and the child connection as source-shaped nodes. The kernel
now has an `InoutNet` driver relation and resolves sampled equal-strength
four-state contributions through the shared resolver. Canonical E still
refuses hierarchy integration because its scalar store has no source-shaped
inout connection route. No scalar alias or x/z approximation is used. Icarus
Verilog 13.0 and Xcelium 24.03-s004 match the known, z, and conflicting-driver
rows.
