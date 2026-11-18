# Inout resolved-net wall

This source exercises IEEE 1800-2023 §6.6 bidirectional net resolution and
§23.2.2 inout port connections. The symbolic envelope retains the parser's
`inout` direction and the child connection as source-shaped nodes. Canonical
E still refuses the declaration because its scalar store has no driver-set
resolution relation. No scalar alias or x/z approximation is used. Icarus
Verilog 13.0 and Xcelium 24.03-s004 match the known, z, and conflicting-driver
rows.
