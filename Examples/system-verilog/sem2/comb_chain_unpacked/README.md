# Genvar-indexed unpacked-array chain

This fixture exercises a forward continuous chain `s[0]`, `s[i+1] = s[i] >>
1` beside an edge process under IEEE 1800-2023 §§7.4.6, 10.3, and 27.4.
Parser-native generated indices are retained, and canonical E admits the
constant-index dependency order. Icarus Verilog 13.0 and Xcelium 24.03-s004
match four rows.

This receipt covers the `genvar_unpacked_chain` wall. The current ordinary
route admits the distinct constant cells in source order.
