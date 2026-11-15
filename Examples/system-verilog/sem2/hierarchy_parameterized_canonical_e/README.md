# Parameterized packed-port hierarchy canonical-E receipt

The parent connects two parameterized child outputs into packed slices of `y`.
The canonical E hierarchy path now applies those source-shaped part-select
writes with IEEE 1800-2023 §23.3.3 port-connection timing and preserves
four-state values. Five rows match Icarus Verilog 13.0 and Xcelium
`xrun(64)` 24.03-s004: `00000000`, `00000001`, `10100101`, `11110000`, and
`xxxxxxxx`.
