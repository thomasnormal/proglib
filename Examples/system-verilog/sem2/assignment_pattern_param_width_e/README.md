# Parameter-dependent default assignment pattern

This source-shaped IEEE 1800-2023 §10.9 pattern repeats its scalar `default:`
value across the packed parameter width. The canonical E receipt checks W=2 and
W=4. Icarus Verilog 13.0 and Xcelium 24.03-s004 are the pinned simulator
oracles for the same rows.
