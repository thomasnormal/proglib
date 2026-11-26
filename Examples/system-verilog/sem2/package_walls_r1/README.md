# Scoped package width port regression

This parser-native row keeps the package-qualified width expression on both
ANSI ports, `logic [cfg::W-1:0]`, while resolving the type syntax from the
port header itself. The package name inside the packed dimension is an
expression reference, not a typedef name. IEEE 1800-2023 §§6.11 and 23.2.2
therefore give both ports width 6.

The ordinary `load_design_sv2` receipt checks the retained package default.
Xcelium 26.09-s001 reports `bits(i)=6 bits(o)=6` with matching `101010` and
`1x0z10` pass-through rows. Icarus Verilog 13.0 reports the same values.
