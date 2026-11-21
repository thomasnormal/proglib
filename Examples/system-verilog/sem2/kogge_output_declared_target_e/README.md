# Packed output bit-select targets

This source-shaped receipt covers continuous assignments to packed output bit-selects retained by Slang as `ArraySel` nodes. Canonical E dispatches a scalar declaration through its existing four-state bit-write semantics. The fixture covers a direct bit-select and a generated bit-select at `WIDTH=4`.

The four rows include known, unknown, and high-impedance input values and match Icarus Verilog 13.0 and Xcelium 24.03-s004.
