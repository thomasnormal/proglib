# Direct declarations in a `generate for`

This parser-native fixture exercises IEEE 1800-2023 §27.4. A declaration made
inside a `generate for` body has one hierarchical object in each elaborated
generate scope. The source has one `logic t` declaration, and the two instances
must therefore expose `g[0].t` and `g[1].t` independently.

The extractor keeps the declaration and its references source-shaped with a
`$genvar` marker. Canonical E substitutes the active generate binding while
expanding the design. The Lean receipt checks both declaration names and all
four assignment processes for `N = 2`.

`check.py` regenerates the envelope and runs five rows through Icarus Verilog
13.0 and Xcelium Verilog 24.03-s004. Both report the identity mapping,
including x and z values.
