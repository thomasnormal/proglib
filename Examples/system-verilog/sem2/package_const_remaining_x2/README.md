# Unpacked package array read in a constant function

The constant function `last` reads `tab::ROM[n]`, an unpacked package array
parameter, under IEEE 1800-2023 §§7.4.2, 7.4.6, and 13.4.3. The ordinary
loader evaluates `K = 7` and the receipt checks four-state rows. Icarus
Verilog 13.0 and Xcelium 26.09-s001 both report `00000111`, `00000110`,
`xxxxxxxx`, and `xxxxxxxx` for the unchanged source.
