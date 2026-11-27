# Child parameter defaults and string forwarding

The parent forwards `WIDTH`, `ADDRESS_BITS`, `DEGREE`, and the untyped string
`ROM_STYLE` parameter to its coefficient child. The extractor retains the
string literal as parser metadata, while the loader forwards its packed value
through the hierarchical parameter binder. The child then elaborates its
parameter-sized declarations at the supplied values under IEEE 1800-2023
§6.20.2 and §23.3.

The agreement receipt checks the ordinary canonical-E route at
`WIDTH=8`, `ADDRESS_BITS=2`, `DEGREE=2`, and `ROM_STYLE="distributed"`.
Icarus Verilog 13.0 and Xcelium 24.03-s004 both report four matching rows.
The rows cover zero, a known value, x, and z input bits.
