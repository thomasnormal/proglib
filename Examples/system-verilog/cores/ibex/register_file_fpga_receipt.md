# Ibex FPGA register-file ordinary-route receipt

The pinned Ibex `ibex_register_file_fpga.sv` source was extracted with its
actual `ibex_pkg.sv`, `ibex_cheriot_pkg.sv`, and `prim_assert.sv` dependencies
using Slang. Its source-shaped envelope loaded through `load_design_sv2` and
reported the expected parameterized `Design` family.

Icarus Verilog 13.0 rejects the unchanged module header at line 39, so no
Icarus oracle result is claimed. Xcelium 24.03-s004 runs the unchanged source
for the initial unknown row, a write/read row, the zero-register row, and the
x/z address row. The output agrees with the ordinary-route receipt for those
rows. The pinned source is external to this repository and is selected with
`IBEX_ROOT` in the lane journal.
