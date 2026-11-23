# Ibex flip-flop register-file ordinary-route receipt

This receipt measures the pinned Ibex `ibex_register_file_ff.sv` source as a
bounded real subdesign. The approved Slang extractor was run over
`ibex_cheriot_pkg.sv`, `ibex_pkg.sv`, `prim_assert.sv`, and the register-file
source, with `ibex_register_file_ff` selected as the top. The resulting
source-shaped envelope loaded through `load_design_sv2` and `#check` succeeded.

The source simulator command used Icarus Verilog 13.0. Its frontend rejects
the unchanged module header at line 38 (`module ... import ibex_pkg::*;`), so
no Icarus oracle result is claimed for this source. Xcelium 24.03-s004 loaded
the same unchanged source and ran the stimulus. It reported the initial
unknown register reads, the written `a5a55a5a` value, the zero register value,
and the x/z address row without a semantic mismatch.

The source is pinned outside this repository. Reproduce the measurement with
`IBEX_ROOT` set to the pinned checkout and the ordinary extractor command
shown in the lane journal.
