# Generated child scalar storage

The active `else : shift` generate arm declares `pipe` inside the child module.
IEEE 1800-2023 §§23.3.3 and 27.4 preserve that declaration in the instantiated
child scope. Canonical E now carries the parser-native declaration through
hierarchy flattening as `child.shift.pipe`, so the edge process updates storage
before the child output assignment reads it.

The ordinary `load_design_sv2` receipt checks `WIDTH=8` and `DEPTH=2`. The
five rows cover zero, known values, x, and z input bits. Icarus Verilog 13.0
and Xcelium 24.03-s004 are the pinned simulator oracles.
