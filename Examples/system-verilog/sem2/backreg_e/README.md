# Continuous-assignment settling

This clean-room fixture is the source-shaped chain from IEEE 1800-2023
§§4.5 and 10.3: `a` is assigned from `b`, `b` from `c`, and `c` from the
clocked register `q`.  Canonical E repeats its continuous-assignment pass to
quiescence, so this non-topological source order reaches the settled value.

`agree.lean` checks the canonical-E rows.  `check.py` regenerates the Slang
envelope and compares eight x/z-inclusive source rows against Icarus Verilog
13.0 and Xcelium 24.03-s004.  Both simulators report `a=xxxx,0101,0101,
0101,1001,1001,1001,1001` for the eight rows, and E matches those values.
