# Topological continuous-assignment refusal

This clean-room fixture is the source-shaped chain from IEEE 1800-2023
§§4.5 and 10.3: `a` is assigned from `b`, `b` from `c`, and `c` from the
clocked register `q`.  The canonical E memory route currently performs a
source-order settle pass, so it refuses a driver that reads the target of a
later continuous assignment instead of claiming the stale value that the
old route produced.

`agree.lean` checks the exact refusal.  `check.py` regenerates the Slang
envelope and compares eight x/z-inclusive source rows against Icarus Verilog
13.0 and Xcelium 24.03-s004.  Both simulators report `a=xxxx,0101,0101,
0101,1001,1001,1001,1001` for the eight rows; E claims no value for this
shape until its settling theorem is available.
