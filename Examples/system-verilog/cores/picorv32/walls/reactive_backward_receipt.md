# Reactive backward dependency wall

This clean-room module exercises the running wall reached by the pinned
PicoRV32 `RISCV_FORMAL` E run. The first `always @*` process reads `t`, and the
later process writes `t`. IEEE 1800-2023 §9.2.2.2.1 permits the value change to
reactivate the earlier process in the same reactive region.

The source rows use `a=0` at time zero, then set `a=1` at 1 ns and sample at
2 ns and 3 ns. Icarus Verilog 13.0 and Xcelium 24.03-s004 both report
`y=x` at time zero and `y=1` at both later samples.

Canonical E now re-runs the retained reactive region to quiescence. Its two
input rows produce `(a,t,y) = (0,0,0)` and `(1,1,1)`, matching the defined
blocking-assignment result after the later process wakes the earlier process.
The bounded quiescence loop refuses only if the region fails to settle.

The executable checker `reactive_backward_check.py` reruns the same rows and
the canonical-E probe. It reports two matching canonical-E rows, three matching
rows from Icarus Verilog 13.0, and three matching rows from Xcelium 24.03-s004.
