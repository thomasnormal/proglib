# Reactive backward dependency wall

This clean-room module exercises the running wall reached by the pinned
PicoRV32 `RISCV_FORMAL` E run. The first `always @*` process reads `t`, and the
later process writes `t`. IEEE 1800-2023 §9.2.2.2.1 permits the value change to
reactivate the earlier process in the same reactive region.

The source rows use `a=0` at time zero, then set `a=1` at 1 ns and sample at
2 ns and 3 ns. Icarus Verilog 13.0 and Xcelium 24.03-s004 both report
`y=x` at time zero and `y=1` at both later samples.

Canonical E currently refuses the instantiated envelope with

```
Comb:dependency-order: 9.2.2.2/9.4.2.2: reactive process reads 't' from itself or a later reactive process; canonical E has no fixed-point scheduler
```

No E trace is claimed for this row. The refusal is the first running wall after
PicoRV32's 360 admitted, 0 refused, 4 inactive census.
