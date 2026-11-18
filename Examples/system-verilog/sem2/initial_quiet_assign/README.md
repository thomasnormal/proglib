# Quiet clocked-start counterexample

This source-shaped design has no runtime `initial`, `always_comb`, or
`always_latch` process and no `$readmemh`, but its continuous assignment drives
an output at time zero. IEEE 1800-2017 §§4.5 and 10.3 require that driver to
settle before the first stable observation in the time slot. The receipt records
the resulting boundary in `CoreMemDesign.initialState_of_quiet`: the theorem's
current assumptions do not exclude continuous assignments, so
`initialState` differs from `CoreMemDesign.initial`.

The old E view is `y=x` and the new settled E view is `y=1`. Icarus Verilog
13.0 and Xcelium 24.03-s004 both report `y=1` after `#0` and at `#1`. Their
immediate active-region observations differ (`1` for Icarus and `x` for
Xcelium), so that row is not used as a semantic oracle. The change is
conservative for every admitted design whose continuous assignments already
leave its initial view unchanged, and it changes the result only for designs
whose first stable time-zero observation depends on a continuous driver.
