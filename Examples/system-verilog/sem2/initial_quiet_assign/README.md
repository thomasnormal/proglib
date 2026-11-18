# Quiet clocked-start counterexample

This source-shaped design has no runtime `initial`, `always_comb`, or
`always_latch` process and no `$readmemh`, but its continuous assignment drives
an output at time zero. IEEE 1800-2023 §§4.5 and 10.3 require that driver to
settle before observation. The receipt records the resulting boundary in
`CoreMemDesign.initialState_of_quiet`: the theorem's current assumptions do
not exclude continuous assignments, so `initialState` differs from
`CoreMemDesign.initial`.

Icarus Verilog 13.0 and Xcelium 24.03-s004 both report `y=1`.
