# Package-function argument readiness regression

The package dependency walker visits every source-shaped function-call argument
before binding the call. `cfg::M = bigger(cfg::D, 2)` therefore waits for
`cfg::D = base::U`, under IEEE 1800-2023 §13.4 and declaration-order rules.
The ordinary loader checks `base::U=4`, `cfg::D=4`, and `cfg::M=4`.
Xcelium 26.09-s001 reports `cfg::M=4`. Icarus Verilog 13.0 reports the same
unchanged pass-through design row.
