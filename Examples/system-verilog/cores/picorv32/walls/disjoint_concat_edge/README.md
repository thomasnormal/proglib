# Disjoint concatenation scheduler wall

This clean-room source has two same-edge blocking processes. One writes `x`
and the other writes the disjoint packed bits `{y[1], y[0]}`. The current
canonical edge guard refuses `Event:multiple-write` because its
`PLhs.concat` overlap case is conservative. The loaded probe confirms the
refusal without changing the source or expanding the target.

The pair has no shared concrete LHS root. It is a candidate for an exact
concatenation-overlap rule in canonical E.

The four-row receipt is `check.py`. Icarus Verilog 13.0
(`s20250103-64-gdad78d525`) and Xcelium 24.03-s004 both produce
`x x`, `0 0`, `0 0`, `0 1`.
