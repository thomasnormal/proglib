# Assertion-only initial process

This clean-room fixture isolates an `initial` assertion on a parameter, with a
continuous output derived from the same constant. The parser retains the
initial process; canonical E admits only the constant assertion check as an
inert time-zero adapter, while ordinary initial actions remain loud under
IEEE 1800-2023 §9.6.

The kernel receipt checks eight empty cycles at `N=1` and `N=0`. The source
rows match Icarus Verilog 13.0 and Xcelium 24.03-s004; Xcelium’s expected
assertion diagnostic at `N=0` is recorded by the source harness.
