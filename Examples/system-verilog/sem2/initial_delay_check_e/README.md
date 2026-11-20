# Diagnostic-only initial delay

This clean-room fixture keeps a literal `#1` and a `$error` assertion action
inside one source-shaped `initial` check. Canonical E admits the check through
its existing inert diagnostic adapter, while a timed edge or other procedural
process remains refused under IEEE 1800-2023 §§9.4 and 9.6.

The Lean receipt checks eight empty cycles with the output at `x`. The source
rows match Icarus Verilog 13.0 and Xcelium 24.03-s004 after the diagnostic
check's one-nanosecond delay; no general timed-process result is claimed.
