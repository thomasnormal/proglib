# Canonical-E `always_latch`

This parser-native receipt admits `always_latch` as a retained level-sensitive
process under IEEE 1800-2023 §§9.2.2.3 and 9.4.2. The body uses a blocking
assignment, as required by the canonical combinational executor; incomplete
assignment preserves the latch state. Icarus Verilog 13.0, Xcelium 24.03-s004,
and the Lean E receipt cover enable 0/1/x/z rows and agree on `x,1,1,1,1,0`.
The current receipt reports six matching rows on both pinned simulators.

Run the paired ordinary-E and simulator receipt with
`TMPDIR=<scratch> python3 Examples/system-verilog/sem2/always_latch_e/check.py`.
This source-shaped level-sensitive process is the clean-room analogue of the
`AlwaysLatch` boundary reached by the pinned Ibex closure.
