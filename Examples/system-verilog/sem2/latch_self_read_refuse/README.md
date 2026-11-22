# `always_latch` self-read refusal

These parser-native clean-room fixtures cover the two audited read-before-write
shapes under IEEE 1800-2023 §9.2.2.3. Canonical E refuses both with
`AlwaysLatch:self-read`, preserving the event-driven simulator boundary rather
than choosing a startup or activation ordering.

`check.py` runs six four-state enable/data rows for each shape against Icarus
Verilog 13.0 and Xcelium 24.03-s004. The simulator rows are retained as differential
evidence for the refusal.
