# Unpacked-element bit-select target boundary

This fixture exercises continuous assignments to a packed bit of a
parameter-sized unpacked element under IEEE 1800-2023 §§7.4.6, 10.3, and
11.5.1. The extractor now retains the target as a source-shaped `BitSel` over
`ArraySel`. Canonical E reaches its explicit memory-target refusal. Icarus
Verilog 13.0 and Xcelium 24.03-s004 match four rows, including x/z inputs.

This is the clean-room `unpacked_bitselect_target` repro. The extractor
retains the source-shaped target and ordinary E refuses it explicitly. The
simulator rows are recorded without claiming an E value match.

Update (master repair): since 75a9b0468 canonical E admits this target as a
generated unpacked bit target (`PLhs.arrayBitSel`), so the refusal recorded
above no longer occurs. `agree.lean` now pins the values E computes on the
four testbench rows (`0000`, `1001`, `xxxx`, `xxxx`). No oracle result is
claimed for that pin: the simulators were not re-run against E's values, and
`check.py` still prints the old refusal line.
