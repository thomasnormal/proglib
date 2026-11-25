# Unpacked-element bit-select target boundary

This fixture exercises continuous assignments to a packed bit of a
parameter-sized unpacked element under IEEE 1800-2023 §§7.4.6, 10.3, and
11.5.1. The extractor retains the target as a source-shaped `BitSel` over
`ArraySel`. Canonical E evaluates the four rows as `0000`, `1001`, `xxxx`,
and `xxxx`. Icarus Verilog 13.0 and Xcelium 24.03-s004 produce the same four
rows, including x/z inputs.

This is the clean-room `unpacked_bitselect_target` repro. The source-shaped
target remains intact through extraction and canonical E evaluates it on the
memory route. The `agree.lean` receipt pins the E rows and the simulator
checker records the two oracle runs.
