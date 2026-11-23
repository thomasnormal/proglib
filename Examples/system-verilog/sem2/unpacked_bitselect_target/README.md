# Unpacked-element bit-select target boundary

This fixture exercises continuous assignments to a packed bit of a
parameter-sized unpacked element under IEEE 1800-2023 §§7.4.6, 10.3, and
11.5.1. The extractor now retains the target as a source-shaped `BitSel` over
`ArraySel`. Canonical E reaches its explicit memory-target refusal. Icarus
Verilog 13.0 and Xcelium 24.03-s004 match four rows, including x/z inputs.
