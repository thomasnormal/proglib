# Async memory FIFO canonical-E receipt

This source-shaped one-rank unpacked memory has an active-low asynchronous
reset and a positive-edge nonblocking write to `mem[0]`, followed by a
continuous read. Canonical E keeps the memory as native `MemState` and matches
five reset/edge rows on Icarus Verilog 13.0 and Xcelium `xrun(64)` 24.03-s004:
`00000000`, `00000000`, `00010001`, `00010001`, `00100010`.
