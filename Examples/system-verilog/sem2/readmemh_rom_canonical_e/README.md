# `$readmemh` canonical-E receipt

The approved extractor retains the literal hexadecimal words in structured
`PReadmemh` metadata. Canonical E consumes those words at time zero into the
native `MemState`; it never opens the host file. Five address rows, including
an unknown address, match Icarus Verilog 13.0 and Xcelium `xrun(64)`
24.03-s004: `00000000`, `00010001`, `00100010`, `00110011`, `xxxxxxxx`.
