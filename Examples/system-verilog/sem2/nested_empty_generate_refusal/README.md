# Nested empty generate template

The outer generate loop has `j=0` as its first default iteration. Its nested
loop `k=0..j-1` therefore has no elaborated body at that iteration, while a
later outer iteration is nonempty. The approved extractor retains the outer
and inner symbolic loops and their source assignment. Canonical E reaches the
independent four-state output-net boundary `PortSymbol:net-z`; no E value row
is claimed. The unchanged source runs as `y=1z` on Icarus Verilog 13.0 and
Xcelium `xrun(64)` 24.03-s004.
