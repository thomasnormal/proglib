# Signal event-control refusal

The source uses `always_ff @(clk)` with a signal event control and no edge
keyword. Canonical E reports the same loud
`Clock:implicit: event-controlled process has no supported edge or implicit
sensitivity semantics` boundary under IEEE 1800-2023 §9.4.2. The eight source
rows are pinned in the batch receipt against Icarus Verilog 13.0 and Xcelium
24.03-s004; no E row is claimed.
