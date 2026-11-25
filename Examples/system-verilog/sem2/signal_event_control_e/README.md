# Signal event-control refusal

The source uses `always_ff @(clk)` with a signal event control and no edge
keyword. Slang retains the parser-native any-edge process under IEEE
1800-2023 §9.4.2, while ordinary E keeps the explicit `Clock:implicit`
execution refusal. The eight source rows are pinned against Icarus Verilog
13.0 and Xcelium 24.03-s004; no E row is claimed.
