# Explicit event-list latch blocking self-write

This parser-native clean-room fixture covers IEEE 1800-2023 §9.4.2. An
`always @(en or a or t)` latch body reads `t` and then performs a blocking write
to `t` on the enabled path. The process is not sensitive while executing, then
re-arms when it returns, so canonical E refuses the simulator-dependent
self-trigger shape as `AlwaysEvent:self-write`.

Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on five rows
`x x`, `1 x`, `1 x`, `0 1`, `0 1`.
