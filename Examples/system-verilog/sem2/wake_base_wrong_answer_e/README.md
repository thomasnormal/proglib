# WAKE-BASE wrong-answer audit

This source-shaped witness isolates the stale wake-base candidate from IEEE
1800-2023 §§4.5, 9.4.2, and 10.4.2. A clocked process performs
`g = 0; g <= 1;` while `g` starts at `1`. The nonblocking update is therefore a
`0→1` transition and the `always @(posedge g)` observer must run.

The checked-in receipt runs two rows through Icarus Verilog 13.0 and Xcelium
24.03-s004. Both report `count=1` after seeding `g=1` and `count=2` after the
clocked blocking/NBA pair. The ordinary E loader names this exact source shape
as a multiple-write event-source refusal. The relation audit also covers a
manually reachable cursor state, where the old executor wake base otherwise
misses the NBA-induced edge.
