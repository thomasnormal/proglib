# Parameterized storage ordinary-route timeout

This clean-room source is the parameter-sized unpacked-storage equation-gate
wall: `logic [7:0] stage [0:N-1]` is written and read by one `always_comb`
process, for `N=1` and `N=2`.

The approved extractor emits the envelope. The bounded ordinary-E probe spends
45 seconds in the same `load_design_sv2`/ordinary elaboration-and-run path
(inside the batch route's 60-second bound) while requesting both parameter
points, without producing an E result; no E row is claimed. A load-only probe
on this tree takes about 51 seconds, so the wall is dominated by ordinary
loading before the rows can be emitted. The source witness has 16 rows and
agrees for both parameter points in Icarus
Verilog 13.0 and the pinned Xcelium 24.03-s004 receipt: each point returns
`00000000`, `00000001`, `00010000`, `10100101`, `11111111`, `xxxxxxxx`,
`zzzzzzzz`, `01011010`. Run `python3 check.py` to reproduce the bounded
profile.
