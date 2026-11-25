# Parameterized storage ordinary-route timeout

This clean-room source is the parameter-sized unpacked-storage equation-gate
wall: `logic [7:0] stage [0:N-1]` is written and read by one `always_comb`
process, for `N=1` and `N=2`.

The approved extractor emits the envelope. Canonical E now admits both parameter points on the current ordinary route. The source witness has 16 rows and
agrees for both parameter points in Icarus Verilog 13.0 and the pinned Xcelium
24.03-s004 receipt: each point returns
`00000000`, `00000001`, `00010000`, `10100101`, `11111111`, `xxxxxxxx`,
`zzzzzzzz`, `01011010`. Run `python3 check.py` to reproduce the bounded
profile.
