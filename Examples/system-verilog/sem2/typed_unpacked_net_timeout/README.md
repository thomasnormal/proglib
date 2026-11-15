# Typed unpacked net ordinary-route timeout

This clean-room source is the generic `NetSymbol:type` wall: a four-state
`wire [7:0] tree [0:3]` with a short chain of source-shaped continuous element
assignments and a whole-vector output copy.

The approved extractor emits the envelope. The bounded ordinary-E probe spends
60 seconds in `load_design_sv2`/ordinary elaboration without reaching `#check
 typedUnpackedNet.e`; no E result is claimed. The source witness is green on
all eight rows in Icarus Verilog 13.0 and the pinned Xcelium 24.03-s004 receipt
(`10000011`, `10000000`, `10111101`, `01111111`, `xxxxxxxx`, `zzzzzzzz`,
`00111000`, `10100011`). Run `python3 check.py` to reproduce the bounded
profile.
