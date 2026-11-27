# Plain `always @*` with a procedural loop

The extractor retains the parser's implicit event-control node as
`AlwaysEvent` with `event_kind = ImplicitEventControl`. The memory executor
executes the source-shaped `for` statement at each activation. This follows
IEEE 1800-2023 §9.4.2.2 and keeps the distinction from `always_comb` in
§9.2.2.2, including the initial wait. Icarus Verilog 13.0 and Xcelium
26.09-s001 agree on `0000`, `0011`, `0000`, `0000`, and `0000` for the five
four-state rows.
