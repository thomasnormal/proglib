# Plain any-edge event boundary

The source-shaped `always_ff @(clk)` process is an any-edge event control
(IEEE 1800-2023 §9.4.2), not a `posedge` or `negedge` clock edge. The ordinary
E route retains it as an event process and the differential receipt covers its
five rows on both pinned simulators.

The clocked `sv_structure` profile deliberately refuses this construct with:

```text
process 0 is a plain `always` whose event list is not one clock edge with an optional asynchronous reset edge (a level-change event as in `always @(a or b)`, or more than two events; kept as an event process): outside the clocked profile, refused
```

This is a precise profile boundary, not a claim that the source is invalid or
that its any-edge behavior has been simplified.
