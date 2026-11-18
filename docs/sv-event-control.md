# Retained scalar event controls

The SystemVerilog frontend retains a plain event-controlled `always` as an
`AlwaysEvent` node.  Its finite scalar list carries `any`, `posedge`, or
`negedge` for each member.  IEEE 1800-2023 §9.4.2 makes the event list part of
the process meaning, so ingestion rejects an empty list, malformed edge, or
expression event rather than dropping the control or recovering it from source
text.  The frozen scalar process route remains a loud refusal.  Canonical E's
source-shaped memory route executes the retained scalar event list in its
Active/NBA pass and rechecks event sources after NBA commit.

The clean-room fixture
`Examples/system-verilog/event_control_repro/event_control_repro.sv` contains
`always @(posedge clk) q_clk <= a` and `always @(a or b) q_event = a ^ b`.
The parser envelope retains `posedge clk`, `a:any`, and `b:any`.  The
`event_control_repro_ecanon` row in `harness/sv/cases2.json` runs seven input
rows through canonical E and Icarus Verilog 13.0.  Every `a`, `b`, `q_clk`, and
`q_event` value matches.  A direct Xcelium 24.03-s004 run on the same fixture
and stimulus produced the same seven rows.  The harness's Xcelium invocation
was license-unavailable during this run, so the pinned Xcelium comparison is
recorded from that direct run and is not claimed as a harness-gated receipt.
