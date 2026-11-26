# Generated event-control receipt

The source contains `always @(posedge clk)` inside a parser-native
`generate for` body under IEEE 1800-2023 §§9.2, 9.4, and 27.4.  The approved
extractor retains the `AlwaysEvent` node, and canonical E expands the active
generate instance while preserving the event list and nonblocking body.  No
source-text rewrite or scheduler shortcut is introduced.

The Lean receipt checks the expanded `CoreMemProc.event` shape.  The checker
also runs four rows on Icarus Verilog 13.0 and Xcelium Verilog 24.03-s004.
Both simulators report the same sequence `x, 1, 1, 0`.  This receipt covers
the generated-process admission boundary.  General event-queue semantics for
arbitrary event controls remains outside this profile.
