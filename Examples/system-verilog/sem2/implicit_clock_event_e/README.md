# Implicit event-control refusal

The source uses `always_ff @(clk)` without an edge keyword. Slang retains the
parser-shaped process, while canonical E refuses it as
`Clock:implicit: event-controlled process has no supported edge or implicit
sensitivity semantics`. IEEE 1800-2023 §9.4.2 event-control behavior is not
approximated by a clock edge. The eight source rows are pinned in the batch
receipt against Icarus Verilog 13.0 and Xcelium 24.03-s004.
