# Scheduler S1 C1/C2 receipt

Source `scheduler_race.sv` SHA-256 `0d0d70488145d35e20dbf3dcba01f941ff1297ef65d34e2b7d7a067561f30d8a`.
The bench is parser-shaped source with two `always @(posedge clk)` processes,
each enqueueing one NBA to `q` in the same active region.

| pinned oracle | measured transcript | membership |
| --- | --- | --- |
| Icarus Verilog 13.0 | `S1-C1 q=00` | `{00}` |
| Xcelium 24.03-s004 | `S1-C1 q=01` | `{01}` |

The scheduler's source-shaped `raceDesign` enumerates both `{00, 01}`.  The
different pinned transcripts are retained as evidence of the permitted active
event ordering under IEEE 1800-2023 §§4.6 and 10.4.2.  Neither simulator's
single observed order is promoted to the semantics.
