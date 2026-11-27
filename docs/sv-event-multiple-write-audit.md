# Same-event multiple-write audit

This audit measures the source-shaped `fuji_float_dot` envelope with the
current canonical-E event detector. It contains 42 retained processes and the
detector reports 11 candidate pairs. Every candidate pair shares a `posedge
clk` event source. Expanding a generated hierarchy is a separate step and is
not included in this source-level table.

The detector treats a concatenated left-hand side as potentially overlapping
every other left-hand side. The `exact roots` column expands those
concatenations into their named targets before comparing them. A `no` value
means the pair has no equal target root in the retained source shape. Such a
pair is schedule-independent with respect to direct target overlap. It does
not justify changing the admission rule until generated-instance expansion
and simulator rows are available.

| processes | shared event | detector candidate | exact roots overlap | classification |
| ---: | --- | --- | --- | --- |
| 0, 5 | `clk` posedge | yes | no | detector over-approximation from concatenated target |
| 0, 6 | `clk` posedge | yes | no | detector over-approximation from concatenated target |
| 1, 5 | `clk` posedge | yes | no | detector over-approximation from concatenated target |
| 1, 6 | `clk` posedge | yes | no | detector over-approximation from concatenated target |
| 5, 6 | `clk` posedge | yes | no | detector over-approximation from concatenated targets |
| 5, 24 | `clk` posedge | yes | no | detector over-approximation from concatenated target |
| 5, 28 | `clk` posedge | yes | no | detector over-approximation from concatenated target |
| 5, 41 | `clk` posedge | yes | no | detector over-approximation from concatenated target |
| 6, 24 | `clk` posedge | yes | no | detector over-approximation from concatenated target |
| 6, 28 | `clk` posedge | yes | no | detector over-approximation from concatenated target |
| 6, 41 | `clk` posedge | yes | no | detector over-approximation from concatenated target |

The audit does not widen `Event:multiple-write`. The complete 45-process,
14-pair generated-instance figure remains pending a reproducible expanded
envelope and paired Icarus/Xcelium rows.
