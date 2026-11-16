# Two-clock admission refusal

This source-shaped clean-room fixture has independent `posedge clk1` and
`posedge clk2` processes. IEEE 1800-2023 §§4 and 9.4.2 permit their edges to
arrive independently or simultaneously; the ordinary one-stimulus-per-cycle
route has no such event-queue input. It therefore refuses the design as
`Clock:multiple` rather than selecting an interleaving.

This fixture records refusal only; its source rows are checked against both pinned simulators.

Canonical E now runs the same source-shaped rows directly through `CoreMemDesign.step`: separate edges update one domain at a time, a coincident edge samples the old value in the other domain, stopped clocks do not fire, and x/z clock transitions use the retained four-state edge table.
