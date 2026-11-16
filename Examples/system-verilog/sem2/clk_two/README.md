# Two-clock admission refusal

This source-shaped clean-room fixture has independent `posedge clk1` and
`posedge clk2` processes. IEEE 1800-2023 §§4 and 9.4.2 permit their edges to
arrive independently or simultaneously; the ordinary one-stimulus-per-cycle
route has no such event-queue input. It therefore refuses the design as
`Clock:multiple` rather than selecting an interleaving.

The language-level design for a future exact instant route is: each step is
chosen by an environment instant naming the set of clocks whose edges occur;
all interleavings and simultaneous-edge sets are legal, and simultaneous
NBA bodies sample the same pre-commit state before one joint commit. Hardware
metastability and synchronizer guarantees remain outside this route. This
fixture records refusal only; its source rows are checked against both pinned
simulators.
