# Two-process NBA confluence witness

This clean-room fixture has two independent `always_ff @(posedge clk)`
processes.  One writes `a_q` from `a_in`, the other writes `b_q` from `b_in`.
Their parser-retained queues have disjoint targets, so the admitted canonical-E
NBA scheduler can erase either process order under IEEE 1800-2023 §4.7.

`agree.lean` checks the two-process shape and four source-shaped rows through
`CoreMemDesign.step`.  `check.py` compares the same rows with Icarus Verilog
13.0 and readiness-gated Xcelium.
