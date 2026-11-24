# Two-process disjoint blocking confluence witness

This clean-room fixture has two independent `always @(posedge clk)` processes.
One writes `a` from `d`, and the other writes `b` from `e`. Their writes are
disjoint, so the parser-native guard supplies the cross-process read exclusions
needed by the retained evaluator diamond under IEEE 1800-2023 §4.7 and IEEE
1364.1-2002 §5.2.2 and Annex B.1.

`agree.lean` checks the parser guard and its exact read-closure adapter.
It also instantiates the guarded hidden-observation terminal-path adapter,
with the destination names carried as the explicit hidden observation set.
`check.py` compares the source rows with Icarus Verilog 13.0 and readiness-gated
Xcelium.
