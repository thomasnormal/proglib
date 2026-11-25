# Memory-only quiescence wrong-answer reproducer

This clean-room design has two `always_comb` processes that update only a
source-shaped unpacked memory. Their source order requires a second active pass
for `mem[1]` to observe the new `mem[0]`; the scalar output `q` remains zero.

Canonical E's `runCombSettleQuiesce` compares only `CoreMemState.scalar.view`.
It returns `ok` with `q=0,mem=xx|q=0,mem=xx`, silently dropping both memory
updates. Icarus Verilog 13.0 produces `seed0 q=0 mem=00` and `seed1 q=0 mem=11`.
The result is a wrong answer. Xcelium 24.03-s004 produces the same two rows.
