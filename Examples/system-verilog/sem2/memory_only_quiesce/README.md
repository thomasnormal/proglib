# Memory-only quiescence wrong-answer reproducer

This clean-room design has two `always_comb` processes that update only a
source-shaped unpacked memory. Their source order requires a second active pass
for `mem[1]` to observe the new `mem[0]`; the scalar output `q` remains zero.

Canonical E now refuses this source-shaped reactive memory access with `Comb:memory-quiescence`, because its quiescence scheduler does not yet carry memory changes through sensitivity and fixpoint checks. Icarus Verilog 13.0 produces `seed0 q=0 mem=00` and `seed1 q=0 mem=11`. Xcelium 24.03-s004 produces the same two rows. The prior `q=0,mem=xx|q=0,mem=xx` result was a wrong answer and is closed by the refusal.
