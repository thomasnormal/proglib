# Memory edge-order FIFO receipt

This clean-room fixture has two `always_ff` blocks: one updates scalar FIFO
state and one writes an unpacked memory, including a procedural reset loop.
It is the tactic-side target for the indexed-memory NBA edge-order wall.

The source is intentionally not rewritten into one process or a flat array.
Until the semantic lane publishes `EDGEORDER-MEM READY`, `sv_structure` is
expected to refuse its `oblEdgeOrder` obligation; the current memory-aware
predicate also remains false for the dynamic write target, so the receipt below
records the ordinary memory route and the hand-proof loop lemmas only.
