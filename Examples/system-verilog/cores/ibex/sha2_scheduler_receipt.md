# Ibex SHA-2 scheduler boundary

After the typedef-backed `digest_i` range recovery, the pinned SHA-2 source
reaches canonical E's named scheduler refusal
`Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking
writes; canonical E refuses a multi-write reactive process whose intermediate
value another process can read`. Scheduler semantics are under audit, so this
item records the exact refusal and does not change `Scheduler.lean`.

The paired clean-room receipt uses the existing `preempt_block_refuse.sv`
fixture. The ordinary command produced zero E cycles with that refusal. Icarus
Verilog 13.0 and Xcelium 24.03-s004 each produced eight source cycles and
MATCHed one another on every row, including x/z inputs. No E/oracle MATCH is
claimed for a refused design.
