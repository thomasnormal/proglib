# Deferred scheduler refusals

The independent scheduler audit identified two source shapes that canonical E currently refuses with `Schedule:preemptive` even though their observed readers are edge-triggered and the intermediate continuous value is not exposed by an unrelated event in the measured rows. This is an inventory item only. The canonical admission predicate remains unchanged while the sound PREEMPT-WIDEN proposal is rejected.

| audit shape | source-shaped reason for the current refusal | Icarus Verilog 13.0 | Xcelium Verilog 24.03-s004 | disposition |
|---|---|---|---|---|
| d13b, continuous `assign m = ~nxt` feeding `always_ff @(posedge clk)` | the reactive combinational writer of `nxt` is connected through a continuous assign and the preemptive guard conservatively keeps the pair | `xx`, `01`, `01`, `11` | `xx`, `01`, `01`, `11` | list only, defer any admission change |
| d23, parent `always_comb` driving a child flop input through a port | the port merge is represented as a continuous assign into the child, so the hierarchy path is outside the current widening predicate | `xx`, `01`, `01`, `10` | `xx`, `01`, `01`, `10` | list only, defer any admission change |

The d13b source shape is a combinational `nxt` writer, a continuous inversion into `m`, and a flop sampling `m` on an unrelated input clock. The d23 source shape is a parent combinational `nxt` writer connected to a child `always_ff` input. Both rows are retained as audit evidence. They do not justify a new scheduler resolution or a weakened refusal.
