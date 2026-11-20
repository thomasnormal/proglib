# Plain internal edge and `always_ff` twin

This source-shaped receipt covers R13. A plain `always @(posedge g_plain)` and an `always_ff @(posedge g_ff)` process receive the same internally generated edge. Canonical E now includes retained plain event processes in the in-slot follow-up test, so both outputs are `x`, `1`, `1` on the three rows. Icarus Verilog 13.0 and Xcelium 24.03-s004 match those rows. The ordinary loader continues to refuse the internally driven clock with `Clock:source`.

The route uses the same §9.4.2 edge table for the retained event and edge process. The source kind remains in the AST, and no process is lowered.
