# Plain internal edge and `always_ff` twin

This source-shaped receipt covers R13. The plain `always @(posedge g)` and `always_ff @(posedge g)` sources are executed independently, so the plain process cannot be woken by its twin. Canonical E includes retained plain event processes in the in-slot follow-up test. Both sources have eight rows, including x/z clock and data values, and canonical E, Icarus Verilog 13.0, and Xcelium 24.03-s004 match all eight rows. The ordinary loader continues to refuse the internally driven clock with `Clock:source`.

The route uses the same §9.4.2 edge table for the retained event and edge process. The source kind remains in the AST, and no process is lowered.
