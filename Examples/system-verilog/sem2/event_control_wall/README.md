# Explicit event-control wall

This parser-native source uses `always @(en)`, an explicit level event control
under IEEE 1800-2023 §§9.2 and 9.4. The ordinary census retains the exact
`Clock:implicit` refusal because the frozen process AST has no event-list
constructor. The canonical E latch/implicit routes do not reinterpret this
source as `always_comb`; an event-list transport is still missing. Icarus
Verilog 13.0 and Xcelium 24.03-s004 agree on four source rows, but this receipt
claims simulator behavior only.
