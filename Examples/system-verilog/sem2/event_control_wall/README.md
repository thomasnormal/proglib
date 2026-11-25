# Canonical-E explicit event control

This parser-native source uses `always @(en)`, an explicit level event control
under IEEE 1800-2023 §§9.2 and 9.4. The symbolic envelope retains the event
list as `AlwaysEvent`. The current frozen process AST has no event-list
constructor, so the semantic tier refuses it as
`ProceduralBlockSymbol:Always`; no ordinary-E value row is claimed. Icarus
Verilog 13.0 and Xcelium 24.03-s004 agree on the four simulator-only rows
`0,0,1,0`.
