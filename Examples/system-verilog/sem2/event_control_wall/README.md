# Canonical-E explicit event control

This parser-native source uses `always @(en)`, an explicit level event control
under IEEE 1800-2023 §§9.2 and 9.4. The symbolic envelope retains the event
list as `AlwaysEvent`, and canonical E wakes the process only when `en`
changes. Icarus Verilog 13.0, Xcelium 24.03-s004, and the E receipt cover
the four source rows `x,x,1,0`.
