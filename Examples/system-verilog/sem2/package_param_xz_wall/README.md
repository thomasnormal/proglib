# Package parameter with a four-state default

This clean-room row exercises IEEE 1800-2023 §§6.20.2 and 6.11 with a
source-shaped `logic [31:0]` package parameter whose default contains 25 `z`
bits followed by the `LUI` opcode.  Canonical E now retains that exact
four-state vector for ordinary operand use.  The integer-required route still
refuses the named parameter when its value contains x/z bits.

Icarus Verilog 13.0 and Xcelium 24.03-s004 both produce the same source row,
`zzzzzzzzzzzzzzzzzzzzzzzzz0110111`.  Run `python3 check.py` for the
byte-identical envelope, four-state Lean receipt, and simulator checks.
