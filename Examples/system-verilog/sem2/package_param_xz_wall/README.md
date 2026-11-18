# Package parameter with a four-state default

This clean-room row exercises IEEE 1800-2023 §6.20.2 and §6.11 with a
source-shaped `logic [31:0]` package parameter whose default contains 25 `z`
bits followed by the `LUI` opcode.  The canonical E package-constant tier
refuses the default as `x/z literal in a constant context`, because its trusted
package bindings are currently INT/LVec-free.  The receipt keeps that refusal
loud rather than reinterpreting the value as an integer.

Icarus Verilog 13.0 and Xcelium 24.03-s004 both produce the same source row,
`zzzzzzzzzzzzzzzzzzzzzzzzz0110111`.  Run `python3 check.py` for the
byte-identical envelope, Lean refusal receipt, and simulator checks.
