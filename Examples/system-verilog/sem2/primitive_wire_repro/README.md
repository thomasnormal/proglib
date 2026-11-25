# Primitive wire family receipt

The clean-room `primitive_wire_repro.sv` fixture exercises a parser-native
primitive wire connection through ordinary E. Its eight source rows match
Icarus Verilog 13.0 and Xcelium 24.03-s004, including x inputs.

Receipt command

```text
TMPDIR=<scratch> python3 harness/sv/batch_receipt.py --cleanroom-dir <cleanroom> --ordinary-timeout 120 --lean-group-size 1 --only primitive_wire_repro
```
