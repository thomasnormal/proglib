# Primitive gate family receipt

The clean-room `primitive_gate_family_e.sv` fixture exercises parser-native
primitive gates under canonical E. Its eight source rows match Icarus Verilog
13.0 and Xcelium 24.03-s004, including x inputs.

Receipt command

```text
TMPDIR=<scratch> python3 harness/sv/batch_receipt.py --cleanroom-dir <cleanroom> --ordinary-timeout 120 --lean-group-size 1 --only primitive_gate_family_e
```
