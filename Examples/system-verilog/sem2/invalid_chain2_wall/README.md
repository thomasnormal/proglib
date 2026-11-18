# Invalid continuous-assignment chain wall

This clean-room module exercises the IEEE 1800-2023 §10.6 invalid
continuous-assignment shape in a generated chain. The source retains the
hierarchical `chain[3].running_sum` read, the generated `terms[row]` index, and
the later-row assignment that depends on the previous generated instance.

The extractor reports four source rows. Ordinary canonical-E retains those
nodes and reaches the generated-scope storage refusal
`UnpackedDecl:generate-scope: active generate declarations contain duplicate
names`. No assignment is lowered to a scalar copy, and no E execution result is
claimed for this wall.

Icarus Verilog 13.0 (`s20250103-64-gdad78d525`) and Xcelium `24.03-s004` both
report `1111` followed by `x111` for the faithful source rows. Run the receipt
with:

```text
python3 Examples/system-verilog/sem2/invalid_chain2_wall/check.py
```
