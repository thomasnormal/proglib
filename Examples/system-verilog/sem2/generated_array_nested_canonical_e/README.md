# Nested generated-array select

This clean-room source exercises a generated assignment whose expression is
the source-shaped nested select `state[i][0]`: an unpacked array element
followed by a packed bit select.  The extractor retains the Slang nodes as
`ArraySel` inside `BitSel`, and canonical E evaluates that composition
directly under IEEE 1800-2023 §§7.4.6 and 11.5.1.  The generated loop stays
parametric; it is not lowered into a second source language or unrolled by
ingestion.

The receipt drives `W=4` and `W=8`, including the initial/default value and
known, x, and z values on both inputs.  Icarus Verilog 13.0 and Xcelium
24.03-s004 are the pinned differential oracles.

Regenerate the checked-in envelope with:

```text
python3 extractors/sv/extract.py --top generated_array_nested_canonical_e \
  --retain-proc-rewrites \
  -o Examples/system-verilog/sem2/generated_array_nested_canonical_e/generated_array_nested_canonical_e.sv.json \
  Examples/system-verilog/sem2/generated_array_nested_canonical_e/generated_array_nested_canonical_e.sv
```

This receipt covers the retained nested generated-array select family named
`genvar_unpacked_chain` in the wall packet.
