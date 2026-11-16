# Generated member range select

This clean-room source exercises the source-shaped packed-member range
`state.value[i+1:i]` in a generated body under IEEE 1800-2023 §11.5.1.  Slang's
range-select node is retained with its genvar bounds; canonical E evaluates the
node directly without flattening or unrolling the generate loop.

The receipt covers known, x, and z member data.  The seven canonical-E rows
match Icarus Verilog 13.0 and Xcelium 24.03-s004.

Regenerate the checked-in envelope with:

```text
python3 extractors/sv/extract.py --top member_range_canonical_e \
  --retain-proc-rewrites \
  -o Examples/system-verilog/sem2/member_range_canonical_e/member_range_canonical_e.sv.json \
  Examples/system-verilog/sem2/member_range_canonical_e/member_range_canonical_e.sv
```
