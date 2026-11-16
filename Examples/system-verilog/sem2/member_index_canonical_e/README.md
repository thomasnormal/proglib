# Generated member element index

This clean-room source exercises the source-shaped packed-member element index
`state.out_dis[i]` in a generated body under IEEE 1800-2023 §11.5.1.  Slang's
member-select node is retained with its genvar bound; canonical E evaluates the
node directly without flattening or unrolling the generate loop.

The receipt covers known, x, and z member data.  The seven canonical-E rows
match Icarus Verilog 13.0 and Xcelium 24.03-s004.

Regenerate the checked-in envelope with:

```text
python3 extractors/sv/extract.py --top member_index_canonical_e \
  --retain-proc-rewrites \
  -o Examples/system-verilog/sem2/member_index_canonical_e/member_index_canonical_e.sv.json \
  Examples/system-verilog/sem2/member_index_canonical_e/member_index_canonical_e.sv
```
