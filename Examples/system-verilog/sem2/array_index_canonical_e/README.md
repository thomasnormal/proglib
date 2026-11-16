# Member element index

This clean-room source exercises the source-shaped unpacked-array element
read `values[i]` from IEEE 1800-2023 §11.5.1.  The Slang parser node is
retained as an `ArraySel` and canonical E evaluates that node directly over a
fixed unpacked dimension; ingestion does not flatten the array.

The array is intentionally undriven, so every output is `x`.  The receipt
still drives known, x, and z index values, and both pinned source simulators
agree with E on all eight rows: Icarus Verilog 13.0 and Xcelium 24.03-s004.

Regenerate the checked-in envelope with:

```text
python3 extractors/sv/extract.py --top array_index_canonical_e \
  -o Examples/system-verilog/sem2/array_index_canonical_e/array_index_canonical_e.sv.json \
  Examples/system-verilog/sem2/array_index_canonical_e/array_index_canonical_e.sv
```
