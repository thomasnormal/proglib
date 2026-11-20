# Plain `always` inside a generate loop

This source-shaped receipt covers R14. A `for` generate loop retains one plain
`always @(posedge clk)` per genvar value. Canonical E substitutes the genvar in
the process body before execution, including the packed bit-select target and
source index. The fixture uses `W=2`, and its eight rows include zero/one,
unknown, and high-impedance clock and data values. Canonical E, Icarus Verilog
13.0, and Xcelium 24.03-s004 agree on every row.

Regenerate the envelope from the repository root with:

```sh
python3 extractors/sv/extract.py --top plain_generate_edge_e \
  --retain-loops --retain-proc-rewrites \
  -o Examples/system-verilog/sem2/plain_generate_edge_e/plain_generate_edge_e.sv.json \
  Examples/system-verilog/sem2/plain_generate_edge_e/plain_generate_edge_e.sv
```
