# Collect-all refusal census witness

`refusal_census_three_walls.sv` has parameter-dependent aggregate declarations,
query-label selects, and a selected assignment target.  Slang 11.x extraction
retains five independent unsupported nodes.  The ordinary census calls the
same `PDesign` admission functions used by `load_design_sv2` and reports the
same five walls with source lines.  `census.jsonl` is the checked-in receipt;
each line is JSON and carries the stage, construct, source line, refusing
function, and message.

Run from the repository root:

```sh
python3 harness/sv/refusal_census.py extract --top refusal_census_three_walls \
  Examples/system-verilog/sem2/refusal_census_three_walls/refusal_census_three_walls.sv
python3 harness/sv/refusal_census.py ordinary \
  Examples/system-verilog/sem2/refusal_census_three_walls/refusal_census_three_walls.sv.json
```

The ordinary rows use the canonical Slang envelope and do not reparse source
text or maintain a second admission implementation.
