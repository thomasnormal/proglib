# Public child-instance wall reproduction

This clean-room source follows the public PicoRV32 optional-PCPI shape: an
active generate branch instantiates `picorv32_pcpi_fast_mul`, while the child
definition is absent from the source envelope. Slang retains the child as
`UninstantiatedDefSymbol:UninstantiatedDef`; the ordinary census also reports
`SlangError:UnknownModule` and the canonical-E member refusal.

The source is intentionally unresolved, so no simulator oracle result is
claimed. The parser envelope and census are the oracle for this loud refusal.

```sh
python3 extractors/sv/extract.py --top child_instance_wall \
  -o Examples/system-verilog/sem2/child_instance_wall/child_instance_wall.sv.json \
  Examples/system-verilog/sem2/child_instance_wall/child_instance_wall.sv
python3 harness/sv/refusal_census.py ordinary \
  Examples/system-verilog/sem2/child_instance_wall/child_instance_wall.sv.json
```
