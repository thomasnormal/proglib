# `$test$plusargs` system-function expression wall

This clean-room module retains the IEEE 1800-2023 §20.2.2 system-function call
in a conditional expression. The approved parser produces a typed `SysCall`
node with the spelling `$test$plusargs`, and ingestion preserves that node.
The declared-signal value tier has no plusarg-environment parameter, so its
`Expr2` view is a loud `SysCall` refusal instead of a replacement constant or
identifier. The canonical E envelope retains the parser node and therefore
makes no execution claim for this external query.

Before this change, extractor and ordinary admission each reported one
`CallExpression / parsePExpr` refusal. After the typed node landed, both
censuses report zero refusals. The value-tier receipt below keeps the remaining
semantic boundary explicit.

The simulator receipt covers both absence and presence of `+flag`, with input
values `0`, `1`, `x`, and `z`. Icarus Verilog 13.0
(`s20250103-64-gdad78d525`) and Xcelium `24.03-s004` each match all eight
rows. Run it with:

```text
python3 Examples/system-verilog/sem2/system_function_plusargs/check.py
```
