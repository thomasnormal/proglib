# Procedural package constant-function regression

This parser-native row covers an automatic package function with a local
variable, a blocking initializer, and an `if` / `else-if` assignment chain.
The function declaration is kept in the envelope with its body as written
(`stmts`): the constant evaluator executes the statements under IEEE
1800-2023 §13.4.3. The body is not turned into an expression; the `body`
field, which the run-time function rung reads, is an `Unsupported` node.

The ordinary `load_design_sv2` receipt checks the package constants against
Slang's resolved values. Xcelium 26.09-s001 reports `rec::R.fa=10 rec::R.fb=12`
for `SEL=1`. Icarus Verilog 13.0 does not accept the packed-struct assignment
pattern in this unchanged source, so no Icarus oracle result is claimed.
