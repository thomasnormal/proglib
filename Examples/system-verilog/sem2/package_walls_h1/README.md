# Procedural package constant-function regression

This parser-native row covers an automatic package function with a local
variable, a blocking initializer, and an `if` / `else-if` assignment chain.
The function declaration remains in the envelope and its package constant
call is evaluated in declaration order under IEEE 1800-2023 §13.4.3.

The ordinary `load_design_sv2` receipt checks the package default against
Slang's resolved value. Xcelium 26.09-s001 reports `rec::R.fa=10 rec::R.fb=12`
for `SEL=1`. Icarus Verilog 13.0 does not accept the packed-struct assignment
pattern in this unchanged source, so no Icarus oracle result is claimed.
