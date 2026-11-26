# Function-local unpacked-array refusal

This clean-room source exercises an automatic function with a local unpacked
array and a variable element select under IEEE 1800-2023 §§13.4 and 7.4. The
approved Slang extractor retains the function and call node. Canonical E
refuses the function-local storage at `SubroutineSymbol:Subroutine` before
execution, so no E value is claimed.

Icarus Verilog 13.0 and Xcelium 24.03-s004 both provide the five source rows
`0 -> a5`, `3 -> 14`, `8 -> ad`, `x -> xx`, and `z -> xx`.
