# Package constant function in E

This clean-room source retains a parser-shaped automatic package function and
its call in a localparam constant context. Canonical E evaluates the pure
function with typed input binding and the same constant evaluator, preserving
IEEE 1800-2023 §10.8 and §11.8. The current ordinary route keeps this
source-shaped call and refuses it as `function 'vbits' in a constant context`.
Icarus Verilog 13.0 and Xcelium 24.03-s004 still match the three source rows.
