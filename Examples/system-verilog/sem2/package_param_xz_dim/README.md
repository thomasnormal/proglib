# Four-state package parameter in an integer-required dimension

The package parameter is retained as a four-state value, but IEEE
1800-2023 §§6.20.2 and 7.4 require a known integer for a packed dimension.
The ordinary loader therefore refuses the source-shaped declaration at the
named x/z parameter use. Icarus Verilog 13.0 and Xcelium 24.03-s004 provide the
source receipt separately.
