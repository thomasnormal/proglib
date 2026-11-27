# Unbased fill operands in localparam concatenations

This source exercises IEEE 1800-2023 §5.7.1 unbased unsized `'0` and `'1`
operands inside concatenations used by typed and untyped localparams. Each fill
has one self-determined bit in the concatenation, and the typed localparams then
apply their enclosing packed assignment width under §10.8.

The canonical E receipt checks W=4 and W=8. Icarus Verilog 13.0 and Xcelium
24.03-s004 produce the same two rows at each point.

Run the receipt with `python3 check.py` from the repository root.
