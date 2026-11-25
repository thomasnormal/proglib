# Prefix-adder unpacked-array target boundary

This is the `prefix_adder_unpacked_array` clean-room wall. Slang retains the
generate-loop assignment to a packed bit of an unpacked element, and current
ordinary E admits it under IEEE 1800-2023 §§7.4.6 and 10.3. Four rows match
Icarus Verilog 13.0 and Xcelium 24.03-s004, including x/z values.
