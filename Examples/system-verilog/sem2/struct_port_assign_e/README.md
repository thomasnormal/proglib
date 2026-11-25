# Struct-port continuous assignment

This source-shaped receipt covers the Ibex `shadow_inputs_in.field = input_i` family. A packed aggregate has three fields, each driven by a continuous assignment, and the aggregate is observed through a packed output. The assignments remain parser-native struct-member targets under IEEE 1800-2023 §§6.24 and 10.6.

The receipt command is `python3 Examples/system-verilog/sem2/struct_port_assign_e/check.py`. It regenerates the envelope, builds the ordinary canonical-E check, and compares three rows including x/z inputs against Icarus Verilog 13.0 and Xcelium 24.03-s004.
