# Unpacked package-array read in a constant function

This source exercises IEEE 1800-2023 §§7.4.2, 7.4.6 and 13.4.3. An automatic
constant function reads an element of an unpacked package array with a runtime
function argument. The parser-native envelope retains the aggregate and the
function body. Canonical E evaluates `K = 7` and the output rows match Icarus
Verilog 13.0 and Xcelium 24.03-s004 for 0, `8'hff`, x and z inputs.
