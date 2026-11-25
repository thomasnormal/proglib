# Multi-step LFSR indexed-select receipt

This is the `multi_step_lfsr` wall from the 2026-11-25 inbox. The generated
clocked processes retain indexed unpacked-element and packed-bit selects under
IEEE 1800-2023 §§7.4.6, 9.2, and 27.4. Current ordinary E admits all generated
processes and runs eight rows at WIDTH=8, TAPS=8'hb8, including reset and the
source-shaped feedback transition. Icarus Verilog 13.0 and Xcelium 24.03-s004
match every row.
