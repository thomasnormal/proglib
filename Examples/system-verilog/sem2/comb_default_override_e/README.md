# `always_comb` default override with a clocked consumer

This source-shaped wall combines a mandatory `always_comb` time-zero activation with a `posedge` consumer of its output. IEEE 1800-2023 §§4.7 and 9.2.2.2.2 leave the startup ordering open, so canonical E refuses it with `Event:time-zero` instead of selecting an ordering.

`check.py` pins the ordinary `load_design_sv2` receipt and the same three rows from Icarus Verilog 13.0 and Xcelium 24.03-s004. Both simulators report `q=x`, `q=x`, and `q=0` for the initial, first-edge, and enabled-edge rows.
