# Mixed continuous and edge-triggered packed-array writes

This source-shaped memory receipt exercises IEEE 1800-2023 §§4.5, 9.2, and 10.4. A continuous assignment updates `a[0]`, while an edge-triggered nonblocking assignment reads that value to update `a[1]`. The memory route settles active continuous processes before the clock edge and after the NBA commit. Icarus Verilog 13.0 and Xcelium Verilog 24.03-s004 agree on all five rows.
