# Same-edge race through a two-level child port

This parser-native clean-room fixture covers IEEE 1800-2023 §§4.7 and 10.4.1
when a parent blocking edge write feeds a grandchild edge reader through two
input-port connections. Canonical E closes the flattened clock aliases and
refuses with `Event:edge-blocking-race`.

The six-row receipt matches Icarus Verilog 13.0 as `x,1,1,1,1,1` and Xcelium
24.03-s004 as `x,x,x,1,1,0`. The differing rows are schedule-dependent.
