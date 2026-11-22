# Same-edge race through a continuous assignment

This parser-native clean-room fixture covers IEEE 1800-2023 §§4.7 and 10.4.1
when a blocking edge write reaches a second edge process through `assign w = a`.
Canonical E closes the reader's source names through the assignment and refuses
with `Event:edge-blocking-race`.

The six-row receipt matches Icarus Verilog 13.0 as `x,x,x,0,0,0` and Xcelium
24.03-s004 as `x,x,x,1,1,0`. The differing rows are the schedule-dependent
interleaving that E refuses.
