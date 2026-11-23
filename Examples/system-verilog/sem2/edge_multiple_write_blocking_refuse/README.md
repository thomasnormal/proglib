# Same-edge blocking multiple writers

This parser-native clean-room fixture covers IEEE 1800-2023 §§4.7 and 10.4.1
for two edge-triggered processes that write the same variable on the same event.
Canonical E refuses with `Event:multiple-write` because the standard leaves the
cross-process update order open.

The six-row receipt matches Icarus Verilog 13.0 as `x,1,1,1,1,1` and Xcelium
24.03-s004 as `x,1,1,0,0,1`.
