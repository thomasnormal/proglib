# Same-edge race through a child input port

This parser-native clean-room fixture covers IEEE 1800-2023 §§4.7 and 10.4.1
when a parent blocking edge write feeds a child edge reader through the input
port connection `.a(a)`. Hierarchy elaboration retains the connection as the
source-shaped continuous copy `u.a = a`, so canonical E closes the reader's
names through that connection and refuses with `Event:edge-blocking-race`.

The six-row receipt matches Icarus Verilog 13.0 as `x,1,1,1,1,1` and Xcelium
24.03-s004 as `x,x,x,1,1,0`. The differing rows are the schedule-dependent
interleaving that E refuses.
