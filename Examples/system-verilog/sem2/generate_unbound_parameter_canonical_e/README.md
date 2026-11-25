# Generated child connection in canonical E

This clean-room source has a top module instantiating a child with an
unconnected parameter override. The child’s default `SPAN=4` selects its
source-shaped generated assignment; canonical hierarchy expansion now
elaborates that child point and hoists the generated process before applying
§23.3.3 input/output port connections.

Eight known and z input rows match canonical E, Icarus Verilog 13.0, and
Xcelium 24.03-s004.

The current receipt reports eight matching generated-child rows, including the
z input case.
