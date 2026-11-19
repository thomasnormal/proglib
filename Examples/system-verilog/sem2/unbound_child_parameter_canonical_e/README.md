# Unbound child parameter in canonical E

This clean-room source has a top module instantiating a child without a
parameter override. The child keeps its parser-resolved default width, and
canonical hierarchy expansion applies that default before checking the
source-shaped ANSI ports.

Eight known and four-state input rows match canonical E, Icarus Verilog 13.0,
and Xcelium 24.03-s004.
