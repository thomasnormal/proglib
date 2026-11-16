# Non-topological continuous-assignment wall

This source is the faithful public wall-2 repro for the one-pass canonical E
settle boundary. The ordinary census emits exactly
`Instantiation:E:unsupported / PDesign.instantiateE2` with
`10.3: continuous assignment target is read from itself or a later assignment;
canonical E requires topological source order`.

Icarus Verilog 13.0 and Xcelium 24.03-s004 both produce `y=0,1,x,z` for the
four source inputs; the E route refuses before claiming a result.
