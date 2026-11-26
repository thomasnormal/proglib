# Parameter-bound clocked procedural loop

This source isolates an external `integer` loop iterator with a parameter-bound
initial value and descending step. The Slang envelope retains the `for` node,
and canonical E instantiates it at the requested parameter point. The
clocked structure profile still reports procedural loops as outside its
current cycle-model slice.

The receipt compares the unchanged source against Icarus Verilog 13.0 and
Xcelium 24.03-s004 for the four-state rows, checks canonical-E admission, and
kernel-checks the named clocked-profile refusal for the descending loop header.
