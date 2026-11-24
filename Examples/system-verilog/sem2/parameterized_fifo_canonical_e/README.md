# Canonical E parameterized FIFO receipt

This clean-room fixture keeps the parameterized FIFO shape with one unpacked
`storage [0:DEPTH-1]`, run-time read and write indices, continuous status
assignments, and an asynchronous-reset edge process.  `instantiateCoreMem`
accepts the source-shaped declaration as one native `MemShape` at both
`DATA_W=8, DEPTH=4` and `DATA_W=32, DEPTH=16`.  The ordinary scalar structure
route is not used for this fixture because it does not provide a sound
parameterized unpacked-memory representation.

`agree.lean` is the kernel receipt.  `check.py` compares six source rows with
Icarus Verilog 13.0 and with readiness-gated Xcelium when available.
