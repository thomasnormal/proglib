# Memory edge-order witness

This clean-room source exercises the memory-aware edge-order admission used by
the relational confluence bridge. One `always_ff` process clears every element
of an unpacked memory with a procedural `for` loop of nonblocking writes. Two
other edge processes write disjoint scalar outputs, and a continuous
assignment reads one memory element.

The generated-envelope receipt in `agree.lean` checks that the concrete
parameter `N = 4` has four processes, one driver per target, and
`seqOblIM = true`. The generic theorem keeps the evaluator frame and
declaration-identity memory receipts explicit.

`check.py` runs three post-edge rows after reset and compares them with Icarus
Verilog 13.0 and Xcelium 24.03-s004. The rows cover the reset loop and two
subsequent scalar NBA updates. The testbench is an oracle receipt only.
