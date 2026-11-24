# Simultaneous NBA acceptance witness

This clean-room source is the relational-semantics acceptance test for two
independent edge processes. Starting from `a = 0` and `b = 1`, a `clk_a` edge
alone produces `(a,b) = (1,1)`, a `clk_b` edge alone produces `(0,0)`, and a
batch containing both edges produces `(1,0)` because both nonblocking RHS
values sample the pre-edge state. The serial single-edge outcomes therefore do
not cover the simultaneous batch.

The testbench forces the initial output values only for the oracle run. The
source itself has no initialization process. The fixture is evidence for the
input-batch and NBA sampling design, not an implementation of the relation.
