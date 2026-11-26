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

The receipt is reproducible with `python3 check.py`. On 2026-11-25 it reports
four matching rows on Icarus Verilog 13.0 and Xcelium 24.03-s004.

## Statements over the relation

`relation.lean` states and proves, over the choice-explicit relation of
`LeanModels/Sv/Kernel/NdStep.lean`, that from every store with both clocks 0
(known) and any four-state values in `a` and `b`, the batch that raises both
clocks has the swap as its only settled outcome (`swap_only`, for every
oracle and every schedule), that such an outcome exists (`swap_exists`), and
that the executor's result on that batch is that outcome (`swap_executor`,
through `CoreMemDesign.step_sound`). The start hypothesis "both clocks known"
is part of every statement: the relation refuses x on a clock.

`step_rows.lean` holds 23 rows on the arms of the step function. Eight are
checked by the Lean kernel; fifteen are evaluated with `#guard`. No simulator
was run for either file; the simulator receipt above is the only oracle
evidence for this design.
