# ARRAYBITSEL CHECK

This source-shaped witness targets `mem[0][...]` from two generated
continuous assignments. The second generated target has an unknown packed-bit
index, then a later source assignment drives `q` to `1'b1`. IEEE 1800-2023
§§10.3 and 11.5.1 require the unknown target to contribute no selected bit and
the later assignment to remain in the same settle pass.

Before the fix, canonical E returned `q = x` because the unknown index returned
from `settleAssignAt` without visiting the remaining process list. The fixed
arm advances to the remaining processes. E now returns `q = 1` for all four
stimulus rows, including x and z input values.

`check.py` regenerates and compares the checked-in Slang envelope, builds the
Lean receipt, and runs the same four source rows through Icarus Verilog 13.0
and Xcelium 24.03-s004 when available. Both pinned simulators return `q = 1`.

The Lean receipt also proves conservativity against the verbatim pre-change
`settleAssignAtBeforeArrayBitSel` evaluator for every process list whose targets
contain no `arrayBitSel` node.
