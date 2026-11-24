# Nested generated child-instance fixture

This is the clean-room structural multiplier used for the T4a hierarchy wall.
It has child gate instances under two nested `generate for` loops and remains
source-shaped in the envelope.  Icarus Verilog 13.0 and Xcelium 24.03-s004
agree on the four differential rows in `check.py`.

The concrete hierarchical semantics loads for `N = 2` and `N = 3`.  The
published compositional equations are indexed by `LeanModels/Sv/DesignLemmas.lean`.
The combinational hierarchy summary still refuses this design because its
flat-twin bridge only admits module-level instances; `agree.lean` keeps that
refusal as an executable receipt.  No correctness theorem is claimed for the
structural multiplier until that bridge is extended.

The fault connection `f[i*N+j]` is therefore not admitted by `sv_structure`
independently of the hierarchy wall: the current affine obligation language
does not prove a product of two symbolic variables.  This is a genuine tactic
wall, not a reason to rewrite the design or to replace the index with a
constant-width encoding.
