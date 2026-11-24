# Finite-state NBA confluence receipt

This clean-room finite-state machine has one `always_ff` state process and two
continuous-assignment output drivers. The source-shaped E proof instantiates
the guarded terminal-path confluence theorem and retains the route, queue,
coherence, and declaration-identity receipts.

`check.py` runs the Lean receipt and six rows against Icarus Verilog 13.0 and
Xcelium 24.03-s004. The row set includes startup, reset, and each state
transition. The theorem is for the admitted process-atomic NBA scheduler
class. It does not claim whole-language fine-grained confluence or implement
the pending normative relation.
