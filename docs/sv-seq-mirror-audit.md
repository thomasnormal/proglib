# `seq_mirror` heartbeat audit

The sequence proof's `seq_mirror` command fit within one million heartbeats in
the sequence-tactic baseline recorded by `3aef9b430`. At the current master
tip, the same symbolic `valid_chain_profile` instantiation reaches the
one-million-heartbeat limit in `sv_seq_inst`, which is why
`valid_proof.lean` uses a two-million-heartbeat test budget. The theorem
statements and the E definitions are unchanged by that budget.

The largest relevant change in the interval is `75a9b0468`, which retained
`PLhs.arrayBitSel` and added its cases to `CoreMemExec`'s structural target
walks and the clocked-profile predicates. The valid/ready profile has no
array-bit-select target, so the added cases are shared evaluator/profile
overhead rather than a new path in this design. The later relational `Nd*`
files are not in the `seq_mirror` import closure.

This identifies the slowdown as evaluator/profile growth in the shared E
closure, with `75a9b0468` the lane-owned change most likely to contribute. A
cold, commit-by-commit attribution is not claimed here because the available
historical worktrees reuse the shared Lake artifacts. No semantic or proof
statement change is justified by this audit.
