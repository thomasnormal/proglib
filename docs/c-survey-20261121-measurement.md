# C survey measurement, 2026-11-21

The required full replay was attempted after rebuilding `c-torture-run` from
the current tree under the lane's 24 GiB cgroup.  The rebuild completed
successfully and `coredumpctl` reported zero Lean coredumps in the preceding
two hours.

Fresh envelope regeneration could not start because this host has the pinned
Clang 21.1.8 runtime but no Clang development headers.  The approved
structured-type probe fails at its first include, `clang/AST/ASTConsumer.h`.
No current C-MATCH number is claimed from a replay with stale envelopes.

For diagnosis only, the current runner replayed all 2,214 rows against the
last approved-plugin envelope set.  It produced 3 passed, 1,066
`refused-unsupported`, 1 `refused-libc`, 6 `refused-ub`, 1 timeout, and 1,137
`not-parsed` rows.  The `not-parsed` rows are an instrument mismatch because
those envelopes predate the expression node-id fields required by the current
extractor.  This result is therefore not a survey receipt.

The last valid structured-envelope receipt remains 625 MATCH / 2,214 rows,
with 625 active matches over the 2,128-row denominator after no-entry-point
rows.  The 2026-11-20 receipt records the 701 names lost against the 1,326
receipt, including 490 structured-plugin instrument changes, 2 correct UB
refusals, and 209 rows requiring regression classification.

The next measurement requires a Clang development package or a rebuilt
`structured_type_probe.so`.  Until that is supplied, no survey delta or S1
gate result is asserted.
