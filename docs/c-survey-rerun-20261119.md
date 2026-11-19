# C survey rerun receipt

The latest complete, provenance-checked C1–C3 survey remains **1326/2214 MATCH**
(**1326/2112** on the comparable compiler-accepted basis). The accepted drop-cause
accounting has 0 unresolved regressions among the 325 formerly matching rows.

The requested rerun used the current runner under a 24 GiB cgroup. The direct
one-million-fuel run reached `memcpy-1.c` and did not complete. The bounded batch
rerun completed all 2214 manifest rows but its cached envelopes predate the
provenance field, so all parsed rows were correctly rejected as stale and it is
not a survey receipt. No changed C-MATCH is claimed from either incomplete run.

The accepted group counts remain 189 fresh-envelope recoveries, 67 floating-bit
old matches that relied on source spelling, 43 layout/aggregate rows, 6
declaration-binding rows, 19 effective-type rows, and 1 bounds row. The current
full-survey verdict buckets are 9 failed, 354 not-parsed, 1 oracle-tests-compiler,
20 refused-libc, 99 refused-ub, 396 refused-unsupported, and 9 timeout, with 102
no-entry-point rows excluded from the comparable denominator.
